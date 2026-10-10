#!/usr/bin/env python3
"""Audit the actual Challenge import closure and exact canonical Mathlib pins.

This local source/provenance check parses headers with the installed Lean compiler.
It does not elaborate proofs, replay kernels, or reproduce Palomar's protected build.
Run after `lake update` and `lake exe cache get`. Optional --online checks use the
primary GitHub HTTPS API; they do not assert that commits have digital signatures.
"""

from __future__ import annotations

import argparse
import collections
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import urllib.request


def run(args: list[str], root: Path) -> str:
    env = dict(os.environ)
    env["LEAN_NUM_THREADS"] = "1"
    result = subprocess.run(args, cwd=root, env=env, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(f"{' '.join(args)} failed ({result.returncode}): {result.stderr.strip()}")
    return result.stdout


def repository(url: str) -> str:
    match = re.fullmatch(r"https://github\.com/([\w.-]+/[\w.-]+?)(?:\.git)?/?", url)
    if not match:
        raise RuntimeError(f"Expected credential-free canonical GitHub HTTPS URL: {url}")
    return match.group(1).lower()


def load_manifest(path: Path) -> dict[str, dict]:
    entries = json.loads(path.read_text())["packages"]
    result: dict[str, dict] = {}
    for entry in entries:
        name = entry["name"]
        if name in result or entry.get("type") != "git" or entry.get("subDir") is not None:
            raise RuntimeError(f"Duplicate/unsupported dependency in {path}: {name}")
        if not re.fullmatch(r"[0-9a-f]{40}", entry.get("rev", "")):
            raise RuntimeError(f"Dependency lacks an exact immutable revision: {name}")
        repository(entry["url"])
        result[name] = entry
    return result


def tracked_blobs(directory: Path, root: Path) -> dict[str, str]:
    output = run(["git", "-C", str(directory), "ls-tree", "-rz", "HEAD"], root)
    result = {}
    for record in output.split("\0"):
        if record:
            info, path = record.split("\t", 1)
            _mode, kind, oid = info.split()
            if kind == "blob":
                result[path] = oid
    return result


def blob_hash(path: Path) -> str:
    data = path.read_bytes()
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def within(path: Path, directory: Path) -> bool:
    return path == directory or directory in path.parents


def api(path: str, evidence: Path | None) -> dict:
    url = "https://api.github.com/repos/" + path
    request = urllib.request.Request(url, headers={
        "Accept": "application/vnd.github+json", "User-Agent": "ArbitraryRSB-local-verification"
    })
    with urllib.request.urlopen(request, timeout=60) as response:
        body = response.read()
    result = json.loads(body)
    if evidence:
        evidence.mkdir(parents=True, exist_ok=True)
        (evidence / (path.replace("/", "_") + ".json")).write_bytes(body)
    return result


def check(root: Path, online: bool, evidence: Path | None) -> dict:
    if evidence and within(evidence, root):
        raise RuntimeError("Keep raw GitHub API evidence outside the public repository")
    config = json.loads((root / "comparator.json").read_text())
    module = config["challenge_module"]
    challenge = root.joinpath(*module.split(".")).with_suffix(".lean")
    if not challenge.is_file() or challenge.is_symlink():
        raise RuntimeError("Challenge must be a regular root-package source")
    packages = load_manifest(root / "lake-manifest.json")
    mathlibs = [name for name, item in packages.items()
                if repository(item["url"]) == "leanprover-community/mathlib4"]
    if len(mathlibs) != 1:
        raise RuntimeError("Expected exactly one canonical Mathlib dependency")
    mathlib_name = mathlibs[0]
    mathlib = packages[mathlib_name]
    package_dirs = {name: (root / ".lake" / "packages" / name).resolve() for name in packages}
    canonical = load_manifest(package_dirs[mathlib_name] / "lake-manifest.json")
    if set(packages) != set(canonical) | {mathlib_name}:
        raise RuntimeError("Root manifest is not exactly Mathlib's pinned manifest closure")
    for name, expected in canonical.items():
        actual = packages[name]
        if (repository(actual["url"]), actual["rev"]) != (
                repository(expected["url"]), expected["rev"]):
            raise RuntimeError(f"Root manifest substitutes canonical dependency {name}")
    toolchain = (root / "lean-toolchain").read_text().strip()
    if (package_dirs[mathlib_name] / "lean-toolchain").read_text().strip() != toolchain:
        raise RuntimeError("Project and pinned Mathlib select different Lean toolchains")
    lean = run(["lake", "env", "which", "lean"], root).strip()
    prefix = Path(run([lean, "--print-prefix"], root).strip()).resolve()
    lean_version = run([lean, "--version"], root).strip()
    expected_version = toolchain.removeprefix("leanprover/lean4:v")
    if f"version {expected_version}," not in lean_version:
        raise RuntimeError("Installed Lean does not match lean-toolchain")
    src_path = run(["lake", "env", "printenv", "LEAN_SRC_PATH"], root).strip()
    roots = list(dict.fromkeys(Path(item).resolve() for item in src_path.split(os.pathsep) if item))
    roots += [prefix / "src" / "lean" / "lake", prefix / "src" / "lean"]
    project_roots = [path for path in roots
                     if within(path, root) and not within(path, root / ".lake")]
    git_blobs = {}
    pin_reports = {}
    for name, item in packages.items():
        directory = package_dirs[name]
        head = run(["git", "-C", str(directory), "rev-parse", "HEAD"], root).strip()
        if head != item["rev"]:
            raise RuntimeError(f"Dependency HEAD differs from manifest: {name}")
        if run(["git", "-C", str(directory), "status", "--porcelain", "--untracked-files=no"], root):
            raise RuntimeError(f"Tracked dependency files are modified: {name}")
        git_blobs[name] = tracked_blobs(directory, root)
        manifest_path = directory / "lake-manifest.json"
        if manifest_path.exists() and git_blobs[name].get("lake-manifest.json") != blob_hash(manifest_path):
            raise RuntimeError(f"Dependency manifest differs from its exact Git blob: {name}")
        pin_reports[name] = {"repository": repository(item["url"]), "revision": head,
                            "tree": run(["git", "-C", str(directory), "rev-parse", "HEAD^{tree}"], root).strip()}

    def resolve(name: str) -> Path:
        components = name.split(".")
        for source_root in roots:
            if (source_root / components[0]).is_dir() or (source_root / f"{components[0]}.lean").exists():
                source = source_root.joinpath(*components).with_suffix(".lean")
                if not source.is_file() or source.is_symlink():
                    raise RuntimeError(f"Missing/symlink source for {name}: {source}")
                return source.resolve()
        raise RuntimeError(f"Cannot resolve imported module {name}")

    # Lean.findLean chooses the first root containing the module's top-level
    # directory/file. Parse each reached source header with Lean's own parser.
    pending = {module: challenge}
    seen: dict[str, dict] = {}
    while pending:
        batch = list(pending.items())[:64]
        for name, _path in batch:
            del pending[name]
        payload = json.loads(run([lean, "--deps-json", *(str(path) for _, path in batch)], root))
        entries = payload["imports"]
        if len(entries) != len(batch):
            raise RuntimeError("Lean returned the wrong number of parsed headers")
        for (name, path), entry in zip(batch, entries, strict=True):
            if entry.get("errors"):
                raise RuntimeError(f"Lean rejected {path}'s import header: {entry['errors']}")
            imports = sorted({item["module"] for item in entry["result"]["imports"]})
            if name == module:
                if not entry["result"]["isModule"]:
                    raise RuntimeError("Challenge does not use the required module system")
                owner = "project"
                relative = str(path.relative_to(root))
            elif within(path, prefix):
                owner = "core"
                relative = str(path.relative_to(prefix))
            else:
                owners = [owner for owner, directory in package_dirs.items() if within(path, directory)]
                if len(owners) != 1:
                    raise RuntimeError(f"Challenge imports an untrusted project/outside source: {path}")
                owner = owners[0]
                relative = path.relative_to(package_dirs[owner]).as_posix()
                if git_blobs[owner].get(relative) != blob_hash(path):
                    raise RuntimeError(f"Imported source differs from its exact Git blob: {path}")
            seen[name] = {"owner": owner, "path": relative, "imports": imports,
                          "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
            for imported in imports:
                imported_path = resolve(imported)
                if imported != module:
                    components = imported.split(".")
                    for source_root in project_roots:
                        candidate = source_root.joinpath(*components).with_suffix(".lean")
                        if candidate.exists():
                            raise RuntimeError(f"Project source shadows a Challenge dependency: {candidate}")
                if imported not in seen:
                    pending[imported] = imported_path

    canonical_evidence = {"checked_online": online}
    if online:
        for name, item in pin_reports.items():
            remote = api(f"{item['repository']}/commits/{item['revision']}", evidence)
            if remote["sha"] != item["revision"] or remote["commit"]["tree"]["sha"] != item["tree"]:
                raise RuntimeError(f"Canonical GitHub commit/tree differs for {name}")
        repo = "leanprover-community/mathlib4"
        tag = "v" + expected_version
        tag_response = api(f"{repo}/git/ref/tags/{tag}", evidence)
        obj = tag_response["object"]
        while obj["type"] == "tag":
            obj = api(f"{repo}/git/tags/{obj['sha']}", evidence)["object"]
        if obj["type"] != "commit" or obj["sha"] != mathlib["rev"]:
            raise RuntimeError("Canonical Mathlib release tag differs from the pinned commit")
        master = api(f"{repo}/git/ref/heads/master", evidence)["object"]["sha"]
        ancestry = api(f"{repo}/compare/{mathlib['rev']}...{master}", evidence)
        canonical_evidence.update({"release_tag": tag, "release_tag_commit": obj["sha"],
                                  "master_commit": master,
                                  "master_contains_pin": ancestry["behind_by"] == 0,
                                  "merge_base": ancestry["merge_base_commit"]["sha"],
                                  "transport": "primary GitHub HTTPS API; no signed-commit assertion"})
    counts = dict(sorted(collections.Counter(item["owner"] for item in seen.values()).items()))
    return {"status": "passed", "scope": "local source/dependency audit; not Palomar protected verification",
            "toolchain": toolchain, "installed_lean": lean_version, "challenge_module": module,
            "challenge_sha256": seen[module]["sha256"], "module_count_including_challenge": len(seen),
            "module_counts_by_owner": counts, "pins": pin_reports,
            "canonical_evidence": canonical_evidence, "modules": dict(sorted(seen.items()))}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--online", action="store_true", help="Confirm canonical GitHub commits, tag, and ancestry")
    parser.add_argument("--evidence-dir", type=Path, help="Save raw API responses outside the public repository")
    parser.add_argument("--json", type=Path, help="Write the complete dependency audit to this path")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    try:
        report = check(root, args.online, args.evidence_dir.resolve() if args.evidence_dir else None)
        if args.json:
            args.json.write_text(json.dumps(report, indent=2) + "\n")
        summary = {key: value for key, value in report.items() if key != "modules"}
        print(json.dumps(summary, indent=2))
        return 0
    except (RuntimeError, OSError, KeyError, ValueError, subprocess.SubprocessError) as error:
        print(f"Dependency audit failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
