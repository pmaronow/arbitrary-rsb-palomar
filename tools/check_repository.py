#!/usr/bin/env python3
"""Check this ordinary repository against the recorded Palomar source contract.

This implements local source/layout/metadata/pin checks, not Palomar intake,
protected statement compilation, proof checking, licensee detection or review.
It downloads only immutable public policy/schema data, unless --policy-root
supplies the corresponding local snapshot tree. Any incomplete check fails.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tomllib
import urllib.request

sys.dont_write_bytecode = True

import jsonschema
import yaml
from lean_source import imports, mask, proof_snapshot, snapshot_digest, source_roots, sources, submitted_files

SUBMISSION_REV = 'd4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44'
SCHEMA_REV = '99c678e569c7c4c0772db297c5ddd5e4c9b6322e'
STANDARD = {'propext', 'Quot.sound', 'Classical.choice'}
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
SHA = re.compile(r'[0-9a-f]{40}')
GITHUB = re.compile(r'https://github\.com/([A-Za-z0-9_.-]+)/([A-Za-z0-9_.-]+?)(?:\.git)?/?')
ARTIFACTS = {'.a', '.bc', '.dll', '.dylib', '.ilean', '.ir', '.o', '.obj', '.olean', '.so', '.trace'}
LICENSE_NAME = re.compile(r'(?:LICENSE|LICENCE|COPYING|UNLICENSE|OFL)(?:\.(?:md|markdown|txt))?', re.I)


def need(condition, message):
    if not condition: raise ValueError(message)


def unique(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, f'duplicate JSON key: {key}')
        result[key] = value
    return result


class UniqueLoader(yaml.SafeLoader):
    pass


def mapping(loader, node, deep=False):
    result = {}
    for key_node, value_node in node.value:
        need(key_node.tag != 'tag:yaml.org,2002:merge', 'YAML merge keys are forbidden')
        key = loader.construct_object(key_node, deep=deep)
        need(key not in result, f'duplicate YAML key: {key}')
        result[key] = loader.construct_object(value_node, deep=deep)
    return result


UniqueLoader.add_constructor(yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, mapping)


def regular(path, maximum):
    need(not path.is_symlink() and path.is_file(), f'not a regular file: {path}')
    need(path.stat().st_size <= maximum, f'file exceeds {maximum} bytes: {path}')
    return path.read_text(encoding='utf-8')


def module_header(text):
    """Header recognition preserves the distinction between docs and comments."""
    rest = text
    while True:
        rest = rest.lstrip(' \r\n')
        if rest.startswith('--'):
            split = rest.find('\n')
            if split < 0: return False
            rest = rest[split + 1:]
        elif rest.startswith('/-') and not rest.startswith(('/--', '/-!')):
            i, depth = 3, 1
            while depth:
                token = re.search(r'/-|-/', rest[i:])
                if token is None: return False
                depth += 1 if token[0] == '/-' else -1
                i += token.end()
            rest = rest[i:]
        else:
            return bool(re.match(r'module(?:\s|$)', rest))


def json_data(path):
    return json.loads(regular(path, 1024 * 1024), object_pairs_hook=unique)


def tree_snapshot(root):
    return {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in submitted_files(root)}


def policy_json(repository, revision, path, policy_root):
    if policy_root:
        return json.loads((policy_root / repository.split('/')[1] / path).read_text())
    url = f'https://raw.githubusercontent.com/{repository}/{revision}/{path}'
    with urllib.request.urlopen(url, timeout=60) as response:
        return json.loads(response.read().decode('utf-8'))


def version(text):
    match = re.fullmatch(r'leanprover/lean4:v(\d+)\.(\d+)\.(\d+)(?:-rc(\d+))?', text.strip())
    need(match is not None, f'unsupported toolchain: {text.strip()}')
    major, minor, patch = map(int, match.groups()[:3])
    rc = match[4]
    return (major, minor, patch, 1 if rc is None else 0, int(rc or 0))


def safe_relative(root, value):
    need(isinstance(value, str) and value and not value.startswith('/'), 'path must be relative')
    need(not any(c in value for c in '\\?#\x00\n\r'), f'unsafe path: {value}')
    need(all(x not in {'', '.', '..'} for x in value.split('/')), f'unsafe path: {value}')
    path = root.joinpath(*value.split('/'))
    for part in [path, *path.parents]:
        if part == root.parent: break
        need(not part.is_symlink(), f'path contains symlink: {value}')
    need(path.resolve().is_relative_to(root.resolve()), f'path leaves repository: {value}')
    return path


def manifest(root, project, seen):
    need(project not in seen, f'path-dependency cycle: {project}')
    seen.add(project)
    lakefiles = [p for p in (project / 'lakefile.toml', project / 'lakefile.lean') if p.exists()]
    need(len(lakefiles) == 1, f'exactly one Lakefile required: {project}')
    content = regular(lakefiles[0], 1024 * 1024)
    if lakefiles[0].suffix == '.toml': tomllib.loads(content)
    data = json_data(project / 'lake-manifest.json')
    packages = data.get('packages')
    need(isinstance(packages, list), f'manifest packages missing: {project}')
    names = [p.get('name') for p in packages]
    need(all(isinstance(n, str) and n for n in names) and len(set(names)) == len(names),
         f'manifest package names invalid: {project}')
    for package in packages:
        if package.get('type') == 'git':
            need(bool(GITHUB.fullmatch(package.get('url', ''))), 'dependency must use public HTTPS GitHub URL')
            need(bool(SHA.fullmatch(package.get('rev', ''))), f'unpinned dependency: {package.get("name")}')
        elif package.get('type') == 'path':
            raw = package.get('dir')
            need(isinstance(raw, str) and raw, 'path dependency has no directory')
            path = (project / raw).resolve()
            need(path.is_relative_to(root.resolve()), f'path dependency leaves repository: {raw}')
            need(not (project / raw).is_symlink() and path.is_dir(), f'invalid path dependency: {raw}')
            if path not in seen: manifest(root, path, seen)
        else:
            raise ValueError(f'unknown package type: {package.get("type")}')
    return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--config', default='comparator.json')
    parser.add_argument('--policy-root', type=Path)
    parser.add_argument('--report', type=Path, help='external JSON output including per-source hashes')
    args = parser.parse_args()
    root = args.root.resolve()
    result = {'local_repository_checks_passed': False,
              'palomar_verification_complete': False,
              'scope': 'local source, ordinary layout, schema, metadata, and resolved pin checks',
              'policy_revision': SUBMISSION_REV, 'schema_revision': SCHEMA_REV}
    try:
        initial_snapshot = tree_snapshot(root)
        text = regular(root / 'lean-toolchain', 1024 * 1024).strip()
        need(version(text) >= version('leanprover/lean4:v4.35.0-rc2'), 'toolchain below current Palomar minimum')
        config = json_data(safe_relative(root, args.config))
        required = {'challenge_module', 'solution_module', 'theorem_names', 'permitted_axioms'}
        need(isinstance(config, dict) and required <= config.keys(), 'Comparator required fields missing')
        need(config.keys() <= required | {'definition_names', 'enable_nanoda'}, 'Comparator has forbidden fields')
        for key in ('challenge_module', 'solution_module'):
            need(isinstance(config[key], str) and bool(MODULE.fullmatch(config[key])), f'invalid {key}')
        need(config['challenge_module'] != config['solution_module'], 'Challenge and Solution must be distinct')
        need(isinstance(config['theorem_names'], list) and config['theorem_names'], 'empty theorem selection')
        definition_names = config.get('definition_names', [])
        need(isinstance(definition_names, list), 'definition_names must be an array')
        for name in config['theorem_names'] + definition_names:
            need(isinstance(name, str) and bool(MODULE.fullmatch(name)), f'invalid export target: {name}')
        need(isinstance(config['permitted_axioms'], list)
             and all(isinstance(x, str) for x in config['permitted_axioms'])
             and set(config['permitted_axioms']) <= STANDARD, 'forbidden permitted axiom')
        challenge = root.joinpath(*config['challenge_module'].split('.')).with_suffix('.lean')
        solution = root.joinpath(*config['solution_module'].split('.')).with_suffix('.lean')
        challenge_text = regular(challenge, 100 * 1024)
        regular(solution, 500 * 1024 * 1024)
        physical = lambda s: s.count('\n') + int(bool(s) and not s.endswith('\n'))
        need(physical(challenge_text) <= 1000, 'Challenge exceeds 1000 lines')
        warnings = []
        if physical(challenge_text) > 300 or challenge.stat().st_size > 32 * 1024:
            warnings.append('Challenge exceeds preferred 300 lines or 32 KiB')
        checked = sources(root)
        for path in checked:
            source = regular(path, 500 * 1024 * 1024)
            need(physical(source) <= 10000, f'source exceeds 10000 physical lines: {path.relative_to(root)}')
            need(path.name == 'lakefile.lean' or module_header(source),
                 f'module header required: {path.relative_to(root)}')
            if path != challenge:
                need(not re.search(r'\b(?:sorry|admit|sorryAx|native_decide|Lean\.ofReduceBool)\b', mask(source)),
                     f'proof hole/forbidden proof primitive: {path.relative_to(root)}')
                need(not re.search(r'^\s*(?:public\s+)?(?:axiom|constant)\s', mask(source), re.M),
                     f'custom axiom/constant: {path.relative_to(root)}')
        root_manifest = manifest(root, root, set())
        # This check is strict about project-specific imports. Closure against
        # downloaded authenticated dependency sources is still checked by Palomar.
        local_roots = source_roots(root)
        for imported in imports(challenge_text):
            rel = Path(*imported.split('.')).with_suffix('.lean')
            need(not any((base / rel).is_file() for base in local_roots),
                 f'Challenge imports project-specific source: {imported}')
        size = 0
        for directory, dirs, files in os.walk(root, followlinks=False):
            dirs[:] = [d for d in dirs if d not in {'.git', '.lake'} and not (Path(directory) / d).is_symlink()]
            for filename in files:
                path = Path(directory) / filename
                if path.is_symlink(): continue
                size += path.stat().st_size
                need(path.suffix not in ARTIFACTS and not filename.endswith(('.olean.private', '.olean.server')),
                     f'compiled artifact in source: {path.relative_to(root)}')
                if path.stat().st_size <= 1024:
                    need(not path.read_bytes().startswith(b'version https://git-lfs.github.com/spec/v1'),
                         f'Git LFS source pointer: {path.relative_to(root)}')
        need(size <= 500 * 1024 * 1024, 'source checkout exceeds 500 MiB')
        need(not (root / '.gitmodules').exists(), 'submitted Git submodules are unsupported')
        licenses = [p for p in root.iterdir() if LICENSE_NAME.fullmatch(p.name)]
        need(len(licenses) == 1, 'exactly one conventional root license is required')
        license_text = regular(licenses[0], 1024 * 1024)
        # MIT project contract. This is not a substitute for Palomar's licensee.
        normalized = ' '.join(license_text.split())
        for phrase in ('Permission is hereby granted, free of charge',
                       'The above copyright notice and this permission notice',
                       'THE SOFTWARE IS PROVIDED "AS IS"', 'AUTHORS OR COPYRIGHT HOLDERS'):
            need(phrase in normalized, 'root license does not contain the standard MIT terms')
        metadata = yaml.load(regular(root / 'formalization.yaml', 256 * 1024), Loader=UniqueLoader)
        need(isinstance(metadata, dict), 'metadata must be one YAML mapping')
        schema = policy_json('mathlib-initiative/formalization.yaml', SCHEMA_REV,
                             'schema/v0.4.schema.json', args.policy_root)
        try:
            jsonschema.Draft202012Validator(schema).validate(metadata)
        except jsonschema.ValidationError as error:
            location = '.'.join(map(str, error.absolute_path)) or '<root>'
            raise ValueError(f'metadata {location}: {error.message}') from error
        need(metadata.get('version') == 'v0.4', 'declare metadata version v0.4')
        project = metadata['project']
        need(0 < len(project['name'].strip()) <= 300, 'invalid project name')
        need(isinstance(project.get('description'), str) and 0 < len(project['description'].strip()) <= 10000,
             'invalid public abstract')
        need(project['license'] == 'MIT', 'project.license must match MIT root license')
        maintainers = project.get('responsible_maintainers')
        need(isinstance(maintainers, list) and maintainers and all(isinstance(n, str) and n.strip() for n in maintainers),
             'responsible maintainers must be nonempty human names')
        need('repository' not in metadata, 'this package contains the substantive development, so omit repository')
        classes = metadata.get('classification', {})
        for key, lower in [('arxiv', 1), ('msc2020', 0)]:
            codes = classes.get(key, [])
            taxonomy = policy_json('PalomarRegistry/PalomarSubmission', SUBMISSION_REV,
                                   f'taxonomies/{"arxiv-categories" if key == "arxiv" else "msc2020-codes"}.json', args.policy_root)
            need(isinstance(codes, list) and lower <= len(codes) <= 8
                 and all(isinstance(x, str) and x in taxonomy for x in codes)
                 and len(set(codes)) == len(codes), f'invalid {key} classifications')
        relations = {'formalizes', 'adapts', 'independently-proves', 'background', 'other'}
        need(all(s.get('relationship') in relations for s in metadata['sources']), 'invalid source relationship')
        need(not any(s.get('type') == 'original-proof' for s in metadata['sources']), 'paper-based project cannot claim original-proof origin')
        need(any(s.get('relationship') in {'formalizes', 'adapts', 'independently-proves'} for s in metadata['sources']),
             'paper-based result needs a substantive source relationship')
        need(metadata['review']['status'].strip(), 'review status must be nonempty')
        # Compatibility is checked from the actual pinned checkout, not inputRev.
        mathlib = next((p for p in root_manifest['packages'] if p.get('name') == 'mathlib'), None)
        if mathlib:
            checkout = root / root_manifest.get('packagesDir', '.lake/packages') / 'mathlib'
            need(checkout.is_dir(), 'Mathlib checkout absent; run lake update/cache retrieval first')
            revision = subprocess.run(['git', '-C', str(checkout), 'rev-parse', 'HEAD'],
                                      text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            need(revision.returncode == 0 and revision.stdout.strip() == mathlib['rev'],
                 'Mathlib checkout is not the resolved manifest revision')
            need(regular(checkout / 'lean-toolchain', 1024 * 1024).strip() == text, 'Mathlib/project toolchain mismatch')
            expected = json_data(checkout / 'lake-manifest.json')['packages']
            packages = {p['name']: p for p in root_manifest['packages']}
            for dep in expected:
                actual = packages.get(dep['name'])
                need(actual is not None and actual.get('rev') == dep.get('rev')
                     and actual.get('url', '').removesuffix('.git').rstrip('/') == dep.get('url', '').removesuffix('.git').rstrip('/'),
                     f'Mathlib pinned closure substituted or omitted: {dep["name"]}')
        result['source_sha256'] = {
            str(path.relative_to(root)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in checked + [root / 'lean-toolchain', root / 'lakefile.toml',
                                   root / 'lake-manifest.json', root / 'formalization.yaml',
                                   safe_relative(root, args.config), licenses[0]] if path.is_file()
        }
        result['source_tree_sha256'] = hashlib.sha256(
            json.dumps(result['source_sha256'], sort_keys=True, separators=(',', ':')).encode()
        ).hexdigest()
        result['proof_source_sha256'] = snapshot_digest(proof_snapshot(root, args.config))
        result.update(local_repository_checks_passed=True, submitted_lean_files=len(checked),
                      source_bytes=size, compared_declarations=config['theorem_names'], warnings=warnings,
                      checks_outside_this_tool=['canonical dependency authentication and transitive Challenge closure',
                                                 'Palomar protected statement compilation and licensee detection',
                                                 'Comparator, independent kernel checks, and editorial review'])
        need(initial_snapshot == tree_snapshot(root), 'submitted files changed during repository validation')
    except Exception as error:
        result['local_repository_checks_passed'] = False
        result['failure'] = str(error)
    if args.report:
        need(not args.report.resolve().is_relative_to(root), '--report must be outside the submitted repository')
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'source_sha256'}, indent=2))
    return 0 if result['local_repository_checks_passed'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
