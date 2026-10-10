#!/usr/bin/env bash
set -euo pipefail

# Replay the selected proofs with the current toolchain's Comparator and its
# bundled Lean, NanoDa and con-ron kernels. This is a local check; Palomar's
# intake, protected statement build and editorial review are additional checks.
repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"
config_path=${1:-comparator.json}
for command_name in bwrap lake lean python3; do
  command -v "$command_name" >/dev/null || {
    echo "error: $command_name is required" >&2; exit 1;
  }
done
python3 tools/check_repository.py --config "$config_path"
prefix=$(lean --print-prefix)
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
  test -x "$prefix/bin/$tool" || {
    echo "error: selected toolchain does not bundle $tool" >&2; exit 1;
  }
done
python3 - "$prefix" <<'PY'
import pathlib, re, subprocess, sys
prefix = pathlib.Path(sys.argv[1])
expected = pathlib.Path('lean-toolchain').read_text().strip().removeprefix('leanprover/lean4:v')
observed = subprocess.check_output([str(prefix / 'bin/lean'), '--version'], text=True)
match = re.search(r'Lean \(version ([^,]+),', observed)
if match is None or match[1] != expected:
    raise SystemExit(f'error: selected executable {observed.strip()} does not match lean-toolchain')
print(observed.strip())
PY
temporary_dir=$(mktemp -d "${TMPDIR:-/tmp}/arbitrary-rsb-comparator.XXXXXX")
trap 'rm -rf "$temporary_dir"' EXIT
python3 - "$config_path" "$temporary_dir/comparator.json" "$prefix" <<'PY'
import json, pathlib, sys
source, destination, prefix = sys.argv[1:]
config = json.loads(pathlib.Path(source).read_text(encoding='utf-8'))
config.pop('enable_nanoda', None)
config['external_kernels'] = {
    'nanoda': [f'{prefix}/bin/nanoda_bin'],
    'con-ron': [f'{prefix}/bin/con-ron', '--jobs=2'],
}
pathlib.Path(destination).write_text(json.dumps(config, indent=2) + '\n')
import hashlib, os
root = pathlib.Path.cwd()
files = {}
for directory, dirs, names in os.walk(root, followlinks=False):
    dirs[:] = [d for d in dirs if d not in {'.git', '.lake', '__pycache__'}
               and not (pathlib.Path(directory) / d).is_symlink()]
    for name in names:
        p = pathlib.Path(directory) / name
        if p.is_file() and not p.is_symlink():
            files[str(p.relative_to(root))] = hashlib.sha256(p.read_bytes()).hexdigest()
pathlib.Path(destination).with_name('source-snapshot.json').write_text(json.dumps(files, sort_keys=True))
PY
"$prefix/bin/lake" comparator --config "$temporary_dir/comparator.json"
python3 - "$temporary_dir/source-snapshot.json" <<'PY'
import hashlib, json, os, pathlib, sys
sys.dont_write_bytecode = True
root = pathlib.Path.cwd()
files = {}
for directory, dirs, names in os.walk(root, followlinks=False):
    dirs[:] = [d for d in dirs if d not in {'.git', '.lake', '__pycache__'}
               and not (pathlib.Path(directory) / d).is_symlink()]
    for name in names:
        p = pathlib.Path(directory) / name
        if p.is_file() and not p.is_symlink():
            files[str(p.relative_to(root))] = hashlib.sha256(p.read_bytes()).hexdigest()
if files != json.loads(pathlib.Path(sys.argv[1]).read_text()):
    raise SystemExit('error: submitted files changed during Comparator verification')
digest = hashlib.sha256(json.dumps(files, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
print(f'Verified immutable local source snapshot SHA-256: {digest}')
sys.path.insert(0, 'tools')
from lean_source import proof_snapshot, snapshot_digest
print(f'Verified proof source SHA-256: {snapshot_digest(proof_snapshot(root))}')
PY
