#!/usr/bin/env python3
"""Replay the explicit paper targets with three bundled kernels.

This supplements the Challenge/Solution Comparator check. It verifies the
exported revised proof closures, without claiming independent Challenge
statement comparison for these additional declarations. All generated files
and raw logs are written outside the submitted source tree.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
from lean_source import proof_snapshot, scan, snapshot_digest, submitted_files

AXIOMS = ['propext', 'Classical.choice', 'Quot.sound']
# The same primitive declarations exported by the pinned Comparator. con-ron
# checks its embedded primitive pins; no alternative pin list is supplied.
PRIMITIVES = ['Quot', 'Quot.mk', 'Quot.lift', 'Quot.ind', *AXIOMS,
              'Nat.add', 'Nat.sub', 'Nat.mul', 'Nat.pow', 'Nat.gcd',
              'Nat.div', 'Nat.mod', 'Nat.beq', 'Nat.ble', 'Nat.land',
              'Nat.lor', 'Nat.xor', 'Nat.shiftLeft', 'Nat.shiftRight',
              'String.ofList', 'Char.ofNat', 'List', 'eagerReduce',
              'Nat', 'String', 'String.mk', 'Char', 'optParam',
              'autoParam', 'semiOutParam', 'outParam']


def snapshot(root):
    return {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in submitted_files(root)}


def run(command, root, destination):
    with destination.open('w') as output:
        result = subprocess.run(command, cwd=root, stdout=output,
                                stderr=subprocess.STDOUT)
    if result.returncode:
        raise ValueError(f'{command[:3]} failed with exit {result.returncode}; see {destination}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--output', type=Path)
    parser.add_argument('--target-module', action='append', dest='target_modules',
                        help='explicit target module; repeat to export several modules')
    args = parser.parse_args()
    root = args.root.resolve()
    modules = list(dict.fromkeys(args.target_modules or [
        '.'.join(path.relative_to(root).with_suffix('').parts)
        for path in sorted((root / 'Verification').rglob('*.lean'))]))
    output = args.output.resolve() if args.output else Path(
        tempfile.mkdtemp(prefix='arbitrary-rsb-revised-kernels-'))
    external = not output.is_relative_to(root)
    report = {'revised_kernel_checks_passed': False,
              'independent_challenge_comparison': False,
              'scope': 'explicit target declarations and their exported dependencies',
              'target_modules': modules,
              'output_directory': str(output)}
    try:
        if not external:
            raise ValueError('--output must be outside the submitted source tree')
        output.mkdir(parents=True, exist_ok=True)
        frozen = snapshot(root)
        identity = proof_snapshot(root)
        version = subprocess.check_output(['lean', '--version'], cwd=root, text=True).strip()
        match = re.search(r'Lean \(version ([^,]+),', version)
        if match is None or 'leanprover/lean4:v' + match[1] != (root / 'lean-toolchain').read_text().strip():
            raise ValueError('actual Lean executable does not match pinned lean-toolchain')
        prefix = Path(subprocess.check_output(['lean', '--print-prefix'], cwd=root, text=True).strip())
        for name in ['leanexport', 'leanchecker', 'nanoda_bin', 'con-ron']:
            if not (prefix / 'bin' / name).is_file():
                raise ValueError(f'the selected toolchain does not bundle {name}')
        target_paths = []
        for module in modules:
            if re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*', module) is None:
                raise ValueError(f'invalid target module name: {module}')
            path = root.joinpath(*module.split('.')).with_suffix('.lean')
            if path.is_symlink() or not path.resolve().is_relative_to(root) or not path.is_file():
                raise ValueError(f'target module is not an ordinary submitted source: {module}')
            target_paths.append(path)
        targets, violations = scan(target_paths, root)
        if violations:
            raise ValueError(f'forbidden source in revised targets: {violations}')
        names = sorted({d['name'] for d in targets})
        if not names:
            raise ValueError('no revised targets selected')
        run(['lake', 'build', *modules], root, output / 'build.log')
        export = output / 'revised-targets.ndjson'
        with export.open('w') as destination, (output / 'export.log').open('w') as errors:
            command = ['lake', 'env', str(prefix / 'bin/leanexport'),
                       *modules, '--', *names, *PRIMITIVES]
            result = subprocess.run(command, cwd=root, stdout=destination, stderr=errors)
        if result.returncode:
            raise ValueError(f'export failed with exit {result.returncode}; see {output / "export.log"}')
        nano_config = output / 'nanoda.json'
        nano_config.write_text(json.dumps({
            'export_file_path': str(export), 'use_stdin': False,
            'permitted_axioms': AXIOMS, 'unpermitted_axiom_hard_error': True,
            'unsafe_permit_all_axioms': False, 'nat_extension': True,
            'string_extension': True, 'print_success_message': True,
            'print_axioms': False}, indent=2) + '\n')
        checks = [
            ('Lean', [str(prefix / 'bin/leanchecker'), '--from-export', str(export)], 'lean-kernel.log'),
            ('NanoDa', [str(prefix / 'bin/nanoda_bin'), str(nano_config)], 'nanoda.log'),
            ('con-ron', [str(prefix / 'bin/con-ron'), '--verified', '--jobs=2', str(export)], 'con-ron.log')]
        report['kernels'] = {}
        for name, command, log in checks:
            run(command, root, output / log)
            report['kernels'][name] = {'passed': True, 'command': command, 'log': str(output / log)}
        if frozen != snapshot(root):
            raise ValueError('submitted files changed during kernel verification')
        report.update(revised_kernel_checks_passed=True,
                      lean_version=version, selected_declarations=names,
                      permitted_axioms=AXIOMS,
                      proof_source_sha256=snapshot_digest(identity),
                      export_sha256=hashlib.sha256(export.read_bytes()).hexdigest())
    except Exception as error:
        report['failure'] = str(error)
    if output.exists() and external:
        (output / 'revised-kernel-verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))
    return 0 if report['revised_kernel_checks_passed'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
