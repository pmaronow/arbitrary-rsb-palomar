#!/usr/bin/env python3
"""Build submitted sources and audit exact depth targets and transitive axioms.

The seven original exact target checks are retained. This checker makes no
claim that the older 27-claim ledger covers every numbered result in the revised
paper. Mathematical fidelity and current-paper coverage are separate reviews.
The revised general-covariance development and its explicit numbered targets
are audited separately from the preserved legacy development.
Reports/logs/generated Lean are written outside the submitted source tree.
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

from lean_source import module_for_source, proof_snapshot, scan, snapshot_digest, source_roots, sources, submitted_files

STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}

EXACT_TARGETS = [
    ('lower recursion', 'example : DepthPaper.LowerRecursionTarget := DepthPaper.lower_recursion'),
    ('endpoint deficit', 'example : DepthPaper.EndpointDeficitTarget := DepthPaper.endpoint_deficit'),
    ('endpoint root', 'example : DepthPaper.EndpointRootTarget := DepthPaper.endpoint_root'),
    ('cutoff splitting',
     'example : ∀ Ξ : DepthPaper.AdmissibleCovariance, ∀ ε lo hi qc cQ CQ : ℝ, 0 < ε → 0 < lo → lo ≤ hi → qc ∈ Set.Ioo (0 : ℝ) 1 → 0 < cQ → DepthPaper.CutoffSplittingTarget Ξ ε lo hi qc cQ CQ := by intro Ξ ε lo hi qc cQ CQ hε hlo hLH hc hcQ; exact DepthPaper.cutoff_splitting Ξ hε hlo hLH hc hcQ'),
    ('original open-set target',
     'example : (∀ k : ℕ, DepthPaper.ArbitraryDepthOpenTarget k) := DepthPaper.arbitrary_finite_depth_open_set'),
    ('restricted transition target',
     'example : (∀ r : ℕ, DepthPaper.ArbitraryDepthTransitionTarget r) := DepthPaper.arbitrary_depth_gardner_transition'),
    ('uniform sharp gradient inequality',
     'example : ∀ (Ξ : DepthPaper.AdmissibleCovariance) (μ ν : DepthPaper.ParisiMeasure), ‖DepthPaper.gradientDifferenceBCF Ξ μ ν‖ ≤ Real.exp (Ξ.first 1) * Ξ.second 1 * DepthPaper.parisiMeasureD1 μ ν := DepthPaper.norm_gradientDifferenceBCF_le'),
]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def snapshot(root):
    selected = submitted_files(root)
    return {str(p.relative_to(root)): digest(p) for p in sorted(set(selected))}


def run(command, root, log):
    with log.open('w') as output:
        result = subprocess.run(command, cwd=root, stdout=output, stderr=subprocess.STDOUT)
    if result.returncode:
        raise ValueError(f'{command[0:3]} failed with exit {result.returncode}; see {log}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--output', type=Path, help='external directory for raw audit outputs')
    parser.add_argument('--extra-module', action='append', default=[],
                        help='additional committed exact numbered-target audit module')
    args = parser.parse_args()
    root = args.root.resolve()
    output = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix='arbitrary-rsb-audit-'))
    need_external = not output.is_relative_to(root)
    report = {'exact_target_and_axiom_checks_passed': False,
              'current_paper_coverage_complete': False,
              'scope': 'all submitted sources build; public DepthPaper, GeneralDepthPaper, Solution and Verification declaration axioms; legacy and revised exact targets',
              'output_directory': str(output),
              'mathematical_qualification': 'Legacy transition targets retain their narrower hypotheses. Revised targets permit quadratic terms, state subcriticality explicitly, and derive the atomic Hessian from paper nondegeneracy. These checks do not establish every numbered paper claim.'}
    try:
        if not need_external:
            raise ValueError('--output must be outside the submitted repository')
        output.mkdir(parents=True, exist_ok=True)
        frozen = snapshot(root)
        proof_identity = proof_snapshot(root)
        toolchain = (root / 'lean-toolchain').read_text().strip()
        observed = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=root, text=True)
        match = re.search(r'Lean \(version ([^,]+),', observed)
        if match is None or 'leanprover/lean4:v' + match[1] != toolchain:
            raise ValueError('actual Lean executable does not match pinned lean-toolchain')
        report['lean_version'] = observed.strip()
        revision = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=root,
                                  text=True, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
        report['git_revision'] = revision.stdout.strip() if revision.returncode == 0 else None
        depth_sources = sorted((root / 'DepthPaper').rglob('*.lean'))
        declarations, violations = scan(depth_sources, root)
        if violations: raise ValueError(f'forbidden source in DepthPaper: {violations}')
        general_sources = sorted((root / 'GeneralDepthPaper').rglob('*.lean'))
        general_declarations, general_violations = scan(general_sources, root)
        if general_violations:
            raise ValueError(f'forbidden source in GeneralDepthPaper: {general_violations}')
        numbered_declarations, numbered_violations = scan(
            sorted((root / 'Verification').rglob('*.lean')), root)
        if numbered_violations:
            raise ValueError(f'forbidden source in exact target audit: {numbered_violations}')
        names = {d['name'] for d in declarations}
        names.update(d['name'] for d in general_declarations)
        names.update(d['name'] for d in numbered_declarations)
        config = json.loads((root / 'comparator.json').read_text())
        source_files = [p for p in sources(root) if p.name != 'lakefile.lean']
        roots = source_roots(root)
        solution_sources = [p for p in source_files
                            if module_for_source(p, roots) == config['solution_module']]
        if len(solution_sources) != 1:
            raise ValueError('Solution must resolve to exactly one submitted source')
        solution_declarations, solution_violations = scan(solution_sources, root)
        if solution_violations:
            raise ValueError(f'forbidden source in Solution: {solution_violations}')
        names.update(d['name'] for d in solution_declarations)
        selected = config['theorem_names'] + config.get('definition_names', [])
        names.update(selected)
        names.update(['DepthPaper.LowerRecursionTarget', 'DepthPaper.lower_recursion',
                      'DepthPaper.EndpointDeficitTarget', 'DepthPaper.endpoint_deficit',
                      'DepthPaper.EndpointRootTarget', 'DepthPaper.endpoint_root'])
        names = sorted(names)
        body = ['module', 'import DepthPaper', 'import GeneralDepthPaper',
                'import Verification', 'import ' + config['solution_module']]
        # Keep the audit imports explicit for the generated verification module.
        modules = [prefix + '.' + p.stem for prefix, paths in
                   [('DepthPaper', depth_sources), ('GeneralDepthPaper', general_sources)]
                   for p in paths if p.stem.endswith('Audit')]
        body.extend('import ' + m for m in modules + args.extra_module)
        body.extend(line for name in names for line in ('#check ' + name, '#print axioms ' + name))
        body.extend(statement for _, statement in EXACT_TARGETS)
        scratch = output / 'ExactDepthAudit.lean'
        scratch.write_text('\n'.join(body) + '\n', encoding='utf-8')
        # Build every committed source by its actual flattened source-root name.
        build_modules = [module_for_source(p, roots) for p in source_files]
        run(['lake', 'build', *sorted(set(build_modules))], root, output / 'all-sources-build.log')
        run(['lake', 'env', 'lean', str(scratch)], root, output / 'exact-targets-and-axioms.log')
        log = (output / 'exact-targets-and-axioms.log').read_text()
        axioms = {name: [a.strip() for a in values.split(',') if a.strip()] for name, values in
                  re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log)}
        axioms.update({name: [] for name in re.findall(r"'([^']+)' does not depend on any axioms", log)})
        absent = set(names) - axioms.keys()
        if absent: raise ValueError(f'missing transitive axiom reports: {sorted(absent)}')
        bad = {name: values for name, values in axioms.items() if set(values) - STANDARD}
        if bad: raise ValueError(f'forbidden transitive axioms: {bad}')
        if frozen != snapshot(root): raise ValueError('submitted sources changed during verification')
        report.update(exact_target_and_axiom_checks_passed=True,
                      proof_source_sha256=snapshot_digest(proof_identity),
                      source_snapshot=frozen, built_source_count=len(source_files),
                      checked_public_depth_declarations=len(declarations),
                      checked_public_general_depth_declarations=len(general_declarations),
                      checked_public_solution_declarations=len(solution_declarations),
                      checked_numbered_target_declarations=len(numbered_declarations),
                      checked_declarations=len(names), exact_targets=[label for label, _ in EXACT_TARGETS],
                      extra_target_modules=args.extra_module, per_declaration_axioms=axioms)
    except Exception as error:
        report['failure'] = str(error)
    if output.exists() and need_external:
        (output / 'depth-verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'source_snapshot'
                      and k != 'per_declaration_axioms'}, indent=2))
    return 0 if report['exact_target_and_axiom_checks_passed'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
