# Replica symmetry breaking at arbitrary depth

This repository formalizes finite-step replica symmetry breaking in mixed even
spin Ising models at positive temperature and zero external field. It is based
on *Replica symmetry breaking at arbitrary depth* by P. M. Aronow and Patrick
Lopatto ([arXiv:2609.05317](https://arxiv.org/abs/2609.05317)).

The selected results are Theorems 1.1 and 1.2. Theorem 1.1 says that for every finite depth `k`, there are
strictly increasing even exponents starting at four and a nonempty open set of
positive coefficients whose Parisi measures have exactly `k + 1` support
points. The development also includes depth zero. Coefficients describe the
effective covariance `Ξ = β² ξ₀`; normalized mixture weights sum to one after
dividing by `β²`.

Theorem 1.2 starts from a nondegenerate atomic Parisi minimizer for a finite
even covariance, including a quadratic term when `Ξ″(0) < 1`. Adding a
sufficiently high even interaction produces a unique transition threshold:
the depth stays `r` at and below the threshold and becomes `r + 1` above it,
throughout a closed coupling window. The threshold tends to twice the
physical entropy density `pressure(1) − pressure′(1)`, which is proved positive.

`Challenge.lean` states both results using concrete Gaussian Cole–Hopf recursions
and probability measures. Its minimization comparison ranges over every
finite scheme of every competing depth, including endpoint atoms and zero
masses. This is the finite-step variational characterization of the Parisi
minimum. The proof development constructs an optimizer over all probability
measures; `Solution.lean` connects that optimizer to the independent statement.
The correspondence and its scope are described in [COVERAGE.md](COVERAGE.md).

## Source layout

- [Challenge.lean](Challenge.lean) contains the independently readable statements
  and two deliberate theorem placeholders.
- [Solution.lean](Solution.lean) supplies the corresponding proof and the
  bridges to the concrete recursion.
- [DepthPaper/](DepthPaper/) contains the arbitrary-depth development.
- [GeneralDepthPaper/](GeneralDepthPaper/) extends the transition theory to
  finite even covariances with quadratic terms. Its revised interfaces derive
  Hessian positivity from the paper's nondegeneracy conditions.
- `Paper/`, `FRSB/`, `FourPapersCommon/`, and the smaller supporting namespaces
  contain its mathematical dependencies.
- [vendor/](vendor/) preserves the required external foundation sources,
  licenses, and notices.
- [formalization.yaml](formalization.yaml) records scope, sources, authorship,
  automation, and review status; [comparator.json](comparator.json) selects the
  declarations compared with the independent statements.
- [tools/](tools/) and [scripts/](scripts/) provide reproducible checks.

## Installation and verification

Use the exact release in [lean-toolchain](lean-toolchain),
`leanprover/lean4:v4.35.0-rc2`, with Lake available on `PATH`. Mathlib and its
dependencies are pinned in the committed [lake-manifest.json](lake-manifest.json).
Python 3.11 or newer and the packages in [tools/requirements.txt](tools/requirements.txt)
are needed for the audit tools. The Comparator check requires Linux with
Bubblewrap and the checkers bundled with this Lean release.

```sh
lake exe cache get
lake build
python3 -m venv ../arbitrary-rsb-tools
. ../arbitrary-rsb-tools/bin/activate
python3 -m pip install -r tools/requirements.txt
python3 tools/check_repository.py
python3 tools/check_dependencies.py --online --json ../arbitrary-rsb-dependencies.json
python3 tools/check_depth.py --output ../arbitrary-rsb-verification
bash scripts/verify-comparator.sh
python3 tools/check_revised_kernels.py --output ../arbitrary-rsb-revised-kernels
```

The depth checker builds every Lean source, checks explicit legacy and revised
target types, and audits the public declarations in both depth developments,
Solution, and Verification. Comparator checks the selected proofs against
`Challenge.lean` and replays the exported proofs with Lean's kernel, NanoDa,
and con-ron. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted. Raw verification outputs are
written outside the source tree. Current results and the exact checked source
identity are recorded in [docs/VERIFICATION.md](docs/VERIFICATION.md).
The additional kernel command replays the explicit paper targets and their
dependencies; independent Challenge comparison concerns the selected Theorems
1.1 and 1.2 interfaces.

## Mathematical scope

The headline results are the arbitrary-depth open-phase existence theorem
and the universal transition. The revised transition interfaces allow quadratic
terms under
`Ξ″(0) < 1` and use the paper's nondegeneracy definition. The actual atomic
Hessian is proved positive from stationarity and negative contact curvature;
it is no longer an input to the revised transition theorem. Finite atomic
seeds use ordered positive-mass coordinates with the origin fixed, as in the
paper's definition. The legacy namespace preserves its earlier hypotheses.

The entropy proofs establish the diffusion identity and strict positivity.
The transition construction also retains its alternative finite Gibbs entropy
argument with the physical Parisi formula. General-measure time PDE assertions use weak or distributional time
derivatives; atomic breakpoints require within-cell or one-sided derivatives.
For every finite-support probability measure, Lemma 2.2 has the literal
physical-time representation with coefficient `sqrt (Ξ″(q))` times the actual
Hessian along the actual diffusion. A standard Brownian motion is constructed
on the same probability space and drives both the state equation and this
Hessian integral. Equality holds almost surely at each fixed time; the actual
continuous gradient is a continuous modification of the integral. The proof
includes atoms at zero and one and covariances
with `Ξ″(0) = 0`. It uses normalized-time Itô calculus, deterministic Wiener
transport and an L² comparison of actual physical-time left sums.
The four numbered remarks remain context; Remark A.8's entire all-positive
Banach smoothness wording is not separately certified.
The coverage document distinguishes proved targets, conditional infrastructure,
definitions, cited background, and the exact domains of the 41 proved
nonremark targets.

## Attribution and licensing

Formalization authors and responsible maintainers: **P. M. Aronow and Patrick
Lopatto**. Sol 6.1 autoformalized the original development. Subsequent Codex
preparation, compiler compatibility work, mathematical proof extensions, and automated review are credited
separately in [docs/PROVENANCE.md](docs/PROVENANCE.md). Authorship and maintainer
responsibility do not imply human mathematical review.

Original code and documentation use the [MIT license](LICENSE). Vendored code
retains its own Apache-2.0 licenses and copyright notices; see the provenance
document for the file-level license mapping.

