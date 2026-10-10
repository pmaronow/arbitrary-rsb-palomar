# Verification record

The checked proof-source SHA-256 is
`9792fcb5d961164fe66a9e472e0de063a1378f48a75b957d56601394c7bb8d7b`. It identifies all **1,931 Lean
sources** and the pinned build/comparison inputs. Checks completed on
2026-10-10T22:32:01.194992+00:00. The results below concern this exact proof-source
identity.

The corrected manuscript SHA-256 is
`1216a3820a4d632228f0a1218a53c1feda73d04a6bb11ab3eab8cfa1db9c2b9f`.
The supplied Revision (16) SHA-256 is
`3302e39b8554fa851811c402d8aee3ccf32c8f37c727066f5c2fb79cd233bea6`.
Only two prose sentences changed; mathematical statements and numbering
are preserved.

The proof-source identity hashes a sorted map of relative paths to SHA-256
values as compact JSON: every Lean source, `lean-toolchain`,
`lakefile.toml`, `lake-manifest.json`, and `comparator.json`.
Documentation is outside this identity. The verification tools also
require an unchanged complete repository-file snapshot during each run.

The compiler was Lean 4.35.0-rc2, commit
`11acb17ec6b07a8f9e9173e6845197929540936b`, with canonical Mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

## Completed checks

| Check | Result |
|---|---|
| Mathematical fidelity | Automated comparison completed; exact scopes are in [coverage](../COVERAGE.md) |
| Every Lean source | Passed: all 1,931 sources |
| Expanded targets and transitive axioms | Passed: 5,711 unique named declarations; standard three axioms only |
| Theorems 1.1 and 1.2 Comparator | Passed independent Challenge comparison and Lean, NanoDa, con-ron |
| Additional explicit target closures | Passed: all 68 Verification declarations across 10 modules and their dependencies; all three kernels |
| Canonical dependencies and Challenge imports | Passed: all nine pins, imported Git blobs, canonical release and ancestry; checked online |

The axiom audit scans the public declarations in the DepthPaper and
GeneralDepthPaper source trees, Solution, and every Verification module,
and checks 5711 unique collected names. It includes
all 68 public Verification declarations.
Source-file group counts need not be additive: names are deduplicated,
and a file can declare results in another namespace. Each transitive axiom set is contained in
`propext`, `Classical.choice`, and `Quot.sound`. The selected proofs and
their dependencies have no proof holes or forbidden axioms. The two
intentional Challenge theorem placeholders are outside these proved closures.

For the two headline proofs, con-ron accepted **87,375 declarations** in verified mode; Lean and NanoDa accepted the same selected proof closures. The separate export of all 68 Verification declarations and their dependencies passed Lean, NanoDa (**91,610 declarations with no typechecker errors**) and con-ron (**89,078 declarations** in verified mode). This additional replay verifies the stated target closures; it does not compare every numbered target with an independent Challenge declaration.

The numbered-target modules are selected dynamically from every
`Verification/*.lean` source. They include Section 2, Section 4, the
optimized value, Appendix A/C, one-step diffusion law, closed-domain
implicit-function theorem, finite-atomic clock-form stochastic targets,
and the full finite-atomic physical Brownian target, along with the
preserved legacy and revised targets. Specifications with type `Prop`
are not counted as proofs merely because they are defined.

## Mathematical scope

The selected headline theorems are proved with the paper's hypotheses,
including the quadratic-inclusive subcritical covariance class and paper
nondegeneracy. Hessian positivity is derived. The independent finite-scheme
interface is proved equivalent to minimization over all probability measures.

All 41 nonremark numbered targets have complete or explicitly stronger
faithful interfaces. The printed finite-support scope of Lemma 2.2 now
includes a genuine physical standard Brownian motion on the original
sample space, the same driver's actual state equation, and the literal
square-root-volatility-times-Hessian integral. Its physical left sums have
proved cell-mesh and endpoint limits, with the actual continuous gradient
as a continuous modification. Equality holds almost surely at each fixed time.
Both endpoint atoms and zero origin volatility are included. The alternate
proof uses normalized-time Ito calculus,
deterministic inverse-clock Wiener transport and an L2 comparison. It does
not assume raw natural-filtration equality or a stochastic representation.
No arbitrary-measure Hessian-integral extension is asserted.

General-measure time PDE statements use weak or distributional time
derivatives. The four remarks are explanatory context; Remark A.8's
complete all-positive Banach smoothness wording is not separately
certified. This does not claim a complete formalization of all cited
background. See [coverage](../COVERAGE.md) for exact domains, norm
conventions, proof routes and conditional infrastructure.

## Reproducing the checks

The [README](../README.md) gives the commands. `tools/check_depth.py` builds
every Lean source and generates an external expanded-target and axiom
audit. `scripts/verify-comparator.sh` uses the pinned release's Comparator
and all three bundled kernels. `tools/check_revised_kernels.py` exports
every public Verification target with the same primitive declarations used
by Comparator and requires all three kernels. Reports, raw logs, generated
Lean and exports stay outside the public source tree.

`tools/check_dependencies.py --online` checks the actual canonical Challenge
import closure, materialized Git revisions/trees/blobs, and public GitHub
commit/tag/ancestry evidence. No digital signature is inferred.
`tools/check_repository.py` checks metadata, source layout, exact pins and
source limits. The recorded revision also passed the primary source-contract
checks and MIT license detection.

## Recorded verification contracts

The upstream heads were rechecked on 2026-10-10T22:24:01.991307+00:00:

| Source | Revision |
|---|---|
| [Source policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/96b034cc31a72a63d4f4041911dce337a85c9a04/docs/specification.md) | `96b034cc31a72a63d4f4041911dce337a85c9a04` |
| [Source-layout verifier](https://github.com/PalomarRegistry/PalomarSubmission/blob/d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44/scripts/verify_submission.py) | `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44` |
| [Comparator template](https://github.com/PalomarRegistry/PalomarTemplate/blob/2891de4c48955af824969a263d31b25e7a9a1406/scripts/verify-comparator.sh) | `2891de4c48955af824969a263d31b25e7a9a1406` |
| [Metadata schema v0.4](https://github.com/mathlib-initiative/formalization.yaml/blob/99c678e569c7c4c0772db297c5ddd5e4c9b6322e/schema/v0.4.schema.json) | `99c678e569c7c4c0772db297c5ddd5e4c9b6322e` |

The recorded source-layout verifier requires Lean at least 4.35.0-rc2 and
matching canonical
Mathlib, module headers, at most 10,000 physical lines per source, and a
Challenge of at most 1,000 lines and 100 KiB. This Challenge has
229 lines and 11,979 bytes. Original code
and documentation use MIT; vendor licenses and notices remain preserved.

## Compiler compatibility

The initial mechanical port added module, export, and import-visibility declarations to 1,297 legacy sources. Reversing those additions recovered their pre-port bytes exactly. Another 87 inherited module sources required no insertion. A private-helper compatibility option is present in 175 files; it changes visibility without introducing an axiom. Later docstring corrections distinguish historical numbering from the current manuscript without changing mathematical declarations.

Eleven inherited files required further compiler compatibility repairs: six import-only files, four vendored files with local proof repairs, and one file with a theorem-local resource adjustment.

| Files | Final repair |
|---|---|
| [IndependentEndpoint.lean](../vendor/spin-glass-foundations/Lemmas/SmartPath/IndependentEndpoint.lean), [CanonicalModel.lean](../vendor/spin-glass-foundations/Lemmas/Gaussian/CanonicalModel.lean), [Price/Gaussian.lean](../vendor/spin-glass-foundations/Lemmas/Price/Gaussian.lean), [gaussian_concentration.lean](../vendor/spin-glass-foundations/Lemmas/SpinGlass/gaussian_concentration.lean), [Transport.lean](../vendor/spin-glass-foundations/Lemmas/Concentration/Transport.lean), and [PhysicalSKBridge.lean](../Paper/PhysicalSKBridge.lean) | Explicit public imports expose the required Gaussian-law, Gaussian-moment, and independence-integration APIs. Declaration types and proof bodies are unchanged. |
| [KSInequality.lean](../vendor/spin-glass-foundations/Lemmas/SmartPath/KSInequality.lean) | One local positivity subproof in `kearns_saul_inequality` applies `Real.artanh_pos` directly with the existing hypotheses. |
| [Interpolation.lean](../vendor/spin-glass-foundations/Lemmas/SmartPath/Interpolation.lean) | One pointwise algebra subproof in `pressure_derivative_ibp` applies the existing `pressure_trace_algebra` identity and `linarith only`. |
| [SmallNegative.lean](../vendor/spin-glass-foundations/Lemmas/GuerraTalagrand/Flatness/Cases/SmallNegative.lean) | Two zero-scale endpoint subproofs explicitly unfold `gtHalfStepEndpoint` and use `Real.exp_ne_zero`, preserving the two flatness derivative identities. |
| [ParisiCascadeSorting.lean](../vendor/spin-glass-foundations/Targets/ParisiCascadeSorting.lean) | Three proof sites in the ordered-insertion and insertion-sort inequalities use the public `List.orderedInsert_nil`, `List.insertionSort_nil`, and `List.insertionSort_cons` equations. |
| [DiracSoftMoment.lean](../Paper/DiracSoftMoment.lean) | The existing theorem-local heartbeat budget increases from 1,000,000 to 2,000,000. Declaration types and proof bodies are unchanged. |

The four vendored proof-repair files contain seven changed local proof sites across six enclosing theorem declarations. A byte comparison recovers the mechanical-port checkpoint after reversing precisely those seven replacements and the recorded added imports. Together with the resource-only comparison for `DiracSoftMoment`, these checks establish that every inherited theorem statement and definition body remains unchanged. Other inherited proof bodies are unchanged outside the seven identified sites.

All eleven repaired sources passed targeted compiler checks on Lean 4.35.0-rc2 with the pinned mathlib revision. These checks use the compiled dependency environment. The full repository build, exact-target and transitive-axiom audit, Comparator run, and independent kernel replay are separate checks whose final outcomes appear above.
