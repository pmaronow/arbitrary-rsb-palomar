module

public import DepthPaper.StationaryBranchProposition
public import DepthPaper.LowerGeometryLemma
public import DepthPaper.StationaryHighOverlapGeometry
public import DepthPaper.GardnerTransition
public import DepthPaper.StationaryGardnerAsymptotics
public import DepthPaper.AllDepthIteration

public section

/-!
# Exact types of selected supporting results

These declarations check that the retained proofs inhabit their complete
proposition-valued targets with all quantified covariance, depth, seed,
atomic-coordinate and nondegeneracy hypotheses present. The target definitions
are concrete propositions in the cited modules; these checks neither assume
those propositions nor replace them with weaker conclusions.

The stationary and transition targets use `AdmissibleCovariance`, whose even
degrees begin at four, and `Nondegenerate`, which includes a positive atomic
Hessian. They are supporting results for that restricted model class. They do
not certify the revised paper's universal Theorem 1.2, which also permits a
quadratic interaction and uses a weaker nondegeneracy condition. Old theorem
numbers in retained module documentation refer to the earlier manuscript.

The quartic seed checks correspond to revised Lemma 2.9, with the stronger
nondegeneracy condition explicitly retained. The all-depth polynomial construction corresponds to the revised paper's
Proposition 5.1 (earlier Proposition 6.1). The exact source mapping and remaining
limitations are recorded in `COVERAGE.md`.
-/

namespace Verification

/-- Exact quartic seed optimizer, corresponding to the revised Lemma 2.9. -/
theorem quarticSeedMinimizer_exact :
    DepthPaper.parisiMinimizer DepthPaper.quarticSeed = Paper.diracOverlap 0 (by norm_num) :=
  DepthPaper.quarticSeed_parisiMinimizer

/-- Exact quartic seed nondegeneracy, with the development's stronger predicate. -/
theorem quarticSeedNondegenerate_exact :
    DepthPaper.Nondegenerate DepthPaper.quarticSeed (0 : DepthPaper.AtomicPoint 0)
      DepthPaper.isAtomicPoint_zero_depth :=
  DepthPaper.quarticSeed_nondegenerate

/-- Exact conditional stationary-branch target, including every seed hypothesis. -/
theorem stationaryBranches_exact :
    ∀ (Ξ : DepthPaper.AdmissibleCovariance) (r : ℕ)
      (seed : DepthPaper.AtomicPoint r) (hz : DepthPaper.IsAtomicPoint seed),
      DepthPaper.Nondegenerate Ξ seed hz → DepthPaper.StationaryBranchesTarget Ξ seed := by
  intro Ξ r seed hz hnd
  exact DepthPaper.stationary_branches Ξ seed hz hnd

/-- Exact lower-contact geometry target under the retained nondegeneracy condition. -/
theorem lowerGeometry_exact :
    ∀ (Ξ : DepthPaper.AdmissibleCovariance) (r : ℕ)
      (seed : DepthPaper.AtomicPoint r) (hz : DepthPaper.IsAtomicPoint seed),
      DepthPaper.Nondegenerate Ξ seed hz → DepthPaper.LowerGeometryTarget Ξ seed := by
  intro Ξ r seed hz hnd
  exact DepthPaper.lower_geometry Ξ seed hz hnd

/-- Exact high-overlap geometry target under the retained nondegeneracy condition. -/
theorem highOverlapGeometry_exact :
    ∀ (Ξ : DepthPaper.AdmissibleCovariance) (r : ℕ)
      (seed : DepthPaper.AtomicPoint r) (hz : DepthPaper.IsAtomicPoint seed),
      DepthPaper.Nondegenerate Ξ seed hz → DepthPaper.HighOverlapGeometryTarget Ξ seed := by
  intro Ξ r seed hz hnd
  exact DepthPaper.high_overlap_geometry Ξ seed hz hnd

/-- Exact transition target for the restricted covariance and seed hypotheses. -/
theorem gardnerTransition_exact :
    ∀ (Ξ : DepthPaper.AdmissibleCovariance) (r : ℕ)
      (seed : DepthPaper.AtomicPoint r) (hz : DepthPaper.IsAtomicPoint seed),
      DepthPaper.Nondegenerate Ξ seed hz → DepthPaper.GardnerTransitionTarget Ξ seed := by
  intro Ξ r seed hz hnd
  exact DepthPaper.gardner_transition Ξ seed hz hnd

/-- Exact mass/location asymptotic target for the restricted covariance class. -/
theorem gardnerAsymptotics_exact :
    ∀ (Ξ : DepthPaper.AdmissibleCovariance) (r : ℕ)
      (seed : DepthPaper.AtomicPoint r) (hz : DepthPaper.IsAtomicPoint seed),
      DepthPaper.Nondegenerate Ξ seed hz → DepthPaper.GardnerAsymptoticsTarget Ξ seed := by
  intro Ξ r seed hz hnd
  exact DepthPaper.gardner_asymptotics Ξ seed hz hnd

/-- Exact polynomial target at every natural-number depth, including depth zero. -/
theorem arbitraryDepthPolynomial_exact :
    ∀ k : ℕ, DepthPaper.ArbitraryDepthPolynomialTarget k :=
  DepthPaper.arbitrary_depth_polynomial

/-- Expanded ordered-model construction, corresponding to revised Proposition 5.1. -/
theorem arbitraryDepthIteration_exact :
    ∀ k : ℕ, ∃ D : DepthPaper.OrderedCovarianceModel k,
      ∃ z : DepthPaper.AtomicPoint k, ∃ hz : DepthPaper.IsAtomicPoint z,
        DepthPaper.Nondegenerate D.covariance z hz :=
  DepthPaper.arbitrary_depth_iteration

end Verification
