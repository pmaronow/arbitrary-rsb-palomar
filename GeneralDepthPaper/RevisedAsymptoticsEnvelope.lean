module

public import GeneralDepthPaper.RevisedAsymptoticsDerivatives

@[expose] public section

/-! The stationary mass function used in the revised asymptotic interface
is the derivative of the actual scalar objective after the lower stationary
coordinates have been substituted. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace GeneralDepthPaper
namespace LimitingStandingData
variable {Ξ : AdmissibleCovariance} {r : ℕ} {seed : AtomicPoint r}

def revisedScalarObjective (d : LimitingStandingData Ξ seed) (p : ℕ)
    (theta : ℝ × ℝ) : ℝ :=
  stationaryReducedObjective Ξ p d.cutoff d.stripRateLower d.stripRateUpper
    (theta, d.stationaryBranch p theta)

theorem revisedScalarObjective_massDerivative_eventually (d : LimitingStandingData Ξ seed) :
    ∀ᶠ p : ℕ in atTop, ∀ _he : Even p, ∀ theta ∈ d.parameterWindow,
      HasDerivAt (fun m => d.revisedScalarObjective p (theta.1, m))
        (d.stationaryMassFunction p theta) theta.2 := by
  obtain ⟨_, _, _, _, _, Hs⟩ := d.stationaryBranch_eventually
  obtain ⟨_, _, _, _, _, Hr⟩ := d.stationaryBranch_regular_error_eventually
  filter_upwards [Hs, Hr] with p hs hr he theta ht
  let z := d.stationaryBranch p theta
  let F := stationaryReducedObjective Ξ (r := r) p d.cutoff d.stripRateLower d.stripRateUpper
  let q := fun m : ℝ => d.stationaryBranch p (theta.1, m)
  have hzball : z ∈ closedBall seed d.radius := ball_subset_closedBall (hs he theta ht).1
  have hF : ContDiffAt ℝ ∞ F (theta, z) := (hr he theta ht).2.1 z hzball
  have hq : DifferentiableAt ℝ q theta.2 :=
    ((hr he theta ht).1.comp theta.2 (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt
      (by simp)
  have hinput : HasDerivAt (fun m : ℝ => ((theta.1, m), q m))
      ((0, 1), deriv q theta.2) theta.2 :=
    ((hasDerivAt_const theta.2 theta.1).prodMk (hasDerivAt_id theta.2)).prodMk hq.hasDerivAt
  have hFD : HasFDerivAt F (fderiv ℝ F (theta, z)) (theta, z) :=
    (hF.differentiableAt (by simp)).hasFDerivAt
  have hchain := hFD.comp_hasDerivAt
    (f := fun m : ℝ => ((theta.1, m), q m)) theta.2 hinput
  have hgradient : partialGradient F theta z = 0 := (hs he theta ht).2.1
  have hvary : fderiv ℝ F (theta, z) (0, deriv q theta.2) = 0 := by
    rw [partialGradient_eq_fullDerivative F (hF.differentiableAt (by simp))] at hgradient
    have heq := congrArg (fun L : AtomicPoint r →L[ℝ] ℝ => L (deriv q theta.2)) hgradient
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      zero_apply] using heq
  have hvalue : fderiv ℝ F (theta, z) ((0, 1), deriv q theta.2) =
      d.stationaryMassFunction p theta := by
    rw [show (((0, 1) : ℝ × ℝ), deriv q theta.2) =
      ((0, 1), (0 : AtomicPoint r)) + (0, deriv q theta.2) by simp,
      map_add, hvary, add_zero]
    rfl
  simpa only [Function.comp_def, revisedScalarObjective, q, F, z, hvalue,
    Prod.eta] using hchain

end LimitingStandingData
end GeneralDepthPaper
