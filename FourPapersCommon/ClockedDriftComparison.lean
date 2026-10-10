module

public import FourPapersCommon.ClockedStateContinuity

@[expose] public section


/-! Actual drift discrepancies for the coupled integral solutions. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus
open scoped Topology NNReal ENNReal
namespace FourPapersCommon
open Paper

def driftDiscrepancy (d e : AdditiveDriftData) (R ε : ℝ) (t : ℝ) : ℝ :=
  |d.coefficient t-e.coefficient t|+R*ε

theorem measurable_driftDiscrepancy (d e : AdditiveDriftData) (R ε : ℝ) :
    Measurable (driftDiscrepancy d e R ε) := by
  unfold driftDiscrepancy
  simpa only [Real.norm_eq_abs,Pi.sub_apply] using
    (d.coefficient_measurable.sub e.coefficient_measurable).norm.add_const (R*ε)

theorem driftDiscrepancy_nonneg (d e : AdditiveDriftData) {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 ≤ ε) (t : ℝ) : 0 ≤ driftDiscrepancy d e R ε t :=
  add_nonneg (abs_nonneg _) (mul_nonneg hR hε)

theorem driftDiscrepancy_bound (d e : AdditiveDriftData) {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 ≤ ε) (t : ℝ) :
    ‖driftDiscrepancy d e R ε t‖ ≤ (d.radius : ℝ)+e.radius+R*ε := by
  rw [Real.norm_of_nonneg (driftDiscrepancy_nonneg d e hR hε t)]
  unfold driftDiscrepancy
  rw [← Real.norm_eq_abs]
  exact add_le_add ((norm_sub_le _ _).trans
    (add_le_add (d.coefficient_bound t) (e.coefficient_bound t))) le_rfl

theorem additive_drift_sub_le (d e : AdditiveDriftData) {R L ε : ℝ}
    (hR : 0 ≤ R) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (heR : (e.radius : ℝ) ≤ R) (heL : (e.gradientLip : ℝ) ≤ L)
    (t x y : ℝ) (hgrad : ‖d.gradient t x-e.gradient t x‖ ≤ ε) :
    ‖d.coefficient t*d.gradient t x-e.coefficient t*e.gradient t y‖ ≤
      R*L*‖x-y‖+driftDiscrepancy d e R ε t := by
  have he : d.coefficient t*d.gradient t x-e.coefficient t*e.gradient t y =
      (d.coefficient t-e.coefficient t)*d.gradient t x+
      e.coefficient t*(d.gradient t x-e.gradient t x)+
      e.coefficient t*(e.gradient t x-e.gradient t y) := by ring
  rw [he]
  have hg := (e.gradient_lipschitz t).dist_le_mul x y
  rw [dist_eq_norm,dist_eq_norm] at hg
  have hc : ‖e.coefficient t‖ ≤ R := (e.coefficient_bound t).trans heR
  have h1 : ‖(d.coefficient t-e.coefficient t)*d.gradient t x‖ ≤
      |d.coefficient t-e.coefficient t| := by
    rw [norm_mul]
    simpa only [Real.norm_eq_abs,mul_one] using
      mul_le_mul_of_nonneg_left (d.gradient_bound t x) (norm_nonneg (d.coefficient t-e.coefficient t))
  have h2 : ‖e.coefficient t*(d.gradient t x-e.gradient t x)‖ ≤ R*ε := by
    rw [norm_mul]
    exact mul_le_mul hc hgrad (norm_nonneg _) hR
  have h3 : ‖e.coefficient t*(e.gradient t x-e.gradient t y)‖ ≤ R*L*‖x-y‖ := by
    rw [norm_mul]
    calc
      _ ≤ R*((e.gradientLip : ℝ)*‖x-y‖) := mul_le_mul hc hg (norm_nonneg _) hR
      _ ≤ R*(L*‖x-y‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right heL (norm_nonneg _)) hR
      _ = _ := by ring
  exact ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add h1 h2)) h3)).trans_eq (by
      unfold driftDiscrepancy
      ring)

theorem clockedItoDrift_sub_le (d e : AdditiveDriftData) (c v : NonnegativeRate)
    (h T : ℝ) (hT : 0 ≤ T) {R L ε : ℝ}
    (hR : 0 ≤ R) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (heR : (e.radius : ℝ) ≤ R) (heL : (e.gradientLip : ℝ) ≤ L)
    (hgrad : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖d.gradient t x-e.gradient t x‖ ≤ ε)
    (t : ℝ≥0) (ht : (t : ℝ) ≤ T) (ω : BrownianSample) :
    ‖clockedItoDrift d c h T hT t ω-clockedItoDrift e v h T hT t ω‖ ≤
      R*L*‖clockedItoState d c h T hT t ω-clockedItoState e v h T hT t ω‖+
        driftDiscrepancy d e R ε t := by
  simp only [clockedItoDrift,ite_eq_left ht]
  exact additive_drift_sub_le d e hR hL hε heR heL t _ _ (hgrad t ⟨t.coe_nonneg,ht⟩ _)

end FourPapersCommon
