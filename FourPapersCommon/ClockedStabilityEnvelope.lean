module

public import FourPapersCommon.ClockedMeanSquareStability

@[expose] public section


/-! The uniform mean square bound in precisely the three perturbations:
covariance rate, terminal spatial jets, and integrated step coefficients. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus
open scoped Topology NNReal ENNReal
namespace FourPapersCommon
open Paper

theorem intervalIntegrable_coefficient_difference_square (d e : AdditiveDriftData) (a b : ℝ) :
    IntervalIntegrable (fun s => (d.coefficient s-e.coefficient s)^2) volume a b := by
  apply (intervalIntegrable_const (c := ((d.radius : ℝ)+e.radius)^2)).mono_fun'
    ((d.coefficient_measurable.sub e.coefficient_measurable).pow_const 2).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro s
  dsimp only [Pi.sub_apply]
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hn := (norm_sub_le (d.coefficient s) (e.coefficient s)).trans
    (add_le_add (d.coefficient_bound s) (e.coefficient_bound s))
  have hh := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ (d.radius : ℝ)+e.radius)).mpr hn
  simpa only [Real.norm_eq_abs,sq_abs] using hh

theorem integral_driftDiscrepancy_square_le (d e : AdditiveDriftData) {T R ε : ℝ}
    (hT : 0 ≤ T) (hR : 0 ≤ R) (hε : 0 ≤ ε) :
    (∫ s in 0..T,(driftDiscrepancy d e R ε s)^2) ≤
      2*(∫ s in 0..T,(d.coefficient s-e.coefficient s)^2)+2*R^2*ε^2*T := by
  have hh := intervalIntegral.integral_mono_on hT
    (intervalIntegrable_driftDiscrepancy_square d e hR hε 0 T)
    (((intervalIntegrable_coefficient_difference_square d e 0 T).const_mul 2).add
      (intervalIntegrable_const (c := 2*R^2*ε^2))) (fun s _ => by
        unfold driftDiscrepancy
        nlinarith only [sq_nonneg (|d.coefficient s-e.coefficient s|-R*ε),sq_abs (d.coefficient s-e.coefficient s)])
  rw [intervalIntegral.integral_add ((intervalIntegrable_coefficient_difference_square d e 0 T).const_mul 2)
    (intervalIntegrable_const (c := 2*R^2*ε^2)),intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at hh
  simpa only [sub_zero,smul_eq_mul,mul_comm,mul_left_comm,mul_assoc] using hh

theorem clockedItoState_mean_square_uniform_bound (d e : AdditiveDriftData)
    (c v : NonnegativeRate) (h T : ℝ) (hT : 0 ≤ T) {R L ε δ : ℝ}
    (hR : 0 ≤ R) (hL : 0 ≤ L) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (heR : (e.radius : ℝ) ≤ R) (heL : (e.gradientLip : ℝ) ≤ L)
    (hgrad : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖d.gradient t x-e.gradient t x‖ ≤ ε)
    (hrate : ∀ t ∈ Icc (0 : ℝ) T, ‖c.rate t.toNNReal-v.rate t.toNNReal‖ ≤ δ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (∫ ω,(clockedItoState d c h T hT t.toNNReal ω-clockedItoState e v h T hT t.toNNReal ω)^2
      ∂canonicalBrownianMeasure) ≤
      (2*δ*T+8*T*(∫ s in 0..T,(d.coefficient s-e.coefficient s)^2)+8*R^2*ε^2*T^2)*
        Real.exp (4*T*(R*L)^2*T) := by
  have hh := clockedItoState_mean_square_stability d e c v h T hT hR hL hε hδ heR heL hgrad hrate ht
  have hA := integral_driftDiscrepancy_square_le d e hT hR hε
  have hfront : 2*δ*T+4*T*(∫ s in 0..T,(driftDiscrepancy d e R ε s)^2) ≤
      2*δ*T+8*T*(∫ s in 0..T,(d.coefficient s-e.coefficient s)^2)+8*R^2*ε^2*T^2 := by
    calc
      _ ≤ 2*δ*T+4*T*(2*(∫ s in 0..T,(d.coefficient s-e.coefficient s)^2)+2*R^2*ε^2*T) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hA (by positivity))
      _ = _ := by ring
  have hnonneg : 0 ≤ 2*δ*T+4*T*(∫ s in 0..T,(driftDiscrepancy d e R ε s)^2) :=
    add_nonneg (by positivity) (mul_nonneg (by positivity)
      (intervalIntegral.integral_nonneg_of_forall hT (fun s => sq_nonneg _)))
  exact hh.trans (mul_le_mul hfront (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left ht.2 (by positivity))) (Real.exp_nonneg _) (hnonneg.trans hfront))

end FourPapersCommon
