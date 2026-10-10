module

public import FourPapersCommon.ClockedStabilityEnvelope

@[expose] public section


/-! Actual uniform L² convergence of the coupled clocked diffusions. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus
open scoped Topology NNReal ENNReal
namespace FourPapersCommon
open Paper

theorem tendstoUniformlyOn_clockedItoState_difference_square
    {ι : Type*} {F : Filter ι} (d : ι → AdditiveDriftData) (e : AdditiveDriftData)
    (c : ι → NonnegativeRate) (v : NonnegativeRate) (h T : ℝ) (hT : 0 ≤ T)
    (R L : ℝ) (hR : 0 ≤ R) (hL : 0 ≤ L)
    (heR : (e.radius : ℝ) ≤ R) (heL : (e.gradientLip : ℝ) ≤ L)
    (ε δ : ι → ℝ) (hε : ∀ n,0 ≤ ε n) (hδ : ∀ n,0 ≤ δ n)
    (hgrad : ∀ n,∀ t ∈ Icc (0 : ℝ) T,∀ x,‖(d n).gradient t x-e.gradient t x‖ ≤ ε n)
    (hrate : ∀ n,∀ t ∈ Icc (0 : ℝ) T,‖(c n).rate t.toNNReal-v.rate t.toNNReal‖ ≤ δ n)
    (htε : Tendsto ε F (𝓝 0)) (htδ : Tendsto δ F (𝓝 0))
    (htcoeff : Tendsto (fun n => ∫ s in 0..T,((d n).coefficient s-e.coefficient s)^2) F (𝓝 0)) :
    TendstoUniformlyOn (fun n t => ∫ ω,(clockedItoState (d n) (c n) h T hT t.toNNReal ω-
      clockedItoState e v h T hT t.toNNReal ω)^2 ∂canonicalBrownianMeasure)
      (fun _ => 0) F (Icc (0 : ℝ) T) := by
  let C : ι → ℝ := fun n =>
    (2*δ n*T+8*T*(∫ s in 0..T,((d n).coefficient s-e.coefficient s)^2)+8*R^2*(ε n)^2*T^2)*
      Real.exp (4*T*(R*L)^2*T)
  have hC : Tendsto C F (𝓝 0) := by
    have h1 : Tendsto (fun n => 2*δ n*T) F (𝓝 0) := by
      simpa only [mul_zero,zero_mul] using (htδ.const_mul 2).mul_const T
    have h2 : Tendsto (fun n => 8*T*(∫ s in 0..T,((d n).coefficient s-e.coefficient s)^2)) F (𝓝 0) := by
      simpa only [mul_zero] using htcoeff.const_mul (8*T)
    have h3 : Tendsto (fun n => 8*R^2*(ε n)^2*T^2) F (𝓝 0) := by
      simpa only [zero_pow (by norm_num : 2 ≠ 0),mul_zero,zero_mul] using
        ((htε.pow 2).const_mul (8*R^2)).mul_const (T^2)
    simpa only [C,mul_zero,zero_mul,zero_pow (by norm_num : 2 ≠ 0),add_zero] using
      ((h1.add h2).add h3).mul_const (Real.exp (4*T*(R*L)^2*T))
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro η hη
  filter_upwards [(tendsto_order.mp hC).2 η hη] with n hn
  intro t ht
  have hb := clockedItoState_mean_square_uniform_bound (d n) e (c n) v h T hT
    hR hL (hε n) (hδ n) heR heL (hgrad n) (hrate n) ht
  have hnonneg : 0 ≤ ∫ ω,(clockedItoState (d n) (c n) h T hT t.toNNReal ω-
      clockedItoState e v h T hT t.toNNReal ω)^2 ∂canonicalBrownianMeasure :=
    integral_nonneg (fun ω => sq_nonneg _)
  simpa only [Real.dist_eq,zero_sub,abs_neg,abs_of_nonneg hnonneg] using hb.trans_lt hn

end FourPapersCommon
