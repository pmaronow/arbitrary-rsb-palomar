module

public import FourPapersCommon.ClockedDriftSquare
public import FourPapersCommon.IntegralGronwall

@[expose] public section


/-! A quantitative, genuine coupled L² stability estimate. Time coefficient
errors are integrated, so moving discontinuities are allowed. The covariance
rate may vanish, and no derivative of a Brownian path is used. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus
open scoped Topology NNReal ENNReal
namespace FourPapersCommon
open Paper

theorem clockedItoState_mean_square_stability (d e : AdditiveDriftData)
    (c v : NonnegativeRate) (h T : ℝ) (hT : 0 ≤ T) {R L ε δ : ℝ}
    (hR : 0 ≤ R) (hL : 0 ≤ L) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (heR : (e.radius : ℝ) ≤ R) (heL : (e.gradientLip : ℝ) ≤ L)
    (hgrad : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖d.gradient t x-e.gradient t x‖ ≤ ε)
    (hrate : ∀ t ∈ Icc (0 : ℝ) T, ‖c.rate t.toNNReal-v.rate t.toNNReal‖ ≤ δ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (∫ ω,(clockedItoState d c h T hT t.toNNReal ω-clockedItoState e v h T hT t.toNNReal ω)^2
      ∂canonicalBrownianMeasure) ≤
      (2*δ*T+4*T*(∫ s in 0..T,(driftDiscrepancy d e R ε s)^2))*
        Real.exp (4*T*(R*L)^2*t) := by
  let u : ℝ → ℝ := fun s => ∫ ω,(clockedItoState d c h T hT s.toNNReal ω-
    clockedItoState e v h T hT s.toNNReal ω)^2 ∂canonicalBrownianMeasure
  let a : ℝ → ℝ := fun s => (driftDiscrepancy d e R ε s)^2
  let b : ℝ → ℝ := fun s => ∫ ω,(clockedDriftDifference d e c v h T hT s ω)^2
    ∂canonicalBrownianMeasure
  have hu : Continuous u := continuous_clocked_state_difference_square d e c v h T hT
  have ha (x y : ℝ) : IntervalIntegrable a volume x y :=
    intervalIntegrable_driftDiscrepancy_square d e hR hε x y
  have hb (x y : ℝ) : IntervalIntegrable b volume x y :=
    intervalIntegrable_clockedDriftDifference_square_mean d e c v h T hT x y
  have hun (s : ℝ) : 0 ≤ u s := integral_nonneg (fun ω => sq_nonneg _)
  have han (s : ℝ) : 0 ≤ a s := sq_nonneg _
  have hδ0 : 0 ≤ 2*δ*T+4*T*(∫ s in 0..T,a s) := by
    exact add_nonneg (by positivity)
      (mul_nonneg (by positivity) (intervalIntegral.integral_nonneg_of_forall hT han))
  have hK : 0 ≤ 4*T*(R*L)^2 := by positivity
  have hbound (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      u s ≤ (2*δ*T+4*T*(∫ r in 0..T,a r))+
        (4*T*(R*L)^2)*(∫ r in 0..s,u r) := by
    have h0 := clockedItoState_sub_square_le_integral d e c v h T hT s.toNNReal
    simp only [Real.coe_toNNReal s hs.1] at h0
    change u s ≤ 2*dist (rateClock c s.toNNReal) (rateClock v s.toNNReal)+2*s*(∫ r in 0..s,b r) at h0
    have hnoise := rateClock_dist_le_of_rate_bound c v hT hδ hrate s.toNNReal
      (by simpa only [Real.coe_toNNReal s hs.1] using hs.2)
    have hmono : (∫ r in 0..s,b r) ≤ ∫ r in 0..s,2*(R*L)^2*u r+2*a r :=
      intervalIntegral.integral_mono_on hs.1 (hb 0 s)
        (((hu.intervalIntegrable _ _).const_mul (2*(R*L)^2)).add ((ha 0 s).const_mul 2))
        (fun r hr => clockedDriftDifference_square_mean_le d e c v h T hT hR hL hε heR heL
          hgrad ⟨hr.1,hr.2.trans hs.2⟩)
    rw [intervalIntegral.integral_add ((hu.intervalIntegrable _ _).const_mul (2*(R*L)^2))
      ((ha 0 s).const_mul 2),intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hmono
    have hIu : 0 ≤ ∫ r in 0..s,u r := intervalIntegral.integral_nonneg_of_forall hs.1 hun
    have hIa : 0 ≤ ∫ r in 0..s,a r := intervalIntegral.integral_nonneg_of_forall hs.1 han
    have hIaT : (∫ r in 0..s,a r) ≤ ∫ r in 0..T,a r :=
      intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2
        (.of_forall han) (ha 0 T)
    calc
      _ ≤ _ := h0
      _ ≤ 2*(δ*T)+2*s*(2*(R*L)^2*(∫ r in 0..s,u r)+2*(∫ r in 0..s,a r)) :=
        add_le_add (mul_le_mul_of_nonneg_left hnoise (by norm_num))
          (mul_le_mul_of_nonneg_left hmono (mul_nonneg (by norm_num) hs.1))
      _ ≤ 2*(δ*T)+2*T*(2*(R*L)^2*(∫ r in 0..s,u r)+2*(∫ r in 0..s,a r)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hs.2 (by norm_num))
          (add_nonneg (mul_nonneg (by positivity) hIu) (mul_nonneg (by norm_num) hIa)))
      _ ≤ 2*(δ*T)+2*T*(2*(R*L)^2*(∫ r in 0..s,u r)+2*(∫ r in 0..T,a r)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (mul_le_mul_of_nonneg_left hIaT (by norm_num))) (by positivity))
      _ = _ := by ring
  exact le_exp_of_integral_le u hu T _ _ hδ0 hK (fun s _ => hun s) hbound t ht

end FourPapersCommon
