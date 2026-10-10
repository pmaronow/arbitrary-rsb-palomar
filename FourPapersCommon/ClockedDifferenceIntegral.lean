module

public import FourPapersCommon.ClockedStateContinuity
public import FourPapersCommon.IntegralSquareBound

@[expose] public section


/-! The actual coupled state equation and its mean square integral bound. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus
open scoped Topology NNReal ENNReal
namespace FourPapersCommon
open Paper
section Coupled
variable (d e : AdditiveDriftData) (c v : NonnegativeRate) (h T : ℝ) (hT : 0 ≤ T)

def clockedDriftDifference (s : ℝ) (ω : BrownianSample) : ℝ :=
  clockedItoDrift d c h T hT s.toNNReal ω-clockedItoDrift e v h T hT s.toNNReal ω

theorem measurable_clockedDriftDifference : Measurable (Function.uncurry
    (clockedDriftDifference d e c v h T hT)) :=
  ((measurable_clockedItoDrift d c h T hT).sub (measurable_clockedItoDrift e v h T hT)).comp
    (measurable_fst.real_toNNReal.prodMk measurable_snd)

theorem norm_clockedDriftDifference_le (s : ℝ) (ω : BrownianSample) :
    ‖clockedDriftDifference d e c v h T hT s ω‖ ≤ (d.radius : ℝ)+e.radius :=
  (norm_sub_le _ _).trans (add_le_add (norm_clockedItoDrift_le d c h T hT _ ω)
    (norm_clockedItoDrift_le e v h T hT _ ω))

theorem clockedItoState_sub_equation (t : ℝ≥0) (ω : BrownianSample) :
    clockedItoState d c h T hT t ω-clockedItoState e v h T hT t ω =
      (timeChangedBrownian (rateClock c) t ω-timeChangedBrownian (rateClock v) t ω)+
      ∫ s in 0..(t : ℝ),clockedDriftDifference d e c v h T hT s ω := by
  have hid : IntervalIntegrable (fun s => clockedItoDrift d c h T hT s.toNNReal ω) volume 0 t :=
    (intervalIntegrable_const (c := (d.radius : ℝ))).mono_fun'
      ((measurable_clockedItoDrift d c h T hT).comp
        (measurable_real_toNNReal.prodMk measurable_const)).aestronglyMeasurable
      (.of_forall fun s => norm_clockedItoDrift_le d c h T hT s.toNNReal ω)
  have hie : IntervalIntegrable (fun s => clockedItoDrift e v h T hT s.toNNReal ω) volume 0 t :=
    (intervalIntegrable_const (c := (e.radius : ℝ))).mono_fun'
      ((measurable_clockedItoDrift e v h T hT).comp
        (measurable_real_toNNReal.prodMk measurable_const)).aestronglyMeasurable
      (.of_forall fun s => norm_clockedItoDrift_le e v h T hT s.toNNReal ω)
  rw [clockedItoState_decomposition d c h T hT t ω,
    clockedItoState_decomposition e v h T hT t ω,
    clockedItoState_zero,clockedItoState_zero]
  unfold clockedDriftDifference integratedDrift
  rw [intervalIntegral.integral_sub hid hie,integral_Icc_eq_integral_Ioc,
    integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le t.coe_nonneg,
    ← intervalIntegral.integral_of_le t.coe_nonneg]
  ring

theorem integrable_clockedDriftDifference_primitive_square (t : ℝ≥0) :
    Integrable (fun ω => (∫ s in 0..(t : ℝ),clockedDriftDifference d e c v h T hT s ω)^2)
      canonicalBrownianMeasure := by
  let μ := fun s ω => clockedItoDrift d c h T hT s ω-clockedItoDrift e v h T hT s ω
  have hm : Measurable (Function.uncurry μ) :=
    (measurable_clockedItoDrift d c h T hT).sub (measurable_clockedItoDrift e v h T hT)
  have hb (s : ℝ≥0) (ω : BrownianSample) : ‖μ s ω‖ ≤ (d.radius+e.radius : ℝ≥0) := by
    simpa [μ,clockedDriftDifference] using norm_clockedDriftDifference_le d e c v h T hT s ω
  have hi : MemLp (integratedDrift μ t) 2 canonicalBrownianMeasure :=
    .of_bound (stronglyMeasurable_integratedDrift hm t).aestronglyMeasurable
      (((d.radius+e.radius : ℝ≥0) : ℝ)*(t : ℝ)) (.of_forall fun ω =>
        norm_integratedDrift_le_of_bound (d.radius+e.radius) hb t ω)
  have he : integratedDrift μ t = fun ω =>
      ∫ s in 0..(t : ℝ),clockedDriftDifference d e c v h T hT s ω := by
    funext ω
    rw [integratedDrift,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le t.coe_nonneg]
    rfl
  rw [he] at hi
  exact hi.integrable_sq

theorem clockedItoState_sub_square_le_integral (t : ℝ≥0) :
    (∫ ω,(clockedItoState d c h T hT t ω-clockedItoState e v h T hT t ω)^2
      ∂canonicalBrownianMeasure) ≤
      2*dist (rateClock c t) (rateClock v t)+
      2*(t : ℝ)*(∫ s in 0..(t : ℝ),∫ ω,(clockedDriftDifference d e c v h T hT s ω)^2
        ∂canonicalBrownianMeasure) := by
  have hiX := ((memLp_clockedItoState d c h T hT t).sub
    (memLp_clockedItoState e v h T hT t)).integrable_sq
  have hiW := integrable_timeChangedBrownian_increment_square (rateClock c) (rateClock v) t t
  have hiD := integrable_clockedDriftDifference_primitive_square d e c v h T hT t
  have hh := integral_mono hiX ((hiW.const_mul 2).add (hiD.const_mul 2)) (fun ω => by
    simp only [Pi.sub_apply,Pi.add_apply]
    rw [clockedItoState_sub_equation d e c v h T hT t ω]
    nlinarith only [sq_nonneg ((timeChangedBrownian (rateClock c) t ω-timeChangedBrownian (rateClock v) t ω)-
      (∫ s in 0..(t : ℝ),clockedDriftDifference d e c v h T hT s ω))])
  change (∫ ω,(clockedItoState d c h T hT t ω-clockedItoState e v h T hT t ω)^2
      ∂canonicalBrownianMeasure) ≤
      (∫ ω,2*(timeChangedBrownian (rateClock c) t ω-timeChangedBrownian (rateClock v) t ω)^2+
        2*(∫ s in 0..(t : ℝ),clockedDriftDifference d e c v h T hT s ω)^2 ∂canonicalBrownianMeasure) at hh
  rw [integral_add (hiW.const_mul 2) (hiD.const_mul 2),integral_const_mul,integral_const_mul,
    timeChangedBrownian_increment_square] at hh
  have hb := mean_square_interval_integral_le (P := canonicalBrownianMeasure)
    (clockedDriftDifference d e c v h T hT) (measurable_clockedDriftDifference d e c v h T hT)
    t.coe_nonneg (norm_clockedDriftDifference_le d e c v h T hT)
  calc
    _ ≤ _ := hh
    _ ≤ _ := by nlinarith only [hb]

theorem continuous_clocked_state_difference_square :
    Continuous (fun s : ℝ => ∫ ω,(clockedItoState d c h T hT s.toNNReal ω-
      clockedItoState e v h T hT s.toNNReal ω)^2 ∂canonicalBrownianMeasure) := by
  have he : (fun s : ℝ => ∫ ω,(clockedItoState d c h T hT s.toNNReal ω-
      clockedItoState e v h T hT s.toNNReal ω)^2 ∂canonicalBrownianMeasure) =
      fun s => ‖clockedStateLp d c h T hT s.toNNReal-clockedStateLp e v h T hT s.toNNReal‖^2 := by
    funext s
    exact (norm_sq_sub_toLp _ _ (memLp_clockedItoState d c h T hT s.toNNReal)
      (memLp_clockedItoState e v h T hT s.toNNReal)).symm
  rw [he]
  exact (((continuous_clockedStateLp d c h T hT).comp continuous_real_toNNReal).sub
    ((continuous_clockedStateLp e v h T hT).comp continuous_real_toNNReal)).norm.pow 2

end Coupled
end FourPapersCommon
