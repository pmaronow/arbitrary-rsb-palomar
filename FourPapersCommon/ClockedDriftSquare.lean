module

public import FourPapersCommon.ClockedDriftComparison
public import FourPapersCommon.ClockedDifferenceIntegral

@[expose] public section


/-! Genuine expected squared drift comparison, with the actual coefficient
error retained under time integration. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus
open scoped Topology NNReal ENNReal
namespace FourPapersCommon
open Paper

theorem intervalIntegrable_driftDiscrepancy_square (d e : AdditiveDriftData) {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 ≤ ε) (a b : ℝ) :
    IntervalIntegrable (fun s => (driftDiscrepancy d e R ε s)^2) volume a b := by
  apply (intervalIntegrable_const (c := ((d.radius : ℝ)+e.radius+R*ε)^2)).mono_fun'
    ((measurable_driftDiscrepancy d e R ε).pow_const 2).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro s
  dsimp only
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hh := (sq_le_sq₀ (norm_nonneg _) (by positivity :
    0 ≤ (d.radius : ℝ)+e.radius+R*ε)).mpr (driftDiscrepancy_bound d e hR hε s)
  simpa only [Real.norm_eq_abs,sq_abs] using hh

theorem integrable_clockedDriftDifference_square (d e : AdditiveDriftData)
    (c v : NonnegativeRate) (h T : ℝ) (hT : 0 ≤ T) (s : ℝ) :
    Integrable (fun ω => (clockedDriftDifference d e c v h T hT s ω)^2) canonicalBrownianMeasure := by
  have hi : MemLp (clockedDriftDifference d e c v h T hT s) 2 canonicalBrownianMeasure :=
    .of_bound ((measurable_clockedDriftDifference d e c v h T hT).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      ((d.radius : ℝ)+e.radius) (.of_forall (norm_clockedDriftDifference_le d e c v h T hT s))
  exact hi.integrable_sq

theorem intervalIntegrable_clockedDriftDifference_square_mean (d e : AdditiveDriftData)
    (c v : NonnegativeRate) (h T : ℝ) (hT : 0 ≤ T) (a b : ℝ) :
    IntervalIntegrable (fun s => ∫ ω,(clockedDriftDifference d e c v h T hT s ω)^2
      ∂canonicalBrownianMeasure) volume a b := by
  have hm : Measurable (fun s => ∫ ω,(clockedDriftDifference d e c v h T hT s ω)^2
      ∂canonicalBrownianMeasure) :=
    (((measurable_clockedDriftDifference d e c v h T hT).pow_const 2).stronglyMeasurable.integral_prod_right).measurable
  apply (intervalIntegrable_const (c := ((d.radius : ℝ)+e.radius)^2)).mono_fun' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro s
  dsimp only
  rw [Real.norm_of_nonneg (integral_nonneg (fun ω => sq_nonneg _))]
  calc
    _ ≤ ∫ _ : BrownianSample, ((d.radius : ℝ)+e.radius)^2 ∂canonicalBrownianMeasure :=
      integral_mono (integrable_clockedDriftDifference_square d e c v h T hT s) (integrable_const _) (fun ω => by
        have hh := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ (d.radius : ℝ)+e.radius)).mpr
          (norm_clockedDriftDifference_le d e c v h T hT s ω)
        simpa only [Real.norm_eq_abs,sq_abs] using hh)
    _ = _ := by simp

theorem clockedDriftDifference_square_mean_le (d e : AdditiveDriftData)
    (c v : NonnegativeRate) (h T : ℝ) (hT : 0 ≤ T) {R L ε : ℝ}
    (hR : 0 ≤ R) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (heR : (e.radius : ℝ) ≤ R) (heL : (e.gradientLip : ℝ) ≤ L)
    (hgrad : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖d.gradient t x-e.gradient t x‖ ≤ ε)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    (∫ ω,(clockedDriftDifference d e c v h T hT s ω)^2 ∂canonicalBrownianMeasure) ≤
      2*(R*L)^2*(∫ ω,(clockedItoState d c h T hT s.toNNReal ω-
        clockedItoState e v h T hT s.toNNReal ω)^2 ∂canonicalBrownianMeasure)+
      2*(driftDiscrepancy d e R ε s)^2 := by
  let X := fun ω => clockedItoState d c h T hT s.toNNReal ω-clockedItoState e v h T hT s.toNNReal ω
  have hiX : Integrable (fun ω => (X ω)^2) canonicalBrownianMeasure :=
    ((memLp_clockedItoState d c h T hT s.toNNReal).sub
      (memLp_clockedItoState e v h T hT s.toNNReal)).integrable_sq
  have hp (ω : BrownianSample) : (clockedDriftDifference d e c v h T hT s ω)^2 ≤
      2*(R*L)^2*(X ω)^2+2*(driftDiscrepancy d e R ε s)^2 := by
    have hn := clockedItoDrift_sub_le d e c v h T hT hR hL hε heR heL hgrad
      s.toNNReal (by simpa only [Real.coe_toNNReal s hs.1] using hs.2) ω
    simp only [Real.coe_toNNReal s hs.1] at hn
    change ‖clockedDriftDifference d e c v h T hT s ω‖ ≤ R*L*‖X ω‖+driftDiscrepancy d e R ε s at hn
    have ha := driftDiscrepancy_nonneg d e hR hε s
    have hh := (sq_le_sq₀ (norm_nonneg _) (add_nonneg
      (mul_nonneg (mul_nonneg hR hL) (norm_nonneg _)) ha)).mpr hn
    rw [Real.norm_eq_abs,sq_abs] at hh
    have he : (R*L*‖X ω‖)^2 = (R*L)^2*(X ω)^2 := by
      rw [mul_pow,Real.norm_eq_abs,sq_abs]
    nlinarith only [hh,he,sq_nonneg (R*L*‖X ω‖-driftDiscrepancy d e R ε s)]
  have hh := integral_mono (integrable_clockedDriftDifference_square d e c v h T hT s)
    ((hiX.const_mul (2*(R*L)^2)).add (integrable_const (2*(driftDiscrepancy d e R ε s)^2))) hp
  change (∫ ω,(clockedDriftDifference d e c v h T hT s ω)^2 ∂canonicalBrownianMeasure) ≤
    (∫ ω,2*(R*L)^2*(X ω)^2+2*(driftDiscrepancy d e R ε s)^2 ∂canonicalBrownianMeasure) at hh
  rw [integral_add (hiX.const_mul (2*(R*L)^2)) (integrable_const _),integral_const_mul,integral_const] at hh
  simpa only [probReal_univ,one_smul] using hh

end FourPapersCommon
