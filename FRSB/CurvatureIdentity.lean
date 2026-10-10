module

public import FRSB.CurvatureGrid
public import FRSB.ParisiGridTopology
public import FRSB.JetMomentContinuity

@[expose] public section


/-! Actual arbitrary-measure curvature-square evolution, obtained by the
finite-cell centered Itô estimate, endpoint closure, grid telescoping and weak
approximation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper
open scoped Topology NNReal
namespace FRSB

theorem fixedStateJetPower_self_physical (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (j p : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    fixedStateJetPower β hβ μ μ j p t =
      ∫ω,jetProcess β μ (j+1) t ω ^ p ∂canonicalBrownianMeasure := by
  unfold fixedStateJetPower
  apply integral_congr_ae
  exact .of_forall fun ω => by
    dsimp only
    rw [selectedParisiItoState_eq β 0 hβ μ
      (by simpa only [Real.coe_toNNReal _ ht.1] using ht.2),Real.coe_toNNReal _ ht.1]
    rfl

theorem curvatureMoment2_tail_integral (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    curvatureMoment2 β μ 1-curvatureMoment2 β μ s =
      ∫t in s..1,curvatureEvolutionSource β hβ μ μ t := by
  have hF (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      Tendsto (fun n => gridCurvatureMoment β hβ μ n t) atTop
        (nhds (curvatureMoment2 β μ t)) := by
    have hh := tendsto_fixedStateJetPower_of_weak β hβ μ μ (parisiGridMeasure μ)
      (tendsto_parisiGridMeasure μ) 1 2 t
    rw [fixedStateJetPower_self_physical β hβ μ 1 2 ht] at hh
    exact hh
  have hS := tendsto_curvatureEvolutionSource_integral_of_weak β hβ μ μ
    (parisiGridMeasure μ) (tendsto_parisiGridMeasure μ) s 1
  have hleft := ((hF 1 ⟨by norm_num,le_rfl⟩).sub (hF s hs)).sub hS |>.norm
  have hright : Tendsto (fun n => 2*β^2*((1+uniformSpatialConstant β 2)*
      parisiCDFDistance μ (parisiGridMeasure μ n)+uniformSpatialConstant β 2*
        parisiHJBGradientError β μ n)) atTop (nhds 0) := by
    simpa only [mul_zero,zero_add] using
      (((tendsto_parisiCDFDistance_grid μ).const_mul (1+uniformSpatialConstant β 2)).add
        ((tendsto_parisiHJBGradientError β hβ μ).const_mul (uniformSpatialConstant β 2))).const_mul
          (2*β^2)
  have hh := le_of_tendsto_of_tendsto hleft hright
    (.of_forall fun n => gridCurvature_tail_remainder_le β hβ μ n hs)
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))

theorem curvatureMoment2_interval_integral (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    {r t : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    curvatureMoment2 β μ t-curvatureMoment2 β μ r =
      ∫s in r..t,curvatureEvolutionSource β hβ μ μ s := by
  have hR := curvatureMoment2_tail_integral β hβ μ hr
  have hT := curvatureMoment2_tail_integral β hβ μ ht
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (curvatureEvolutionSource_intervalIntegrable β hβ μ μ r t)
    (curvatureEvolutionSource_intervalIntegrable β hβ μ μ t 1)
  linarith

theorem curvatureMoment2_integral (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    curvatureMoment2 β μ t = curvatureMoment2 β μ 0+
      ∫s in 0..t,curvatureEvolutionSource β hβ μ μ s := by
  have hh := curvatureMoment2_interval_integral β hβ μ ⟨le_rfl,by norm_num⟩ ht
  linarith

theorem curvatureEvolutionSource_self_physical (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    curvatureEvolutionSource β hβ μ μ t =
      β^2*∫ω,D β μ t ω ^ 2-2*parisiCDF μ t*C β μ t ω ^ 3 ∂canonicalBrownianMeasure := by
  unfold curvatureEvolutionSource
  rw [fixedStateJetPower_self_physical β hβ μ 2 2 ht,
    fixedStateJetPower_self_physical β hβ μ 1 3 ht,
    integral_sub (integrable_jetProcess_pow β hβ μ 2 2 ht)
      ((integrable_jetProcess_pow β hβ μ 1 3 ht).const_mul (2*parisiCDF μ t)),integral_const_mul]

theorem GammaPrime_interval_integral (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    {r t : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hrt : r ≤ t) :
    GammaPrime β μ t-GammaPrime β μ r =
      β^4*∫s in r..t,∫ω,D β μ s ω ^ 2-2*parisiCDF μ s*C β μ s ω ^ 3
        ∂canonicalBrownianMeasure := by
  unfold GammaPrime
  rw [← mul_sub,curvatureMoment2_interval_integral β hβ μ hr ht]
  have he : (∫s in r..t,curvatureEvolutionSource β hβ μ μ s) =
      β^2*∫s in r..t,∫ω,D β μ s ω ^ 2-2*parisiCDF μ s*C β μ s ω ^ 3
        ∂canonicalBrownianMeasure := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le hrt
    intro s hs
    exact curvatureEvolutionSource_self_physical β hβ μ ⟨hr.1.trans hs.1.le,hs.2.le.trans ht.2⟩
  rw [he]
  ring

theorem hasDerivAt_curvatureMoment2_of_continuousAt_CDF (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hCDF : ContinuousAt (parisiCDF μ) t) :
    HasDerivAt (curvatureMoment2 β μ) (curvatureEvolutionSource β hβ μ μ t) t := by
  have hc : ContinuousAt (curvatureEvolutionSource β hβ μ μ) t :=
    continuousAt_const.mul (((continuous_fixedStateJetPower β hβ μ μ 2 2).continuousAt).sub
      ((continuousAt_const.mul hCDF).mul
        (continuous_fixedStateJetPower β hβ μ μ 1 3).continuousAt))
  have hd := (intervalIntegral.integral_hasDerivAt_right
    (curvatureEvolutionSource_intervalIntegrable β hβ μ μ 0 t)
    (measurable_curvatureEvolutionSource β hβ μ μ).aestronglyMeasurable.stronglyMeasurableAtFilter hc).const_add
      (curvatureMoment2 β μ 0)
  have he : curvatureMoment2 β μ =ᶠ[nhds t] fun r => curvatureMoment2 β μ 0+
      ∫s in 0..r,curvatureEvolutionSource β hβ μ μ s := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    exact curvatureMoment2_integral β hβ μ ⟨hr.1.le,hr.2.le⟩
  exact hd.congr_of_eventuallyEq he

theorem hasDerivAt_GammaPrime_of_continuousAt_CDF (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hCDF : ContinuousAt (parisiCDF μ) t) :
    HasDerivAt (GammaPrime β μ)
      (β^4*∫ω,D β μ t ω ^ 2-2*parisiCDF μ t*C β μ t ω ^ 3 ∂canonicalBrownianMeasure) t := by
  have hh := (hasDerivAt_curvatureMoment2_of_continuousAt_CDF β hβ μ ht hCDF).const_mul (β^2)
  rw [curvatureEvolutionSource_self_physical β hβ μ ⟨ht.1.le,ht.2.le⟩] at hh
  unfold GammaPrime
  convert hh using 1
  ring

end FRSB
