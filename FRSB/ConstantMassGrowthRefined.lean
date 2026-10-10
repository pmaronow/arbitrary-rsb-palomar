module

public import FRSB.ConstantMassGrowth
public import Paper.ParisiControlConvexity
public import Mathlib.Analysis.Convex.Integral

@[expose] public section


/-! Exact lower/upper log-cosh growth bounds for the actual selected
arbitrary-measure potential, refining the absolute Gaussian envelope. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper Filter
open scoped NNReal
namespace FRSB

lemma integral_logCosh_gaussianReal_ge (x : ℝ) (v : ℝ≥0) :
    Real.log (Real.cosh x) ≤ ∫ y, Real.log (Real.cosh y) ∂gaussianReal x v := by
  have hg : ColeHopfFoundation.ProbabilityTheory.HasLinearGrowth
      (fun y : ℝ => Real.log (Real.cosh y)) := ⟨0,1,zero_le_one,fun y => by
        simpa only [zero_add, one_mul, Real.norm_eq_abs] using norm_logcosh_le_abs y⟩
  have hi : Integrable (fun y : ℝ => y) (gaussianReal x v) := by
    have hid : ColeHopfFoundation.ProbabilityTheory.HasLinearGrowth (fun y : ℝ => y) :=
      ⟨0,1,zero_le_one,by intro y; simp only [Real.norm_eq_abs,zero_add,one_mul,le_refl]⟩
    exact hid.toHasExpGrowth.integrable_gaussianReal (by fun_prop)
  have hilog : Integrable (fun y : ℝ => Real.log (Real.cosh y)) (gaussianReal x v) :=
    hg.toHasExpGrowth.integrable_gaussianReal
    (((Real.continuous_cosh).log (fun y => (Real.cosh_pos y).ne')).aestronglyMeasurable)
  have hh := strictConvexOn_logCosh.convexOn.map_integral_le
    (((Real.continuous_cosh).log (fun y => (Real.cosh_pos y).ne')).continuousOn)
    isClosed_univ (Eventually.of_forall fun y => mem_univ y) hi hilog
  simpa only [Function.comp_def, integral_id_gaussianReal] using hh

lemma heatLogCosh_ge (ell x : ℝ) (hell : 0 ≤ ell) :
    Real.log (Real.cosh x) ≤ heatSemigroup ell (fun y => Real.log (Real.cosh y)) x := by
  have hm : (gaussianReal 0 1).map (fun z => x + Real.sqrt ell * z) = gaussianReal x ell.toNNReal := by
    rw [show (fun z : ℝ => x + Real.sqrt ell * z) =
      (fun z => x + z) ∘ (fun z => Real.sqrt ell * z) by rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
      gaussianReal_map_const_add]
    congr 1
    · simp
    · ext
      simp [Real.sq_sqrt hell, Real.toNNReal_of_nonneg hell]
  have hi := integral_logCosh_gaussianReal_ge x ell.toNNReal
  rw [← hm, integral_map (by fun_prop)
    ((Real.continuous_cosh).log (fun y => (Real.cosh_pos y).ne')).aestronglyMeasurable] at hi
  exact hi

lemma parisiDuhamelCorrection_nonneg (β : ℝ) (μ : ParisiMeasure) (t x : ℝ) (ht : t ≤ 1) :
    0 ≤ parisiDuhamelCorrection β μ (parisiGradient β μ) 1 t x := by
  unfold parisiDuhamelCorrection
  apply mul_nonneg (by positivity)
  apply intervalIntegral.integral_nonneg ht
  intro r hr
  unfold parisiHeatSource
  exact mul_nonneg (parisiCDF_nonneg μ r) (integral_nonneg (fun _ => sq_nonneg _))

/-- The paper's full displayed potential-growth estimate holds for the
actual arbitrary-measure solution, including both time endpoints. -/
theorem parisiPotential_logCosh_bounds (β : ℝ) (μ : ParisiMeasure) (t x : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    Real.log (Real.cosh x) ≤ parisiPotential β μ (t,x) ∧
    parisiPotential β μ (t,x) ≤ Real.log (Real.cosh x) + β ^ 2 * (1 - t) := by
  have hell : 0 ≤ β ^ 2 * (1 - t) := mul_nonneg (sq_nonneg β) (sub_nonneg.mpr ht.2)
  have hl := heatLogCosh_ge (β ^ 2 * (1 - t)) x hell
  have hu := heatLogCosh_le (β ^ 2 * (1 - t)) x hell
  have hc0 := parisiDuhamelCorrection_nonneg β μ t x ht.2
  have hc := norm_parisiDuhamelCorrection_le β μ (parisiGradient β μ) 1
    (norm_parisiGradient_le_one β μ) 1 t x ht.2
  have hc' := (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, one_pow, mul_one] using hc)
  rw [parisiPotential_eq_duhamel β μ t x ht.2]
  unfold parisiDuhamelPotential
  constructor <;> linarith

lemma lipschitzWith_parisiPotential_spatial (β : ℝ) (μ : ParisiMeasure)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    LipschitzWith 1 (fun x => parisiPotential β μ (t,x)) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun x => (hasDerivAt_parisiPotential_spatial_all β μ t x ht).differentiableAt)
  intro x
  rw [(hasDerivAt_parisiPotential_spatial_all β μ t x ht).deriv]
  exact_mod_cast norm_parisiGradient_le_one β μ (t,x)

/-- The exact linear-growth display normalized at the spatial origin. -/
theorem parisiPotential_origin_growth (β : ℝ) (μ : ParisiMeasure) (t x : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ parisiPotential β μ (t,x) - parisiPotential β μ (t,0) ∧
    parisiPotential β μ (t,x) - parisiPotential β μ (t,0) ≤ |x| := by
  have habs : |parisiPotential β μ (t,x) - parisiPotential β μ (t,0)| ≤ |x| := by
    simpa only [Real.norm_eq_abs, NNReal.coe_one, one_mul, sub_zero] using
      (lipschitzWith_parisiPotential_spatial β μ t ht).norm_sub_le x 0
  refine ⟨?_, (le_abs_self _).trans habs⟩
  by_cases hβ : β = 0
  · subst β
    simpa only [parisiPotential_zero, Real.cosh_zero, Real.log_one, sub_zero] using logCosh_nonneg x
  · have hmono : MonotoneOn (fun y => parisiPotential β μ (t,y)) (Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
        ((contDiff_parisiPotential_spatial β μ t ht).continuous.continuousOn)
        (fun y _ => (hasDerivAt_parisiPotential_spatial_all β μ t y ht).differentiableAt.differentiableWithinAt)
      intro y hy
      rw [(hasDerivAt_parisiPotential_spatial_all β μ t y ht).deriv]
      have hy0 : 0 ≤ y := interior_subset hy
      have hh := (parisiGradient_strictMono β hβ μ t ht).monotone hy0
      rw [parisiGradient_at_zero β hβ μ t ht] at hh
      exact hh
    by_cases hx : 0 ≤ x
    · exact sub_nonneg.mpr (hmono (by norm_num) hx hx)
    · have hn : 0 ≤ -x := by linarith
      have hh := hmono (by norm_num) hn hn
      change parisiPotential β μ (t,0) ≤ parisiPotential β μ (t,-x) at hh
      rw [parisiPotential_even β μ t x ht] at hh
      exact sub_nonneg.mpr hh

end FRSB
