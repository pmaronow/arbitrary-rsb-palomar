module

public import FourPapersCommon.L2IntegralBounds
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section


/-! Genuine Cauchy--Schwarz and Fubini estimates for bounded random drifts. -/
noncomputable section
open Set MeasureTheory
namespace FourPapersCommon
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem interval_integral_square_le (f : ℝ → ℝ) (hm : Measurable f)
    {D t : ℝ} (ht : 0 ≤ t) (hb : ∀ s, ‖f s‖ ≤ D) :
    (∫ s in 0..t,f s)^2 ≤ t*(∫ s in 0..t,(f s)^2) := by
  let μ := volume.restrict (Ioc (0 : ℝ) t)
  haveI : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  have hf : MemLp f 2 μ := .of_bound hm.aestronglyMeasurable D (.of_forall hb)
  have hh := integral_sq_le_mass_mul_integral_sq f hf
  rw [intervalIntegral.integral_of_le ht,intervalIntegral.integral_of_le ht]
  have he : μ.real univ = t := by
    simp only [μ,Measure.real,Measure.restrict_apply_univ]
    rw [Real.volume_Ioc,ENNReal.toReal_ofReal (by linarith)]
    simp
  simpa only [he] using hh

theorem integrable_bounded_random_drift_square (f : ℝ → Ω → ℝ)
    (hm : Measurable (Function.uncurry f)) {D t : ℝ}
    (hb : ∀ s ω, ‖f s ω‖ ≤ D) :
    Integrable (fun z : ℝ × Ω => (f z.1 z.2)^2) ((volume.restrict (uIoc 0 t)).prod P) := by
  haveI : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) t)) := by
    rw [uIoc]
    infer_instance
  apply (integrable_const (D^2)).mono' (hm.pow_const 2).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  have hD : 0 ≤ D := (norm_nonneg (f z.1 z.2)).trans (hb z.1 z.2)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  change (f z.1 z.2)^2 ≤ D^2
  have hh := (sq_le_sq₀ (norm_nonneg _) hD).mpr (hb z.1 z.2)
  simpa only [Real.norm_eq_abs,sq_abs] using hh

theorem mean_square_interval_integral_le (f : ℝ → Ω → ℝ)
    (hm : Measurable (Function.uncurry f)) {D t : ℝ} (ht : 0 ≤ t)
    (hb : ∀ s ω, ‖f s ω‖ ≤ D) :
    (∫ ω,(∫ s in 0..t,f s ω)^2 ∂P) ≤
      t*(∫ s in 0..t,∫ ω,(f s ω)^2 ∂P) := by
  have hi := integrable_bounded_random_drift_square (P := P) f hm hb (t := t)
  have his : Integrable (fun ω => ∫ s in 0..t,(f s ω)^2) P := by
    simp_rw [intervalIntegral.integral_of_le ht]
    rw [uIoc_of_le ht] at hi
    exact hi.integral_prod_right
  have him : Measurable (fun ω => ∫ s in 0..t,f s ω) := by
    simp_rw [intervalIntegral.integral_of_le ht]
    exact (hm.stronglyMeasurable.integral_prod_left
      (μ := volume.restrict (Ioc (0 : ℝ) t))).measurable
  have hib : Integrable (fun ω => (∫ s in 0..t,f s ω)^2) P := by
    apply (integrable_const ((D*t)^2)).mono' (him.pow_const 2).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ω
    have hD : 0 ≤ D := (norm_nonneg (f 0 ω)).trans (hb 0 ω)
    have hn := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := t)
      (fun s _ => hb s ω)
    simp only [sub_zero,abs_of_nonneg ht] at hn
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hh := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hD ht)).mpr hn
    simpa only [Real.norm_eq_abs,sq_abs] using hh
  have hh := integral_mono hib (his.const_mul t) (fun ω =>
    interval_integral_square_le (fun s => f s ω)
      (hm.comp (measurable_id.prodMk measurable_const)) ht (fun s => hb s ω))
  change (∫ ω,(∫ s in 0..t,f s ω)^2 ∂P) ≤ (∫ ω,t*(∫ s in 0..t,(f s ω)^2) ∂P) at hh
  rw [integral_const_mul,← intervalIntegral_integral_swap hi] at hh
  exact hh

end FourPapersCommon
