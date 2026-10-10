module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

@[expose] public section


/-! The actual one-spin entropy penalty log(1+exp(-x)), including its Jensen
bound under a genuine probability law. -/
noncomputable section
open Set MeasureTheory
namespace FourPapersCommon

def entropyPenalty (x : ℝ) : ℝ := Real.log (1+Real.exp (-x))

theorem entropyPenalty_pos (x : ℝ) : 0 < entropyPenalty x :=
  Real.log_pos (by linarith [Real.exp_pos (-x)])

theorem hasDerivAt_entropyPenalty (x : ℝ) :
    HasDerivAt entropyPenalty (-Real.exp (-x)/(1+Real.exp (-x))) x := by
  have hh := (((hasDerivAt_id x).neg.exp).const_add 1).log
    (by positivity : (1+Real.exp (-x)) ≠ 0)
  unfold entropyPenalty
  simpa only [mul_neg_one,Pi.neg_apply,id_eq] using hh

theorem continuous_entropyPenalty : Continuous entropyPenalty :=
  (show Differentiable ℝ entropyPenalty from fun x => (hasDerivAt_entropyPenalty x).differentiableAt).continuous

theorem antitone_entropyPenalty : Antitone entropyPenalty :=
  antitone_of_hasDerivAt_nonpos hasDerivAt_entropyPenalty (fun x =>
    div_nonpos_of_nonpos_of_nonneg (by linarith [Real.exp_pos (-x)]) (by positivity))

theorem convexOn_entropyPenalty : ConvexOn ℝ univ entropyPenalty := by
  apply Monotone.convexOn_univ_of_deriv
    (fun x => (hasDerivAt_entropyPenalty x).differentiableAt)
  intro x y hxy
  rw [(hasDerivAt_entropyPenalty x).deriv,(hasDerivAt_entropyPenalty y).deriv]
  apply (div_le_div_iff₀ (by positivity : 0 < 1+Real.exp (-x))
    (by positivity : 0 < 1+Real.exp (-y))).mpr
  nlinarith only [Real.exp_le_exp.mpr (neg_le_neg hxy)]

theorem entropyPenalty_le_log_two_add_abs (x : ℝ) : entropyPenalty x ≤ Real.log 2+|x| := by
  have he : 1+Real.exp (-x) ≤ 2*Real.exp |x| := by
    have h1 : 1 ≤ Real.exp |x| := by simpa using Real.exp_le_exp.mpr (abs_nonneg x)
    have h2 : Real.exp (-x) ≤ Real.exp |x| := Real.exp_le_exp.mpr (neg_le_abs x)
    linarith
  have hh := Real.log_le_log (by positivity : 0 < 1+Real.exp (-x)) he
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero _),Real.log_exp] at hh
  exact hh

theorem integrable_entropyPenalty {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Integrable X P) :
    Integrable (fun ω => entropyPenalty (X ω)) P := by
  apply ((integrable_const (Real.log 2)).add hX.norm).mono'
    (continuous_entropyPenalty.comp_aestronglyMeasurable hX.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro ω
  simp only [Real.norm_eq_abs,abs_of_pos (entropyPenalty_pos (X ω))]
  exact entropyPenalty_le_log_two_add_abs (X ω)

theorem entropyPenalty_integral_ge_of_mean_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Integrable X P) {C : ℝ}
    (hmean : (∫ ω,X ω ∂P) ≤ C) :
    entropyPenalty C ≤ ∫ ω,entropyPenalty (X ω) ∂P := by
  have hh := convexOn_entropyPenalty.map_integral_le continuous_entropyPenalty.continuousOn
    isClosed_univ (.of_forall fun ω => mem_univ (X ω)) hX (integrable_entropyPenalty X hX)
  exact (antitone_entropyPenalty hmean).trans hh

end FourPapersCommon
