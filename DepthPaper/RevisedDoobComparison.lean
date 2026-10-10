module

public import DepthPaper.DoobEndpointIntegralBounds
public import Paper.RSFunctional
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-! The even monotone change of density in revision (16), Lemma C.2.
The association inequality is proved from independent copies. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open ColeHopfFoundation.ProbabilityTheory
open scoped NNReal ENNReal
namespace DepthPaper
set_option maxHeartbeats 900000

def revisedDoobOmega (m x : ℝ) : ℝ := coshPower m x / Real.cosh (m*x)

theorem revisedDoobOmega_pos (m x : ℝ) : 0 < revisedDoobOmega m x := by
  unfold revisedDoobOmega coshPower
  positivity

theorem revisedDoobOmega_even (m x : ℝ) : revisedDoobOmega m (-x) = revisedDoobOmega m x := by
  simp [revisedDoobOmega,coshPower,mul_neg]

theorem hasDerivAt_revisedDoobOmega (m x : ℝ) :
    HasDerivAt (revisedDoobOmega m)
      (m*(Real.tanh x-Real.tanh (m*x))*revisedDoobOmega m x) x := by
  have hn := ((Paper.hasDerivAt_log_cosh x).const_mul m).exp
  have hd := (Real.hasDerivAt_cosh (m*x)).comp x ((hasDerivAt_id x).const_mul m)
  convert hn.div hd (Real.cosh_pos (m*x)).ne' using 1
  · rfl
  · simp only [revisedDoobOmega,coshPower,Real.tanh_eq_sinh_div_cosh,
      Function.comp_apply,mul_one]
    field_simp [(Real.cosh_pos x).ne',(Real.cosh_pos (m*x)).ne']

theorem continuous_revisedDoobOmega (m : ℝ) : Continuous (revisedDoobOmega m) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_revisedDoobOmega m x).continuousAt

theorem revisedDoobOmega_monotoneOn {m : ℝ} (hm : 0 ≤ m) (hm1 : m ≤ 1) :
    MonotoneOn (revisedDoobOmega m) (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (continuous_revisedDoobOmega m).continuousOn
  · intro x _
    exact (hasDerivAt_revisedDoobOmega m x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(hasDerivAt_revisedDoobOmega m x).deriv]
    have hx0 : 0 ≤ x := (interior_subset hx : x ∈ Ici (0:ℝ))
    exact mul_nonneg (mul_nonneg hm (sub_nonneg.mpr
      (Paper.tanh_monotone (by nlinarith)))) (revisedDoobOmega_pos m x).le

theorem revisedDoobOmega_norm_le {m : ℝ} (hm : 0 ≤ m) (hm1 : m ≤ 1) (x : ℝ) :
    ‖revisedDoobOmega m x‖ ≤ 2 := by
  rw [Real.norm_eq_abs,abs_of_pos (revisedDoobOmega_pos m x)]
  unfold revisedDoobOmega
  apply (div_le_iff₀ (Real.cosh_pos (m*x))).mpr
  have hf : Real.exp (-m*Real.log 2) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hm)
      (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)))
  exact (coshPower_sum_upper hm hm1 x).trans (by
    nlinarith [mul_le_mul_of_nonneg_right hf (Real.cosh_pos (m*x)).le])

theorem revised_ordered_association {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {f g : ℝ→ℝ} (hf : Measurable f) (hg : Integrable g ρ)
    (B : ℝ) (hb : ∀x,‖f x‖≤B) {s : Set ℝ}
    (hfs : MonotoneOn f s) (hgs : MonotoneOn g s) (hs : ∀ᵐx∂ρ,x∈s) :
    (∫x,f x∂ρ)*(∫x,g x∂ρ) ≤ ∫x,f x*g x∂ρ := by
  have hif : Integrable f ρ := Integrable.of_bound hf.aestronglyMeasurable B (.of_forall hb)
  have hfg := hg.bdd_mul hf.aestronglyMeasurable (.of_forall hb)
  have hcross₁ := hif.mul_prod hg
  have hcross₂ := hg.mul_prod hif
  have hfg₁ := hfg.comp_fst ρ
  have hfg₂ := hfg.comp_snd ρ
  have he (p:ℝ×ℝ) : (f p.1-f p.2)*(g p.1-g p.2)=
      (f p.1*g p.1+f p.2*g p.2)-(f p.1*g p.2+g p.1*f p.2) := by ring
  have hnon : 0≤∫p:ℝ×ℝ,(f p.1-f p.2)*(g p.1-g p.2) ∂ρ.prod ρ := by
    apply integral_nonneg_of_ae
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hs,
      Measure.quasiMeasurePreserving_snd.ae hs] with p hp₁ hp₂
    rcases le_total p.1 p.2 with hle|hle
    · exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr (hfs hp₁ hp₂ hle)) (sub_nonpos.mpr (hgs hp₁ hp₂ hle))
    · exact mul_nonneg (sub_nonneg.mpr (hfs hp₂ hp₁ hle))
        (sub_nonneg.mpr (hgs hp₂ hp₁ hle))
  simp_rw [he] at hnon
  rw [integral_sub (f:=fun p:ℝ×ℝ=>f p.1*g p.1+f p.2*g p.2)
    (g:=fun p:ℝ×ℝ=>f p.1*g p.2+g p.1*f p.2)
    (hfg₁.add hfg₂) (hcross₁.add hcross₂),
    integral_add hfg₁ hfg₂,integral_add hcross₁ hcross₂,
    integral_fun_fst (μ:=ρ) (ν:=ρ) (fun x=>f x*g x),
    integral_fun_snd (μ:=ρ) (ν:=ρ) (fun x=>f x*g x),
    integral_prod_mul (μ:=ρ) (ν:=ρ) f g,
    integral_prod_mul (μ:=ρ) (ν:=ρ) g f] at hnon
  simp only [probReal_univ,one_smul] at hnon
  nlinarith

theorem revised_gaussianPDF_factor (x : ℝ) (V : ℝ≥0) (hV : V ≠ 0) (w : ℝ) :
    gaussianPDFReal x V w = gaussianPDFReal x V 0 *
      Real.exp (-w^2/(2*(V:ℝ))) * Real.exp (x*w/(V:ℝ)) := by
  have hvr : (V:ℝ) ≠ 0 := by exact_mod_cast hV
  have he : -(w-x)^2/(2*(V:ℝ)) =
      -(0-x)^2/(2*(V:ℝ)) + (-w^2/(2*(V:ℝ))) + x*w/(V:ℝ) := by
    field_simp
    ring
  unfold gaussianPDFReal
  rw [he,Real.exp_add,Real.exp_add]
  ring

theorem revised_gaussianPDF_pairing (x : ℝ) (V : ℝ≥0) (hV : V ≠ 0) (w : ℝ) :
    gaussianPDFReal x V w - gaussianPDFReal x V (-w) =
      Real.tanh (x*w/(V:ℝ)) * (gaussianPDFReal x V w + gaussianPDFReal x V (-w)) := by
  rw [revised_gaussianPDF_factor x V hV w,revised_gaussianPDF_factor x V hV (-w)]
  simp only [neg_sq,mul_neg,neg_div]
  have ht (a : ℝ) : Real.tanh a * (Real.exp a + Real.exp (-a)) =
      Real.exp a - Real.exp (-a) := by
    rw [Real.tanh_eq_sinh_div_cosh,Real.sinh_eq,Real.cosh_eq]
    field_simp
  linear_combination -(gaussianPDFReal x V 0 * Real.exp (-(w^2/(2*(V:ℝ))))) *
    ht (x*w/(V:ℝ))

/-- The literal integral form of the conditional-sign identity, proved by
Gaussian reflection. This avoids invoking an unconstructed conditional law. -/
theorem revised_gaussian_odd_pairing (x : ℝ) (V : ℝ≥0) (hV : V ≠ 0)
    (f : ℝ→ℝ) (hf : ∀w,f (-w) = -f w)
    (hi : Integrable (fun w=>gaussianPDFReal x V w*f w)) :
    (∫w,gaussianPDFReal x V w*f w) =
      ∫w,gaussianPDFReal x V w*f w*Real.tanh (x*w/(V:ℝ)) := by
  have ht : Measurable (fun w=>Real.tanh (x*w/(V:ℝ))) :=
    (continuous_iff_continuousAt.mpr fun t =>
      (Paper.hasDerivAt_tanh t).continuousAt).measurable.comp
        ((measurable_const.mul measurable_id).div_const _)
  have hi' := hi.mul_bdd ht.aestronglyMeasurable
    (.of_forall fun w => (by simpa only [Real.norm_eq_abs] using
      (Real.abs_tanh_lt_one (x*w/(V:ℝ))).le))
  have he (w : ℝ) : gaussianPDFReal x V w*f w + gaussianPDFReal x V (-w)*f (-w) =
      gaussianPDFReal x V w*f w*Real.tanh (x*w/(V:ℝ)) +
      gaussianPDFReal x V (-w)*f (-w)*Real.tanh (x*(-w)/(V:ℝ)) := by
    rw [hf]
    simp only [mul_neg,neg_div,Real.tanh_neg]
    linear_combination f w * revised_gaussianPDF_pairing x V hV w
  have heq := integral_congr_ae (μ:=volume) (.of_forall he)
  rw [integral_add hi hi.comp_neg,integral_add hi' hi'.comp_neg,
    integral_neg_eq_self (fun w=>gaussianPDFReal x V w*f w) volume,
    integral_neg_eq_self (fun w=>gaussianPDFReal x V w*f w*Real.tanh (x*w/(V:ℝ))) volume] at heq
  linarith


theorem revised_integrable_pdf_mul (x : ℝ) (V : ℝ≥0) (hV : V ≠ 0)
    {f : ℝ→ℝ} (hi : Integrable f (gaussianReal x V)) :
    Integrable (fun w=>gaussianPDFReal x V w*f w) := by
  rw [gaussianReal_of_var_ne_zero x hV] at hi
  have hh := (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF x V) (.of_forall fun w=>gaussianPDF_lt_top)).mp hi
  simpa only [toReal_gaussianPDF,smul_eq_mul] using hh

theorem revised_gaussian_expectation_odd_pairing (x : ℝ) (V : ℝ≥0) (hV : V ≠ 0)
    (f : ℝ→ℝ) (hf : ∀w,f (-w) = -f w) (hi : Integrable f (gaussianReal x V)) :
    (∫w,f w ∂gaussianReal x V) =
      ∫w,f w*Real.tanh (x*w/(V:ℝ)) ∂gaussianReal x V := by
  simp only [integral_gaussianReal_eq_integral_smul hV,smul_eq_mul]
  simp only [←mul_assoc]
  exact revised_gaussian_odd_pairing x V hV f hf (revised_integrable_pdf_mul x V hV hi)

theorem revised_radial_association {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {f g : ℝ→ℝ} (hf : Continuous f) (hg : Continuous g)
    (B C : ℝ) (hb : ∀x,‖f x‖≤B) (hc : ∀x,‖g x‖≤C)
    (hfe : ∀w,f (-w)=f w) (hge : ∀w,g (-w)=g w)
    (hfm : MonotoneOn f (Ici 0)) (hgm : MonotoneOn g (Ici 0)) :
    (∫x,f x∂ρ)*(∫x,g x∂ρ) ≤ ∫x,f x*g x∂ρ := by
  have hfi (w : ℝ) : f |w|=f w := by
    rcases le_total 0 w with h|h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h,hfe]
  have hgi (w : ℝ) : g |w|=g w := by
    rcases le_total 0 w with h|h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h,hge]
  have hs : ∀ᵐw∂ρ.map abs,w ∈ Ici (0:ℝ) :=
    (ae_map_iff measurable_abs.aemeasurable measurableSet_Ici).mpr
      (.of_forall abs_nonneg)
  have hga : Integrable g (ρ.map abs) := Integrable.of_bound hg.aestronglyMeasurable C
    (.of_forall hc)
  have hh := revised_ordered_association (ρ:=ρ.map abs) hf.measurable hga B hb hfm hgm hs
  rw [integral_map measurable_abs.aemeasurable hf.aestronglyMeasurable,
    integral_map measurable_abs.aemeasurable hg.aestronglyMeasurable,
    integral_map (f:=fun x=>f x*g x) measurable_abs.aemeasurable
      (show AEStronglyMeasurable (fun x=>f x*g x) (ρ.map abs) from
        (hf.mul hg).aestronglyMeasurable)] at hh
  simpa only [hfi,hgi] using hh

theorem continuous_revised_tanh : Continuous Real.tanh :=
  continuous_iff_continuousAt.mpr fun t=>(Paper.hasDerivAt_tanh t).continuousAt

def revisedTanhPair (m x : ℝ) (V : ℝ≥0) (w : ℝ) : ℝ :=
  Real.tanh (m*w)*Real.tanh (x*w/(V:ℝ))

theorem revisedTanhPair_monotoneOn {m x : ℝ} (hm : 0 ≤ m) (hx : 0 ≤ x) (V : ℝ≥0) :
    MonotoneOn (revisedTanhPair m x V) (Ici 0) := by
  intro a ha b hb hab
  have ht₁ := Paper.tanh_monotone (mul_le_mul_of_nonneg_left hab hm)
  have ht₂ := Paper.tanh_monotone (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hab hx) V.coe_nonneg)
  exact mul_le_mul ht₁ ht₂
    (Paper.tanh_nonneg (div_nonneg (mul_nonneg hx ha) V.coe_nonneg))
    (Paper.tanh_nonneg (mul_nonneg hm hb))


theorem revised_limiting_odd_pairing (m x : ℝ) (V : ℝ≥0) (hV : V ≠ 0)
    (f : ℝ→ℝ) (hf : Continuous f) (hodd : ∀w,f (-w) = -f w)
    (B : ℝ) (hb : ∀w,‖f w‖≤B) :
    (∫w,f w∂limitingDoobMeasure m V x) =
      ∫w,f w*Real.tanh (x*w/(V:ℝ))∂limitingDoobMeasure m V x := by
  rw [integral_limitingDoobMeasure,integral_limitingDoobMeasure]
  have hi := (integrable_limitingDoobWeight m V x).bdd_mul hf.aestronglyMeasurable
    (.of_forall hb)
  have ho (w:ℝ) : f (-w)*limitingDoobWeight m V x (-w) =
      -(f w*limitingDoobWeight m V x w) := by
    simp [hodd,limitingDoobWeight,mul_neg]
  have hh := revised_gaussian_expectation_odd_pairing x V hV
    (fun w=>f w*limitingDoobWeight m V x w) ho hi
  convert hh using 1
  congr 1
  funext w
  ring

theorem revised_integral_sinh_gaussian (m x : ℝ) (V : ℝ≥0) :
    (∫w,Real.sinh (m*w) ∂gaussianReal x V) =
      Real.exp ((V:ℝ)*m^2/2)*Real.sinh (m*x) := by
  have hp := integrable_exp_mul_gaussianReal (μ:=x) (v:=V) m
  have hn := integrable_exp_mul_gaussianReal (μ:=x) (v:=V) (-m)
  simp_rw [Real.sinh_eq]
  rw [integral_div,integral_sub hp (by simpa only [neg_mul] using hn)]
  have he (a:ℝ) : (∫w,Real.exp (a*w) ∂gaussianReal x V) =
      Real.exp (x*a+(V:ℝ)*a^2/2) := by
    simpa only [mgf,id_eq] using congrFun (mgf_id_gaussianReal (μ:=x) (v:=V)) a
  rw [he m]
  have hne : (∫w,Real.exp (-(m*w)) ∂gaussianReal x V) =
      Real.exp (-m*x+(V:ℝ)*m^2/2) := by
    simpa only [neg_mul,neg_sq,mul_neg,mul_comm x m] using he (-m)
  rw [hne,show x*m=m*x by ring,show -m*x=-(m*x) by ring]
  simp only [Real.exp_add]
  ring

theorem revised_limiting_tanh_expectation (m x : ℝ) (V : ℝ≥0) :
    (∫w,Real.tanh (m*w) ∂limitingDoobMeasure m V x)=Real.tanh (m*x) := by
  rw [integral_limitingDoobMeasure]
  have hew (w:ℝ) : Real.tanh (m*w)*limitingDoobWeight m V x w =
      (Real.exp (-m^2*(V:ℝ)/2)/Real.cosh (m*x))*Real.sinh (m*w) := by
    rw [Real.tanh_eq_sinh_div_cosh,limitingDoobWeight]
    field_simp
  simp_rw [hew]
  rw [integral_const_mul,revised_integral_sinh_gaussian,Real.tanh_eq_sinh_div_cosh]
  have he : Real.exp (-m^2*(V:ℝ)/2)*Real.exp ((V:ℝ)*m^2/2)=1 := by
    rw [←Real.exp_add,show -m^2*(V:ℝ)/2+(V:ℝ)*m^2/2=0 by ring,Real.exp_zero]
  field_simp
  have he' : Real.exp (-(m^2*(V:ℝ)/2))*Real.exp (m^2*(V:ℝ)/2)=1 := by
    rw [←Real.exp_add,neg_add_cancel,Real.exp_zero]
  linear_combination Real.sinh (m*x)*he'

theorem revised_omega_tanh_association {m x : ℝ} (hm : 0 ≤ m) (hm1 : m ≤ 1)
    (hx : 0 ≤ x) (V : ℝ≥0) (hV : V ≠ 0) :
    (∫w,revisedDoobOmega m w∂limitingDoobMeasure m V x)*Real.tanh (m*x) ≤
      ∫w,revisedDoobOmega m w*Real.tanh (m*w)∂limitingDoobMeasure m V x := by
  have := isProbabilityMeasure_limitingDoobMeasure m V x
  have htc : Continuous (fun w=>Real.tanh (m*w)) :=
    continuous_revised_tanh.comp (continuous_const.mul continuous_id)
  have hqc : Continuous (revisedTanhPair m x V) :=
    htc.mul (continuous_revised_tanh.comp
      ((continuous_const.mul continuous_id).div_const _))
  have htn (w:ℝ) : ‖Real.tanh (m*w)‖≤1 := by
    simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one (m*w)).le
  have hqn (w:ℝ) : ‖revisedTanhPair m x V w‖≤1 := by
    unfold revisedTanhPair
    rw [norm_mul]
    exact (mul_le_mul (htn w) (by simpa only [Real.norm_eq_abs] using
      (Real.abs_tanh_lt_one (x*w/(V:ℝ))).le) (norm_nonneg _) zero_le_one).trans_eq (by ring)
  have hoe (w:ℝ) : revisedDoobOmega m (-w)*Real.tanh (m*(-w)) =
      -(revisedDoobOmega m w*Real.tanh (m*w)) := by
    rw [revisedDoobOmega_even];simp
  have hon (w:ℝ) : ‖revisedDoobOmega m w*Real.tanh (m*w)‖≤2 := by
    rw [norm_mul]
    exact (mul_le_mul (revisedDoobOmega_norm_le hm hm1 w) (htn w)
      (norm_nonneg _) (by norm_num)).trans_eq (by ring)
  have hh := revised_radial_association (ρ:=limitingDoobMeasure m V x)
    (continuous_revisedDoobOmega m) hqc 2 1 (revisedDoobOmega_norm_le hm hm1) hqn
    (revisedDoobOmega_even m) (by intro w;simp [revisedTanhPair,neg_div])
    (revisedDoobOmega_monotoneOn hm hm1) (revisedTanhPair_monotoneOn hm hx V)
  have hg := revised_limiting_odd_pairing m x V hV (fun w=>Real.tanh (m*w))
    htc (by intro w;simp) 1 htn
  have hfg := revised_limiting_odd_pairing m x V hV
    (fun w=>revisedDoobOmega m w*Real.tanh (m*w))
    ((continuous_revisedDoobOmega m).mul htc) hoe 2 hon
  change (∫w,revisedDoobOmega m w∂limitingDoobMeasure m V x)*
    (∫w,Real.tanh (m*w)*Real.tanh (x*w/(V:ℝ))∂limitingDoobMeasure m V x) ≤
    ∫w,revisedDoobOmega m w*(Real.tanh (m*w)*Real.tanh (x*w/(V:ℝ)))
      ∂limitingDoobMeasure m V x at hh
  simp_rw [←mul_assoc] at hh
  rw [←hg,←hfg,revised_limiting_tanh_expectation] at hh
  exact hh


theorem revised_continuous_logCosh : Continuous (fun w:ℝ=>Real.log (Real.cosh w)) :=
  Real.continuous_cosh.log (fun w=>(Real.cosh_pos w).ne')

theorem revised_continuous_coshPower (m:ℝ) : Continuous (coshPower m) :=
  Real.continuous_exp.comp (continuous_const.mul revised_continuous_logCosh)

theorem revised_integrable_coshPower (m x : ℝ) (V : ℝ≥0) :
    Integrable (coshPower m) (gaussianReal x V) :=
  (hasLinearGrowth_logCosh.exp_mul m).integrable_gaussianReal
    ((revised_continuous_coshPower m).aestronglyMeasurable)

theorem revised_tanh_moment_lower {m x : ℝ} (hm : 0 ≤ m) (hm1 : m ≤ 1)
    (hx : 0 ≤ x) (V : ℝ≥0) (hV : V ≠ 0) :
    (∫w,coshPower m w∂gaussianReal x V)*Real.tanh (m*x) ≤
      ∫w,coshPower m w*Real.tanh (m*w)∂gaussianReal x V := by
  have hh := revised_omega_tanh_association hm hm1 hx V hV
  have hew (w:ℝ) : revisedDoobOmega m w*limitingDoobWeight m V x w =
      (Real.exp (-m^2*(V:ℝ)/2)/Real.cosh (m*x))*coshPower m w := by
    unfold revisedDoobOmega limitingDoobWeight
    field_simp
  rw [integral_limitingDoobMeasure,integral_limitingDoobMeasure] at hh
  have hew' (w:ℝ) : revisedDoobOmega m w*Real.tanh (m*w)*limitingDoobWeight m V x w =
      (Real.exp (-m^2*(V:ℝ)/2)/Real.cosh (m*x))*(coshPower m w*Real.tanh (m*w)) := by
    linear_combination Real.tanh (m*w)*hew w
  simp_rw [hew,hew'] at hh
  rw [integral_const_mul,integral_const_mul] at hh
  have hk : 0 < Real.exp (-m^2*(V:ℝ)/2)/Real.cosh (m*x) := by positivity
  exact (mul_le_mul_iff_right₀ hk).mp (by simpa only [mul_assoc] using hh)

theorem revised_tanh_moment_comparison {m x : ℝ} (_hm : 0 ≤ m) (hm1 : m ≤ 1)
    (hx : 0 ≤ x) (V : ℝ≥0) (hV : V ≠ 0) :
    (∫w,coshPower m w*Real.tanh (m*w)∂gaussianReal x V) ≤
      ∫w,coshPower m w*Real.tanh w∂gaussianReal x V := by
  have htc : Continuous Real.tanh := continuous_revised_tanh
  have hmc : Continuous (fun w=>Real.tanh (m*w)) := htc.comp (continuous_const.mul continuous_id)
  have hxc : Continuous (fun w=>Real.tanh (x*w/(V:ℝ))) :=
    htc.comp ((continuous_const.mul continuous_id).div_const _)
  have htn (a:ℝ) : ‖Real.tanh a‖≤1 := by
    simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one a).le
  have hi₁ := (revised_integrable_coshPower m x V).mul_bdd htc.aestronglyMeasurable
    (.of_forall htn)
  have hi₂ := (revised_integrable_coshPower m x V).mul_bdd hmc.aestronglyMeasurable
    (.of_forall fun w=>htn (m*w))
  have he₁ := revised_gaussian_expectation_odd_pairing x V hV
    (fun w=>coshPower m w*Real.tanh w) (by intro w;simp [coshPower]) hi₁
  have he₂ := revised_gaussian_expectation_odd_pairing x V hV
    (fun w=>coshPower m w*Real.tanh (m*w)) (by intro w;simp [coshPower]) hi₂
  rw [he₁,he₂]
  apply integral_mono (hi₂.mul_bdd hxc.aestronglyMeasurable (.of_forall fun w=>htn _))
    (hi₁.mul_bdd hxc.aestronglyMeasurable (.of_forall fun w=>htn _))
  intro w
  simp only [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by unfold coshPower;positivity)
  rcases le_total 0 w with hw|hw
  · exact mul_le_mul_of_nonneg_right (Paper.tanh_monotone (by nlinarith))
      (Paper.tanh_nonneg (div_nonneg (mul_nonneg hx hw) V.coe_nonneg))
  · exact mul_le_mul_of_nonpos_right (Paper.tanh_monotone (by nlinarith))
      (by have ht := Paper.tanh_monotone (div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos hx hw) V.coe_nonneg)
          simpa using ht)

theorem revised_coleHopf_derivative_ratio {m : ℝ} (hm : m ≠ 0) (V : ℝ≥0) (x : ℝ) :
    deriv (coleHopf m V (fun w=>Real.log (Real.cosh w))) x =
      (∫w,coshPower m w*Real.tanh w∂gaussianReal x V)/
        (∫w,coshPower m w∂gaussianReal x V) := by
  have htc : Measurable Real.tanh := continuous_revised_tanh.measurable
  have htg : HasLinearGrowth Real.tanh := ⟨1,0,le_rfl,fun w=>by
    simpa using (Real.abs_tanh_lt_one w).le⟩
  have hd := (hasDerivAt_coleHopf Paper.hasDerivAt_log_cosh hasLinearGrowth_logCosh htg.toHasExpGrowth htc hm V x).deriv
  rw [hd]
  have hz := integral_gaussianReal_eq_integral_comp_add (H:=coshPower m) x V
    (revised_continuous_coshPower m).aestronglyMeasurable
  have hn := integral_gaussianReal_eq_integral_comp_add (H:=fun w=>coshPower m w*Real.tanh w) x V
    ((revised_integrable_coshPower m x V).mul_bdd htc.aestronglyMeasurable
      (.of_forall fun w=>by simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one w).le)).aestronglyMeasurable
  rw [hn,hz,←integral_div]
  exact integral_congr_ae (.of_forall fun z=>by
    dsimp only
    rw [coleHopfQ_eq hasLinearGrowth_logCosh revised_continuous_logCosh.measurable hm]
    unfold coshPower
    ring)

theorem revised_coleHopf_derivative_lower_nonneg {m x : ℝ} (hm : 0 < m) (hm1 : m ≤ 1)
    (hx : 0 ≤ x) (V : ℝ≥0) :
    Real.tanh (m*x) ≤ deriv (coleHopf m V (fun w=>Real.log (Real.cosh w))) x := by
  by_cases hV : V=0
  · subst V
    have hfun : coleHopf m 0 (fun w=>Real.log (Real.cosh w)) =
        (fun w=>Real.log (Real.cosh w)) := funext (coleHopf_zero_var m _)
    rw [hfun]
    rw [(Paper.hasDerivAt_log_cosh x).deriv]
    exact Paper.tanh_monotone (by nlinarith)
  rw [revised_coleHopf_derivative_ratio hm.ne' V x]
  have hz : 0 < ∫w,coshPower m w∂gaussianReal x V := by
    rw [integral_gaussianReal_eq_integral_comp_add x V (revised_continuous_coshPower m).aestronglyMeasurable]
    exact integral_exp_mul_comp_add_pos hasLinearGrowth_logCosh revised_continuous_logCosh.measurable m V x
  apply (le_div_iff₀ hz).mpr
  exact (by simpa only [mul_comm] using
    ((revised_tanh_moment_lower hm.le hm1 hx V hV).trans
      (revised_tanh_moment_comparison hm.le hm1 hx V hV)))


theorem revised_gaussian_reflection (x : ℝ) (V : ℝ≥0) (f : ℝ→ℝ) (hf : Continuous f) :
    (∫w,f w∂gaussianReal (-x) V)=(∫w,f (-w)∂gaussianReal x V) := by
  rw [←gaussianReal_map_neg,integral_map measurable_neg.aemeasurable hf.aestronglyMeasurable]

theorem revised_coleHopf_derivative_odd {m : ℝ} (hm : m ≠ 0) (V : ℝ≥0) (x : ℝ) :
    deriv (coleHopf m V (fun w=>Real.log (Real.cosh w))) (-x) =
      -deriv (coleHopf m V (fun w=>Real.log (Real.cosh w))) x := by
  rw [revised_coleHopf_derivative_ratio hm V (-x),revised_coleHopf_derivative_ratio hm V x,
    revised_gaussian_reflection x V (coshPower m) (revised_continuous_coshPower m),
    revised_gaussian_reflection x V (fun w=>coshPower m w*Real.tanh w)
      ((revised_continuous_coshPower m).mul continuous_revised_tanh)]
  simp only [coshPower,Real.cosh_neg,Real.tanh_neg,mul_neg,integral_neg,neg_div]

/-- Revision (16), Lemma C.2: every finite Cole–Hopf step stays above the
limiting scaled hyperbolic tangent in absolute gradient. The proof uses the
same even monotone likelihood ratio as the paper, with bounded conditional
sign expectations in place of differentiation of an unbounded covariance. -/
theorem revised_coleHopf_gradient_tanh_lower {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1)
    (V : ℝ≥0) (x : ℝ) :
    Real.tanh (m*|x|) ≤ |deriv (coleHopf m V (fun w=>Real.log (Real.cosh w))) x| := by
  rcases le_total 0 x with hx|hx
  · rw [abs_of_nonneg hx]
    exact (revised_coleHopf_derivative_lower_nonneg hm hm1 hx V).trans (le_abs_self _)
  · rw [abs_of_nonpos hx]
    have hh := (revised_coleHopf_derivative_lower_nonneg hm hm1 (neg_nonneg.mpr hx) V).trans
      (le_abs_self (deriv (coleHopf m V (fun w=>Real.log (Real.cosh w))) (-x)))
    rw [revised_coleHopf_derivative_odd hm.ne' V x,abs_neg] at hh
    exact hh

/-- The squared conclusion in revision (16), Lemma C.2, for the actual
Cole–Hopf derivative with no positivity or variance assumptions omitted. -/
theorem revised_coleHopf_gradient_sech_upper {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1)
    (V : ℝ≥0) (x : ℝ) :
    1-(deriv (coleHopf m V (fun w=>Real.log (Real.cosh w))) x)^2 ≤ Paper.sech (m*x)^2 := by
  have hh := revised_coleHopf_gradient_tanh_lower hm hm1 V x
  have ht := Paper.tanh_nonneg (mul_nonneg hm.le (abs_nonneg x))
  have hs : Real.tanh (m*|x|)^2=Real.tanh (m*x)^2 := by
    rcases le_total 0 x with hx|hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx,mul_neg,Real.tanh_neg,neg_sq]
  have ha : |deriv (coleHopf m V (fun w=>Real.log (Real.cosh w))) x|^2 =
      (deriv (coleHopf m V (fun w=>Real.log (Real.cosh w))) x)^2 := sq_abs _
  have hi := Paper.tanh_sq_add_sech_sq (m*x)
  nlinarith [sq_nonneg (|deriv (coleHopf m V (fun w=>Real.log (Real.cosh w))) x|-
    Real.tanh (m*|x|))]


/-- Revision (16), Lemma C.2, with the paper's real nonnegative variance
quantifier and both printed conclusions. -/
theorem revised_tanh_comparison (m V : ℝ) (hm : 0 < m) (hm1 : m ≤ 1)
    (_hV : 0 ≤ V) (x : ℝ) :
    Real.tanh (m*|x|) ≤ |deriv (coleHopf m V.toNNReal (fun w=>Real.log (Real.cosh w))) x| ∧
      1-(deriv (coleHopf m V.toNNReal (fun w=>Real.log (Real.cosh w))) x)^2 ≤
        Paper.sech (m*x)^2 :=
  ⟨revised_coleHopf_gradient_tanh_lower hm hm1 V.toNNReal x,
    revised_coleHopf_gradient_sech_upper hm hm1 V.toNNReal x⟩

end DepthPaper
