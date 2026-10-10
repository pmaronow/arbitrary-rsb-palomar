module

public import FRSB.PolynomialJetBCF
public import FRSB.ItoExpectationSource

@[expose] public section


/-! Genuine fixed-state polynomial moment sources and uniform weak-law
stability for the stochastic expectation passage. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter MvPolynomial Paper
open scoped Topology
namespace FourPapersCommon
open FRSB
set_option maxHeartbeats 1000000

 def fixedStatePolynomialMoment (β h : ℝ) (hβ:β≠0) (μ ν:Paper.ParisiMeasure)
    (f:MomentPolynomial) (t:ℝ) : ℝ :=
  ∫ω,polynomialJetField β ν f t (selectedParisiItoState β h hβ μ t.toNNReal ω)
    ∂canonicalBrownianMeasure

/-- Every polynomial of actual positive spatial jets along the all-field state. -/
def fieldMoment (β h : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (f : MomentPolynomial) (t : ℝ) : ℝ := fixedStatePolynomialMoment β h hβ μ μ f t

 theorem measurable_fixedStatePolynomialField (β h : ℝ) (hβ:β≠0) (μ ν:Paper.ParisiMeasure)
    (f:MomentPolynomial) : Measurable (fun z:ℝ×Paper.BrownianSample=>
      polynomialJetField β ν f z.1 (selectedParisiItoState β h hβ μ z.1.toNNReal z.2)) := by
  have hXm : Measurable (fun z:ℝ×Paper.BrownianSample =>
      selectedParisiItoState β h hβ μ z.1.toNNReal z.2) := by
    convert (measurable_canonicalParisiItoState β h μ
      (fun t x=>parisiGradient β μ (t,x)) (continuous_parisiGradient β μ)
      (fun t x=>norm_parisiGradient_le_one β μ (t,x))
      (lipschitzWith_parisiGradient β hβ μ)).comp
        (measurable_real_toNNReal.prodMap measurable_id) using 1
    rfl
  convert (continuous_polynomialJetField β ν f).measurable.comp
    (measurable_fst.prodMk hXm) using 1
  rfl

 theorem integrable_fixedStatePolynomialField (β h : ℝ) (hβ:β≠0) (μ ν:Paper.ParisiMeasure)
    (f:MomentPolynomial) (t:ℝ) : Integrable (fun ω=>
      polynomialJetField β ν f t (selectedParisiItoState β h hβ μ t.toNNReal ω))
      canonicalBrownianMeasure :=
  (integrable_const (uniformPolynomialMomentBound β f)).mono'
    (((measurable_fixedStatePolynomialField β h hβ μ ν f).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    (.of_forall fun _ω=>norm_polynomialJetField_le_uniform β ν f t _)

 theorem continuous_fixedStatePolynomialMoment (β h : ℝ) (hβ:β≠0) (μ ν:Paper.ParisiMeasure)
    (f:MomentPolynomial) : Continuous (fixedStatePolynomialMoment β h hβ μ ν f) := by
  unfold fixedStatePolynomialMoment
  apply continuous_of_dominated (μ:=canonicalBrownianMeasure)
    (bound:=fun _=>uniformPolynomialMomentBound β f)
  · intro t
    exact (integrable_fixedStatePolynomialField β h hβ μ ν f t).aestronglyMeasurable
  · intro t
    exact .of_forall fun _ω=>norm_polynomialJetField_le_uniform β ν f t _
  · exact integrable_const _
  · apply ae_of_all
    intro ω
    have hc : Continuous (fun t:ℝ=>selectedParisiItoState β h hβ μ t.toNNReal ω) :=
      ((boundedDriftItoCharacteristics_selectedParisiState β h hβ μ).continuous_state ω).comp
        continuous_real_toNNReal
    convert (continuous_polynomialJetField β ν f).comp (continuous_id.prodMk hc) using 1
    rfl

 theorem norm_fixedStatePolynomialMoment_le (β h : ℝ) (hβ:β≠0) (μ ν:Paper.ParisiMeasure)
    (f:MomentPolynomial) (t:ℝ) :
    ‖fixedStatePolynomialMoment β h hβ μ ν f t‖≤uniformPolynomialMomentBound β f := by
  simpa only [probReal_univ,mul_one,fixedStatePolynomialMoment] using
    norm_integral_le_of_norm_le_const (μ:=canonicalBrownianMeasure)
      (f:=fun ω=>polynomialJetField β ν f t (selectedParisiItoState β h hβ μ t.toNNReal ω))
      (C:=uniformPolynomialMomentBound β f)
      (.of_forall fun _ω=>norm_polynomialJetField_le_uniform β ν f t _)

 theorem fixedStatePolynomialMoment_sub_norm_le (β h : ℝ) (hβ:β≠0) (μ ν ρ:Paper.ParisiMeasure)
    (f:MomentPolynomial) (t:ℝ) :
    ‖fixedStatePolynomialMoment β h hβ μ ν f t-fixedStatePolynomialMoment β h hβ μ ρ f t‖≤
      ‖polynomialJetBCF β ν f-polynomialJetBCF β ρ f‖ := by
  unfold fixedStatePolynomialMoment
  rw [←integral_sub (integrable_fixedStatePolynomialField β h hβ μ ν f t)
    (integrable_fixedStatePolynomialField β h hβ μ ρ f t)]
  simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
    (μ:=canonicalBrownianMeasure) (.of_forall fun ω=>norm_polynomialJetField_sub_le β ν ρ f t
      (selectedParisiItoState β h hβ μ t.toNNReal ω))

 theorem fixedStatePolynomialMoment_self_physical (β h : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (f : MomentPolynomial) {t : ℝ} (_ht : t∈Icc (0:ℝ) 1) :
    fixedStatePolynomialMoment β h hβ μ μ f t=fieldMoment β h hβ μ f t := rfl

theorem continuous_fieldMoment (β h : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (f : MomentPolynomial) : Continuous (fieldMoment β h hβ μ f) :=
  continuous_fixedStatePolynomialMoment β h hβ μ μ f

 def polynomialMomentSource (β h : ℝ) (hβ:β≠0) (μ ν:Paper.ParisiMeasure)
    (f:MomentPolynomial) (t:ℝ) : ℝ := β^2*(
  fixedStatePolynomialMoment β h hβ μ ν (momentDrift0 f) t+
    parisiCDF μ t*fixedStatePolynomialMoment β h hβ μ ν (momentDrift1 f) t)

 theorem polynomialMomentSource_measurable (β h : ℝ) (hβ:β≠0) (μ ν:Paper.ParisiMeasure)
    (f:MomentPolynomial) : Measurable (polynomialMomentSource β h hβ μ ν f) :=
  measurable_const.mul ((continuous_fixedStatePolynomialMoment β h hβ μ ν _).measurable.add
    ((parisiCDF_measurable μ).mul (continuous_fixedStatePolynomialMoment β h hβ μ ν _).measurable))

 theorem norm_polynomialMomentSource_le (β h : ℝ) (hβ:β≠0) (μ ν:Paper.ParisiMeasure)
    (f:MomentPolynomial) (t:ℝ) :
    ‖polynomialMomentSource β h hβ μ ν f t‖≤β^2*(uniformPolynomialMomentBound β (momentDrift0 f)+
      uniformPolynomialMomentBound β (momentDrift1 f)) := by
  unfold polynomialMomentSource
  rw [norm_mul,Real.norm_of_nonneg (sq_nonneg β)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg β)
  apply (norm_add_le _ _).trans
  apply add_le_add (norm_fixedStatePolynomialMoment_le β h hβ μ ν _ t)
  rw [norm_mul,Real.norm_of_nonneg (parisiCDF_nonneg μ t)]
  exact (mul_le_mul (parisiCDF_le_one μ t) (norm_fixedStatePolynomialMoment_le β h hβ μ ν _ t)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

 theorem polynomialMomentSource_intervalIntegrable (β h : ℝ) (hβ:β≠0)
    (μ ν:Paper.ParisiMeasure) (f:MomentPolynomial) (a b:ℝ) :
    IntervalIntegrable (polynomialMomentSource β h hβ μ ν f) volume a b :=
  (intervalIntegrable_const (c:=β^2*(uniformPolynomialMomentBound β (momentDrift0 f)+
    uniformPolynomialMomentBound β (momentDrift1 f)))).mono_fun'
      (polynomialMomentSource_measurable β h hβ μ ν f).aestronglyMeasurable
      (.of_forall fun t=>norm_polynomialMomentSource_le β h hβ μ ν f t)

 theorem polynomialMomentSource_eq_integral (β h : ℝ) (hβ:β≠0)
    (μ ν:Paper.ParisiMeasure) (f:MomentPolynomial) (t:ℝ) :
    polynomialMomentSource β h hβ μ ν f t=∫ω,β^2*(
      polynomialJetField β ν (momentDrift0 f) t (selectedParisiItoState β h hβ μ t.toNNReal ω)+
      parisiCDF μ t*polynomialJetField β ν (momentDrift1 f) t
        (selectedParisiItoState β h hβ μ t.toNNReal ω)) ∂canonicalBrownianMeasure := by
  unfold polynomialMomentSource fixedStatePolynomialMoment
  rw [integral_const_mul,integral_add (integrable_fixedStatePolynomialField β h hβ μ ν _ t)
    ((integrable_fixedStatePolynomialField β h hβ μ ν _ t).const_mul (parisiCDF μ t)),integral_const_mul]

 theorem polynomialMomentSource_sub_norm_le (β h : ℝ) (hβ:β≠0)
    (μ ν ρ:Paper.ParisiMeasure) (f:MomentPolynomial) (t:ℝ) :
    ‖polynomialMomentSource β h hβ μ ν f t-polynomialMomentSource β h hβ μ ρ f t‖≤
      β^2*(‖polynomialJetBCF β ν (momentDrift0 f)-polynomialJetBCF β ρ (momentDrift0 f)‖+
        ‖polynomialJetBCF β ν (momentDrift1 f)-polynomialJetBCF β ρ (momentDrift1 f)‖) := by
  unfold polynomialMomentSource
  rw [←mul_sub,show (fixedStatePolynomialMoment β h hβ μ ν (momentDrift0 f) t+
      parisiCDF μ t*fixedStatePolynomialMoment β h hβ μ ν (momentDrift1 f) t)-
      (fixedStatePolynomialMoment β h hβ μ ρ (momentDrift0 f) t+
      parisiCDF μ t*fixedStatePolynomialMoment β h hβ μ ρ (momentDrift1 f) t)=
    (fixedStatePolynomialMoment β h hβ μ ν (momentDrift0 f) t-fixedStatePolynomialMoment β h hβ μ ρ (momentDrift0 f) t)+
      parisiCDF μ t*(fixedStatePolynomialMoment β h hβ μ ν (momentDrift1 f) t-fixedStatePolynomialMoment β h hβ μ ρ (momentDrift1 f) t) by ring,
    norm_mul,Real.norm_of_nonneg (sq_nonneg β)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg β)
  apply (norm_add_le _ _).trans
  apply add_le_add (fixedStatePolynomialMoment_sub_norm_le β h hβ μ ν ρ _ t)
  rw [norm_mul,Real.norm_of_nonneg (parisiCDF_nonneg μ t)]
  exact (mul_le_mul (parisiCDF_le_one μ t) (fixedStatePolynomialMoment_sub_norm_le β h hβ μ ν ρ _ t)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

 theorem tendsto_polynomialMomentSource_integral_of_weak {ι:Type*} {L:Filter ι}
    (β h : ℝ) (hβ:β≠0) (μ ρ:Paper.ParisiMeasure) (ν:ι→Paper.ParisiMeasure)
    (hν:Tendsto ν L (nhds ρ)) (f:MomentPolynomial) (a b:ℝ) :
    Tendsto (fun i=>∫t in a..b,polynomialMomentSource β h hβ μ (ν i) f t) L
      (nhds (∫t in a..b,polynomialMomentSource β h hβ μ ρ f t)) := by
  let E:ι→ℝ:=fun i=>β^2*(‖polynomialJetBCF β (ν i) (momentDrift0 f)-
    polynomialJetBCF β ρ (momentDrift0 f)‖+‖polynomialJetBCF β (ν i) (momentDrift1 f)-
      polynomialJetBCF β ρ (momentDrift1 f)‖)
  have hE:Tendsto E L (nhds 0) := by
    have h0:=((continuous_polynomialJetBCF β (momentDrift0 f)).tendsto ρ).comp hν
      |>.sub_const (polynomialJetBCF β ρ (momentDrift0 f)) |>.norm
    have h1:=((continuous_polynomialJetBCF β (momentDrift1 f)).tendsto ρ).comp hν
      |>.sub_const (polynomialJetBCF β ρ (momentDrift1 f)) |>.norm
    simpa only [E,Function.comp_apply,sub_self,norm_zero,zero_add,mul_zero] using (h0.add h1).const_mul (β^2)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (g:=fun i=>E i*|b-a|) (fun i=>norm_nonneg _)
  · intro i
    rw [←intervalIntegral.integral_sub (polynomialMomentSource_intervalIntegrable β h hβ μ (ν i) f a b)
      (polynomialMomentSource_intervalIntegrable β h hβ μ ρ f a b)]
    exact intervalIntegral.norm_integral_le_of_norm_le_const
      (fun t _=>polynomialMomentSource_sub_norm_le β h hβ μ (ν i) ρ f t)
  · simpa only [zero_mul] using hE.mul_const |b-a|

end FourPapersCommon
