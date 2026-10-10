module

public import FourPapersCommon.AllFieldPolynomialMomentSources
public import FRSB.PolynomialGeneratorError
public import FRSB.InteriorTimeCap

@[expose] public section


/-! Genuine arbitrary-polynomial finite-cell Itô identities on the actual
optimal diffusion; all test regularity follows from the actual jet hierarchy. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus Paper
open scoped Topology NNReal
namespace FourPapersCommon
open FRSB
set_option maxHeartbeats 1000000
open SpinGlass.Targets

 theorem polynomial_moment_finite_cell_cropped_bound (β h : ℝ) (hβ:β≠0)
    (μ:Paper.ParisiMeasure) {k:ℕ} (s:RSBScheme k) {p:ℕ} (hp:p≤k+1)
    (hq:s.q p<s.q (p+1)) (F:MomentPolynomial) (l r:ℝ≥0)
    (hl:s.q p<(l:ℝ)) (hlr:l≤r) (hr:(r:ℝ)<s.q (p+1))
    (eps:ℝ) (heps:0≤eps)
    (hclose:∀t∈Icc (l:ℝ) (r:ℝ),∀x,
      ‖parisiGradient β μ (t,x)-parisiSpatialJet β (parisiSchemeMeasure s) 1 t x‖≤eps) :
    ‖fixedStatePolynomialMoment β h hβ μ (parisiSchemeMeasure s) F r-
      fixedStatePolynomialMoment β h hβ μ (parisiSchemeMeasure s) F l-
      ∫t in (l:ℝ)..(r:ℝ),polynomialMomentSource β h hβ μ (parisiSchemeMeasure s) F t‖ ≤
    ∫t in (l:ℝ)..(r:ℝ),β^2*((uniformPolynomialMomentBound β (momentDrift1 F)+
      uniformPolynomialMomentBound β (polynomialSpatialDerivative F))*|parisiCDF μ t-s.m p|+
        uniformPolynomialMomentBound β (polynomialSpatialDerivative F)*eps) := by
  let ν:=parisiSchemeMeasure s
  let u:=polynomialJetField β ν F
  let ut:=fun t x=>β^2*polynomialJetField β ν (polynomialTimeDerivative (s.m p) F) t x
  let ux:=polynomialJetField β ν (polynomialSpatialDerivative F)
  let uxx:=polynomialJetField β ν (polynomialSpatialDerivative (polynomialSpatialDerivative F))
  let f:=interiorCappedTest u (s.q p) l r (s.q (p+1))
  let X:=selectedParisiItoState β h hβ μ
  let d:=selectedParisiItoDrift β h hβ μ
  let K:=uniformPolynomialMomentBound β (polynomialSpatialDerivative F)
  have hK:0≤K := uniformPolynomialMomentBound_nonneg β _
  have hut:∀t∈Ioo (s.q p) (s.q (p+1)),∀x,
      HasDerivAt (fun t=>u t x) (ut t x) t :=
    fun t ht x=>hasDerivAt_finiteCell_polynomialJetField_time β hβ s hp hq F ht x
  have hux:∀t x,HasDerivAt (u t) (ux t x) x :=
    fun t x=>hasDerivAt_polynomialJetField_spatial β ν F t x
  have huxx:∀t x,HasDerivAt (ux t) (uxx t x) x :=
    fun t x=>hasDerivAt_polynomialJetField_spatial β ν _ t x
  obtain ⟨hfc,hft,hfs,hfdt,hfx,hfxx⟩:=interiorCappedTest_regular u ut ux uxx
    (s.q p) l r (s.q (p+1)) hl (NNReal.coe_le_coe.mpr hlr) hr
    (continuous_polynomialJetField β ν F)
    (continuous_const.mul (continuous_polynomialJetField β ν _))
    (continuous_polynomialJetField β ν _) (continuous_polynomialJetField β ν _)
    hut hux huxx (fun t=>(contDiff_polynomialJetField_spatial β ν F t).of_le (by simp))
  have hfxB:∀t x,‖itoSpaceDerivative f t x‖≤K := by
    intro t x
    rw [interiorCappedTest_spaceDerivative u ux hux]
    exact norm_polynomialJetField_le_uniform β ν _ _ x
  let source:ℝ→Paper.BrownianSample→ℝ:=fun t ω=>β^2*(
    polynomialJetField β ν (momentDrift0 F) t (X t.toNNReal ω)+
      parisiCDF μ t*polynomialJetField β ν (momentDrift1 F) t (X t.toNNReal ω))
  have hsMeas:Measurable (Function.uncurry source) :=
    measurable_const.mul ((measurable_fixedStatePolynomialField β h hβ μ ν _).add
      (((parisiCDF_measurable μ).comp measurable_fst).mul
        (measurable_fixedStatePolynomialField β h hβ μ ν _)))
  have hsB:∀t ω,‖source t ω‖≤β^2*(uniformPolynomialMomentBound β (momentDrift0 F)+
      uniformPolynomialMomentBound β (momentDrift1 F)) := by
    intro t ω
    dsimp only [source]
    rw [norm_mul,Real.norm_of_nonneg (sq_nonneg β)]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg β)
    apply (norm_add_le _ _).trans
    apply add_le_add (norm_polynomialJetField_le_uniform β ν _ t _)
    rw [norm_mul,Real.norm_of_nonneg (parisiCDF_nonneg μ t)]
    exact (mul_le_mul (parisiCDF_le_one μ t) (norm_polynomialJetField_le_uniform β ν _ t _)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  let E:ℝ→ℝ:=fun t=>β^2*((uniformPolynomialMomentBound β (momentDrift1 F)+K)*
    |parisiCDF μ t-s.m p|+K*eps)
  have hEi:IntervalIntegrable E volume l r :=
    (((((parisiCDF_monotone μ).intervalIntegrable).sub intervalIntegrable_const).norm.const_mul
      (uniformPolynomialMomentBound β (momentDrift1 F)+K)).add intervalIntegrable_const).const_mul (β^2)
  have hgen:∀ω,∀t∈Icc (l:ℝ) (r:ℝ),‖hjbGenerator X d β f t ω-source t ω‖≤E t := by
    intro ω t ht
    have ht0:0≤t := l.coe_nonneg.trans ht.1
    have ht1:t≤1 := ht.2.trans (hr.le.trans (s.q_le_one (by omega)))
    have hdr:d t.toNNReal ω=β^2*parisiCDF μ t*parisiGradient β μ (t,X t.toNNReal ω) := by
      simp only [d,selectedParisiItoDrift,canonicalParisiItoDrift,Real.coe_toNNReal t ht0,
        ite_eq_left ht1,X,selectedParisiItoState]
    unfold hjbGenerator
    rw [interiorCappedTest_timeDerivative u ut (s.q p) l r (s.q (p+1)) hl
      (NNReal.coe_le_coe.mpr hlr) hr hut,
      interiorCappedTest_spaceDerivative u ux hux,
      interiorCappedTest_spaceSecondDerivative u ux uxx hux huxx,
      interiorTimeCap_eq _ _ _ _ _ ht,interiorTimeCapD_eq _ _ _ _ _ ht,hdr,mul_one]
    exact polynomial_generator_drift_error β ν (s.m p) (parisiCDF μ t)
      (parisiGradient β μ (t,X t.toNNReal ω)) F t (X t.toNNReal ω) eps
      ⟨parisiCDF_nonneg μ t,parisiCDF_le_one μ t⟩ heps (hclose t ht _)
      (by rw [parisiSpatialJet_one];exact norm_parisiGradient_le_one β ν _)
  have hfi (t:ℝ≥0):Integrable (fun ω=>f t (X t ω)) canonicalBrownianMeasure := by
    have hm:Measurable (X t) :=
      (boundedDriftItoCharacteristics_selectedParisiState β h hβ μ).adapted_state t
        |>.measurable |>.mono (canonicalBrownianFiltration.le t) le_rfl
    exact (integrable_const (uniformPolynomialMomentBound β F)).mono'
      (hfc.measurable.comp (measurable_const.prodMk hm)).aestronglyMeasurable
      (.of_forall fun ω=>norm_polynomialJetField_le_uniform β ν F _ _)
  have hh:=ito_expectation_source_error (boundedDriftItoCharacteristics_selectedParisiState β h hβ μ)
    f hfc hft hfs hfdt hfx hfxx l r hlr ⟨K,hK⟩ (fun t _ x=>hfxB t x)
    source hsMeas (β^2*(uniformPolynomialMomentBound β (momentDrift0 F)+
      uniformPolynomialMomentBound β (momentDrift1 F))) hsB E hEi hgen (hfi l) (hfi r)
  have heval (t:ℝ≥0) (ht:(t:ℝ)∈Icc (l:ℝ) (r:ℝ)) :
      (∫ω,f t (X t ω) ∂canonicalBrownianMeasure)=fixedStatePolynomialMoment β h hβ μ ν F t := by
    unfold f interiorCappedTest fixedStatePolynomialMoment
    rw [interiorTimeCap_eq _ _ _ _ _ ht]
    simp only [Real.toNNReal_coe]
    rfl
  have hsEq:(fun t=>∫ω,source t ω ∂canonicalBrownianMeasure)=polynomialMomentSource β h hβ μ ν F :=
    funext fun t=>(polynomialMomentSource_eq_integral β h hβ μ ν F t).symm
  rw [heval r ⟨NNReal.coe_le_coe.mpr hlr,le_rfl⟩,heval l ⟨le_rfl,NNReal.coe_le_coe.mpr hlr⟩,hsEq] at hh
  exact hh

end FourPapersCommon
