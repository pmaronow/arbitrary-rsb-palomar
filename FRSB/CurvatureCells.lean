module

public import FRSB.CurvatureEvolutionSource
public import FRSB.JetGenerator
public import FRSB.InteriorTimeCap

@[expose] public section


/-! Actual finite-cell curvature-square Itô identities on the fixed optimal
state. Smooth two-sided caps supply genuine global Itô tests. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus Paper
open scoped Topology NNReal
namespace FRSB
set_option maxHeartbeats 1000000
open SpinGlass.Targets

 theorem curvature_square_finite_cell_cropped_bound (β : ℝ) (hβ : β≠0)
    (μ : ParisiMeasure) {k : ℕ} (s : RSBScheme k) {p : ℕ} (hp:p≤k+1)
    (hq:s.q p<s.q (p+1)) (l r : ℝ≥0) (hl:s.q p<(l:ℝ)) (hlr:l≤r)
    (hr:(r:ℝ)<s.q (p+1)) (eps : ℝ) (heps:0≤eps)
    (hclose:∀t∈Icc (l:ℝ) (r:ℝ),∀x,
      ‖parisiGradient β μ (t,x)-parisiSpatialJet β (parisiSchemeMeasure s) 1 t x‖≤eps) :
    ‖fixedStateJetPower β hβ μ (parisiSchemeMeasure s) 1 2 r-
      fixedStateJetPower β hβ μ (parisiSchemeMeasure s) 1 2 l-
      ∫t in (l:ℝ)..(r:ℝ),curvatureEvolutionSource β hβ μ (parisiSchemeMeasure s) t‖ ≤
    ∫t in (l:ℝ)..(r:ℝ),2*β^2*((1+uniformSpatialConstant β 2)*|parisiCDF μ t-s.m p|+
      uniformSpatialConstant β 2*eps) := by
  let ν:=parisiSchemeMeasure s
  let u:=parisiSpatialJet β ν 2
  let ut:=cellTimeForcing β ν (s.m p) 2
  let ux:=parisiSpatialJet β ν 3
  let uxx:=parisiSpatialJet β ν 4
  let g:=interiorCappedTest u (s.q p) l r (s.q (p+1))
  let f:=itoSquareTest g
  let X:=selectedParisiItoState β 0 hβ μ
  let d:=selectedParisiItoDrift β 0 hβ μ
  let K:=uniformSpatialConstant β 2
  have hK:0<K := uniformSpatialConstant_pos β 2
  have hut:∀t∈Ioo (s.q p) (s.q (p+1)),∀x,
      HasDerivAt (fun t=>u t x) (ut t x) t :=
    fun t ht x=>hasDerivAt_finiteCell_spatialJet_time s β hβ hp hq 2 ht x
  have hux:∀t x,HasDerivAt (u t) (ux t x) x :=
    fun t x=>hasDerivAt_parisiSpatialJet_succ β ν 1 t x
  have huxx:∀t x,HasDerivAt (ux t) (uxx t x) x :=
    fun t x=>hasDerivAt_parisiSpatialJet_succ β ν 2 t x
  obtain ⟨hgc,hgt,hgs,hgdt,hgx,hgxx⟩:=interiorCappedTest_regular u ut ux uxx
    (s.q p) l r (s.q (p+1)) hl (NNReal.coe_le_coe.mpr hlr) hr
    (continuous_parisiSpatialJet_succ β ν 1) (continuous_cellTimeForcing β ν (s.m p) 2)
    (continuous_parisiSpatialJet_succ β ν 2) (continuous_parisiSpatialJet_succ β ν 3)
    hut hux huxx (fun t=>(contDiff_parisiSpatialJet_succ β ν 1 t).of_le (by simp))
  have hgd:∀t,Differentiable ℝ (g t) := fun t=>(hgs t).differentiable (by norm_num)
  have hgB:∀t x,‖g t x‖≤1 := by
    intro t x
    change ‖parisiSpatialJet β ν 2 _ x‖≤1
    rw [parisiSpatialJet_two]
    exact norm_parisiHessian_le_one_all β ν _
  have hgxB:∀t x,‖itoSpaceDerivative g t x‖≤K := by
    intro t x
    rw [interiorCappedTest_spaceDerivative u ux hux]
    exact (norm_parisiSpatialJet_succ_le β ν 2 _ x).trans
      (norm_spatialDerivativeBCF_le_uniform β ν 2)
  let source:ℝ→BrownianSample→ℝ:=fun t ω=>β^2*
    (parisiSpatialJet β ν 3 t (X t.toNNReal ω)^2-
      2*parisiCDF μ t*parisiSpatialJet β ν 2 t (X t.toNNReal ω)^3)
  have hXm : Measurable (Function.uncurry (fun t:ℝ=>X t.toNNReal)) := by
    have hm := (measurable_canonicalParisiItoState β 0 μ
      (fun t x=>parisiGradient β μ (t,x)) (continuous_parisiGradient β μ)
      (fun t x=>norm_parisiGradient_le_one β μ (t,x))
      (lipschitzWith_parisiGradient β hβ μ)).comp
        (measurable_real_toNNReal.prodMap measurable_id)
    exact hm
  have hmap:Measurable (fun z:ℝ×BrownianSample=>(z.1,X z.1.toNNReal z.2)) :=
    measurable_fst.prodMk hXm
  have hsMeas:Measurable (Function.uncurry source) :=
    measurable_const.mul ((((continuous_parisiSpatialJet_succ β ν 2).measurable.comp hmap).pow_const 2).sub
      (((measurable_const.mul ((parisiCDF_measurable μ).comp measurable_fst)).mul
        (((continuous_parisiSpatialJet_succ β ν 1).measurable.comp hmap).pow_const 3))))
  have hsB:∀t ω,‖source t ω‖≤β^2*(K^2+2) := by
    intro t ω
    dsimp only [source]
    rw [norm_mul,Real.norm_of_nonneg (sq_nonneg β)]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg β)
    apply (norm_sub_le _ _).trans
    rw [norm_pow,norm_mul,norm_mul,norm_pow,show ‖(2:ℝ)‖=2 by norm_num,
      Real.norm_of_nonneg (parisiCDF_nonneg μ t)]
    apply add_le_add
    · exact pow_le_pow_left₀ (norm_nonneg _)
        ((norm_parisiSpatialJet_succ_le β ν 2 t _).trans
          (norm_spatialDerivativeBCF_le_uniform β ν 2)) 2
    · have hh:‖parisiSpatialJet β ν 2 t (X t.toNNReal ω)‖≤1 := by
        rw [parisiSpatialJet_two];exact norm_parisiHessian_le_one_all β ν _
      exact (mul_le_mul (mul_le_mul_of_nonneg_left (parisiCDF_le_one μ t) (by norm_num))
        (pow_le_one₀ (norm_nonneg _) hh (n:=3)) (by positivity) (by norm_num)).trans_eq (by ring)
  let E:ℝ→ℝ:=fun t=>2*β^2*((1+K)*|parisiCDF μ t-s.m p|+K*eps)
  have hEi:IntervalIntegrable E volume l r :=
    (((((parisiCDF_monotone μ).intervalIntegrable).sub intervalIntegrable_const).norm.const_mul (1+K)).add
      intervalIntegrable_const).const_mul (2*β^2)
  have hgen:∀ω,∀t∈Icc (l:ℝ) (r:ℝ),‖hjbGenerator X d β f t ω-source t ω‖≤E t := by
    intro ω t ht
    have ht0:0≤t := l.coe_nonneg.trans ht.1
    have ht1:t≤1 := ht.2.trans (hr.le.trans (s.q_le_one (by omega)))
    have hdr:d t.toNNReal ω=β^2*parisiCDF μ t*parisiGradient β μ (t,X t.toNNReal ω) := by
      simp only [d,selectedParisiItoDrift,canonicalParisiItoDrift,Real.coe_toNNReal t ht0,
        ite_eq_left ht1,X,selectedParisiItoState]
    rw [itoSquareTest_generator X d β g hgt hgs]
    unfold hjbGenerator
    rw [interiorCappedTest_timeDerivative u ut (s.q p) l r (s.q (p+1)) hl
      (NNReal.coe_le_coe.mpr hlr) hr hut,
      interiorCappedTest_spaceDerivative u ux hux,
      interiorCappedTest_spaceSecondDerivative u ux uxx hux huxx,
      interiorTimeCap_eq _ _ _ _ _ ht,interiorTimeCapD_eq _ _ _ _ _ ht,hdr]
    dsimp only [g,interiorCappedTest]
    rw [interiorTimeCap_eq _ _ _ _ _ ht,mul_one]
    exact curvature_square_generator_error β ν (s.m p) (parisiCDF μ t)
      (parisiGradient β μ (t,X t.toNNReal ω)) t (X t.toNNReal ω) eps K
      ⟨parisiCDF_nonneg μ t,parisiCDF_le_one μ t⟩ heps hK.le (hclose t ht _)
      (by rw [parisiSpatialJet_one];exact norm_parisiGradient_le_one β ν _)
      (by rw [parisiSpatialJet_two];exact norm_parisiHessian_le_one_all β ν _)
      ((norm_parisiSpatialJet_succ_le β ν 2 t _).trans (norm_spatialDerivativeBCF_le_uniform β ν 2))
  have hfi (t:ℝ≥0):Integrable (fun ω=>f t (X t ω)) canonicalBrownianMeasure := by
    have hm:Measurable (X t) :=
      (boundedDriftItoCharacteristics_selectedParisiState β 0 hβ μ).adapted_state t
        |>.measurable |>.mono (canonicalBrownianFiltration.le t) le_rfl
    exact (integrable_const (1:ℝ)).mono'
      ((hgc.pow 2).measurable.comp (measurable_const.prodMk hm)).aestronglyMeasurable
      (.of_forall fun ω=>by change ‖g t (X t ω)^2‖≤1;rw [norm_pow];exact pow_le_one₀ (norm_nonneg _) (hgB t _) (n:=2))
  have hh:=ito_expectation_source_error (boundedDriftItoCharacteristics_selectedParisiState β 0 hβ μ)
    f (continuous_itoSquareTest g hgc) (differentiable_itoSquareTest_time g hgt)
    (contDiff_itoSquareTest_spatial g hgs) (continuous_itoSquareTest_timeDerivative g hgc hgt hgdt)
    (continuous_itoSquareTest_spaceDerivative g hgc hgd hgx)
    (continuous_itoSquareTest_spaceSecondDerivative g hgc hgs hgx hgxx)
    l r hlr ⟨2*K,by positivity⟩ (fun t _ x=>by
      change ‖itoSpaceDerivative (itoSquareTest g) t x‖≤2*K
      convert norm_itoSquareTest_spaceDerivative_le g hgd hgB hgxB t x using 1
      ring)
    source hsMeas (β^2*(K^2+2)) hsB E hEi hgen (hfi l) (hfi r)
  have heval (t:ℝ≥0) (ht:(t:ℝ)∈Icc (l:ℝ) (r:ℝ)) :
      (∫ω,f t (X t ω) ∂canonicalBrownianMeasure)=fixedStateJetPower β hβ μ ν 1 2 t := by
    unfold f itoSquareTest g interiorCappedTest fixedStateJetPower
    rw [interiorTimeCap_eq _ _ _ _ _ ht]
    simp only [Real.toNNReal_coe]
    rfl
  have hsEq:(fun t=>∫ω,source t ω ∂canonicalBrownianMeasure)=curvatureEvolutionSource β hβ μ ν :=
    funext fun t=>(curvatureEvolutionSource_eq_integral β hβ μ ν t).symm
  rw [heval r ⟨NNReal.coe_le_coe.mpr hlr,le_rfl⟩,heval l ⟨le_rfl,NNReal.coe_le_coe.mpr hlr⟩,hsEq] at hh
  exact hh

end FRSB
