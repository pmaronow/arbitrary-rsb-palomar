module

public import DepthPaper.RevisedEntropyRecursion
public import DepthPaper.TerminalConstantShift
public import DepthPaper.ColeHopfRecursionBounds

@[expose] public section

/-! The exact terminal Banach-space Cole–Hopf identities, spatial derivatives,
and all-order bounds of Appendix A.1. All terminal-direction assertions
include zero mass and zero variance. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ContDiff BigOperators BoundedContinuousFunction
namespace DepthPaper
open ColeHopfFoundation.ProbabilityTheory
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

theorem revised_coleHopf_semigroup (a s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (g : TerminalSpace) :
    coleHopfTerminal ((a,s),coleHopfTerminal ((a,t),g)) =
      coleHopfTerminal ((a,s+t),g) := by
  apply terminalValue_injective
  funext x
  rw [terminalValue_coleHopfTerminal_nonneg _ hs,
    terminalValue_coleHopfTerminal_nonneg _ (add_nonneg hs ht)]
  have he : terminalValue (coleHopfTerminal ((a,t),g)) = coleHopf a t.toNNReal (terminalValue g) :=
    funext (terminalValue_coleHopfTerminal_nonneg _ ht)
  rw [he,coleHopf_coleHopf (hasLinearGrowth_terminalValue g)
    (contDiff_terminalValue g).continuous.measurable]
  congr 2
  apply NNReal.coe_injective
  simp [Real.coe_toNNReal _ hs,Real.coe_toNNReal _ ht,Real.coe_toNNReal _ (add_nonneg hs ht)]

theorem revised_constantMassKernel_add_constant (a : ℝ) (V : ℝ≥0)
    (g : TerminalSpace) (c : ℝ) :
    FRSB.constantMassKernel a V (terminalValue (g+terminalConstant c)) =
      FRSB.constantMassKernel a V (terminalValue g) := by
  have he : terminalValue (g+terminalConstant c) = fun x => terminalValue g x+c := by
    funext x; simp [terminalValue_add]
  have hw : FRSB.constantMassWeight a V (terminalValue (g+terminalConstant c)) =
      FRSB.constantMassWeight a V (terminalValue g) := by
    funext x y
    rw [he]
    unfold FRSB.constantMassWeight
    rw [coleHopf_add_const (hasLinearGrowth_terminalValue g)
      (contDiff_terminalValue g).continuous.measurable]
    congr 1
    ring
  simp only [FRSB.constantMassKernel,hw]

/-- The Banach-space transform and its kernel preserve arbitrary constants,
and its nonnegative-variance operators form a semigroup. -/
theorem revised_one_step_constants_semigroup (a V : ℝ) (hV : 0 ≤ V)
    (g : TerminalSpace) :
    (∀ c, coleHopfTerminal ((a,V),g+terminalConstant c) =
      coleHopfTerminal ((a,V),g)+terminalConstant c) ∧
    (∀ c, FRSB.constantMassKernel a V.toNNReal (terminalValue (g+terminalConstant c)) =
      FRSB.constantMassKernel a V.toNNReal (terminalValue g)) ∧
    (∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      coleHopfTerminal ((a,s),coleHopfTerminal ((a,t),g)) = coleHopfTerminal ((a,s+t),g)) :=
  ⟨coleHopfTerminal_add_constant a V hV g,
    revised_constantMassKernel_add_constant a V.toNNReal g,
    fun s t hs ht => revised_coleHopf_semigroup a s t hs ht g⟩

theorem revised_gaussianTerminalTiltMean_kernel (a V : ℝ) (hV : 0 < V)
    (g : TerminalSpace) (G : ℝ →ᵇ ℝ) (x : ℝ) :
    gaussianTerminalTiltMean ((a,V),g) G x =
      ∫ y, G y ∂FRSB.constantMassKernel a V.toNNReal (terminalValue g) x := by
  rw [gaussianTerminalTiltMean_apply _ G hV x]
  have he := FRSB.backwardHeatQuotient_exp_eq_kernel_integral a V.toNNReal
    (terminalValue g) (contDiff_terminalValue g).continuous
    (hasLinearGrowth_terminalValue g) G G.continuous.measurable x
  rw [FRSB.backwardHeatQuotient,FRSB.gaussianHeatFlow,FRSB.gaussianHeatFlow,
    Real.toNNReal_coe] at he
  rw [←he]
  unfold uncenteredGaussianTiltMean
  congr 1
  apply integral_congr_ae
  exact .of_forall fun _ => mul_comm _ _

/-- The displayed first and second spatial derivative formulas, where the
variance is explicitly the second moment minus the square of the mean. -/
theorem revised_one_step_spatial (a V : ℝ) (hV : 0 ≤ V) (g : TerminalSpace)
    (hg : ‖terminalJet g 0‖ ≤ 1) :
    LipschitzWith 1 (terminalValue (coleHopfTerminal ((a,V),g))) ∧
    (∀ x, HasDerivAt (terminalValue (coleHopfTerminal ((a,V),g)))
      (∫ y, terminalJet g 0 y ∂FRSB.constantMassKernel a V.toNNReal (terminalValue g) x) x) ∧
    (∀ x, HasDerivAt (terminalJet (coleHopfTerminal ((a,V),g)) 0)
      ((∫ y, terminalJet g 1 y ∂FRSB.constantMassKernel a V.toNNReal (terminalValue g) x)+
        a*((∫ y, (terminalJet g 0 y)^2 ∂FRSB.constantMassKernel a V.toNNReal (terminalValue g) x)-
          (∫ y, terminalJet g 0 y ∂FRSB.constantMassKernel a V.toNNReal (terminalValue g) x)^2)) x) := by
  have hbound := (norm_terminalJet_coleHopfTerminal_nonneg ((a,V),g) hV).trans hg
  have hlip : LipschitzWith 1 (terminalValue (coleHopfTerminal ((a,V),g))) :=
    (lipschitzWith_terminalValue _).weaken (by exact_mod_cast hbound)
  refine ⟨hlip,?_,?_⟩
  · intro x
    by_cases hv : 0 < V
    · have he := hasDerivAt_coleHopf_terminalValue ((a,V),g) hv x
      rw [←gaussianTerminalTiltMean_jet_zero,
        revised_gaussianTerminalTiltMean_kernel a V hv g _ x] at he
      exact he.congr_of_eventuallyEq (.of_forall fun x =>
        terminalValue_coleHopfTerminal_nonneg _ hV x)
    · have hz : V=0 := le_antisymm (le_of_not_gt hv) hV
      subst V
      simp only [coleHopfTerminal_zero_variance,Real.toNNReal_zero,
        FRSB.constantMassKernel_zero_variance a (terminalValue g)
          (contDiff_terminalValue g).continuous (hasLinearGrowth_terminalValue g),
        Kernel.id_apply,integral_dirac]
      exact hasDerivAt_terminalValue g x
  · intro x
    by_cases hv : 0 < V
    · have he : terminalJet (coleHopfTerminal ((a,V),g)) 0 = terminalGaussianJetOne ((a,V),g) := by
        ext y
        exact (hasDerivAt_terminalValue _ y).unique
          ((hasDerivAt_coleHopf_terminalValue ((a,V),g) hv y).congr_of_eventuallyEq
            (.of_forall fun x => terminalValue_coleHopfTerminal_nonneg _ hV x))
      rw [he]
      have hd := hasDerivAt_terminalGaussianJetOne ((a,V),g) hv x
      apply hd.congr_deriv
      change gaussianTerminalTiltMean ((a,V),g) (terminalJet g 1) x+
        a*(gaussianTerminalTiltMean ((a,V),g) ((terminalJet g 0)^2) x-
          (gaussianTerminalTiltMean ((a,V),g) (terminalJet g 0) x)^2) = _
      simp_rw [revised_gaussianTerminalTiltMean_kernel a V hv g]
      rfl
    · have hz : V=0 := le_antisymm (le_of_not_gt hv) hV
      subst V
      simp only [coleHopfTerminal_zero_variance,Real.toNNReal_zero,
        FRSB.constantMassKernel_zero_variance a (terminalValue g)
          (contDiff_terminalValue g).continuous (hasLinearGrowth_terminalValue g),
        Kernel.id_apply,integral_dirac,sub_self,mul_zero,add_zero]
      exact hasDerivAt_terminalJet_zero g x

theorem revised_one_step_smooth_bounds (alo ahi Vlo Vhi M : ℝ)
    (halo : 0 < alo) (ha : alo ≤ ahi) (hVlo : 0 < Vlo) (hV : Vlo ≤ Vhi) :
    ContDiffOn ℝ ∞ coleHopfTerminal
      {p : ColeHopfParameter | 0 < p.1.1 ∧ 0 < p.1.2 ∧ ‖terminalJet p.2 0‖ < 2} ∧
    (∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ColeHopfParameter,
      p.1.1 ∈ Icc alo ahi → p.1.2 ∈ Icc Vlo Vhi → terminalSumNorm p.2 ≤ M →
      ‖iteratedFDeriv ℝ n coleHopfTerminal p‖ ≤ C) := by
  refine ⟨fun p hp => (contDiffAt_coleHopfTerminal p hp.2.1).contDiffWithinAt,?_⟩
  intro n
  obtain ⟨C,hC,hb⟩ := (boundedSmoothOn_coleHopfTerminal ahi Vlo Vhi (max M 0)
    (halo.le.trans ha) hVlo hV (le_max_right _ _)).bound n
  refine ⟨C,hC,fun p hpa hpv hpg => hb p ⟨?_,hpv.1,hpv.2,?_⟩⟩
  · rw [Real.norm_of_nonneg (halo.le.trans hpa.1)]
    exact hpa.2
  · exact (norm_le_terminalSumNorm p.2).trans (hpg.trans (le_max_left _ _))

/-- The terminal-direction derivative formula also at zero variance. -/
theorem revised_one_step_terminal_derivative (a V : ℝ) (hV : 0 ≤ V)
    (g : TerminalSpace) :
    DifferentiableAt ℝ (fun h : TerminalSpace => coleHopfTerminal ((a,V),h)) g ∧
    ∀ k x, terminalValue (revisedColeHopfTerminalDerivative a V g k) x =
      ∫ y, terminalValue k y ∂FRSB.constantMassKernel a V.toNNReal (terminalValue g) x := by
  by_cases hv : 0 < V
  · exact ⟨((contDiffAt_coleHopfTerminal ((a,V),g) hv).comp g (by fun_prop)).differentiableAt
      (by simp),terminalValue_revisedColeHopfTerminalDerivative_kernel a V hv g⟩
  · have hz : V=0 := le_antisymm (le_of_not_gt hv) hV
    subst V
    have he : (fun h : TerminalSpace => coleHopfTerminal ((a,0),h)) = id := by funext h; simp
    refine ⟨by rw [he]; exact differentiableAt_id,fun k x => ?_⟩
    simp only [revisedColeHopfTerminalDerivative,he,fderiv_id,ContinuousLinearMap.id_apply,
      Real.toNNReal_zero,FRSB.constantMassKernel_zero_variance a (terminalValue g)
        (contDiff_terminalValue g).continuous (hasLinearGrowth_terminalValue g),
      Kernel.id_apply,integral_dirac]

/-- The zero-mass terminal operator is an actual bounded linear operator. -/
def revisedHeatTerminalCLM (V : ℝ) (hV : 0 ≤ V) : TerminalSpace →L[ℝ] TerminalSpace where
  toFun := fun g => coleHopfTerminal ((0,V),g)
  map_add' := by
    intro g h
    apply terminalValue_injective
    funext x
    rw [terminalValue_coleHopfTerminal_nonneg ((0,V),g+h) hV,
      terminalValue_add,terminalValue_coleHopfTerminal_nonneg ((0,V),g) hV,
      terminalValue_coleHopfTerminal_nonneg ((0,V),h) hV]
    simp_rw [coleHopf_zero,terminalValue_add]
    apply integral_add
    · exact ((hasLinearGrowth_terminalValue g).toHasExpGrowth.comp_add_const x).integrable_gaussianReal
        ((contDiff_terminalValue g).continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable
    · exact ((hasLinearGrowth_terminalValue h).toHasExpGrowth.comp_add_const x).integrable_gaussianReal
        ((contDiff_terminalValue h).continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable
  map_smul' := by
    intro c g
    apply terminalValue_injective
    funext x
    rw [terminalValue_coleHopfTerminal_nonneg ((0,V),c • g) hV,
      terminalValue_smul,terminalValue_coleHopfTerminal_nonneg ((0,V),g) hV]
    simp_rw [coleHopf_zero,terminalValue_smul]
    exact integral_const_mul c _
  cont := continuous_coleHopfTerminal.comp (by fun_prop)

/-- Both boundary operators are linear and bounded also in the exact sum
norm used in the paper. -/
theorem revised_one_step_boundary_linear (a V : ℝ) (hV : 0 ≤ V) :
    (∃ L : TerminalSpace →L[ℝ] TerminalSpace,
      (∀ g, L g = coleHopfTerminal ((0,V),g)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ g, terminalSumNorm (L g) ≤ C*terminalSumNorm g) ∧
    (∃ L : TerminalSpace →L[ℝ] TerminalSpace,
      ∀ g, L g = coleHopfTerminal ((a,0),g)) := by
  refine ⟨⟨revisedHeatTerminalCLM V hV,fun _ => rfl,
    4*‖revisedHeatTerminalCLM V hV‖,by positivity,?_⟩,
    ContinuousLinearMap.id ℝ TerminalSpace,?_⟩
  · intro g
    exact (terminalSumNorm_le_four_norm _).trans
      ((mul_le_mul_of_nonneg_left ((revisedHeatTerminalCLM V hV).le_opNorm g) (by norm_num)).trans
        (by nlinarith [norm_le_terminalSumNorm g,norm_nonneg (revisedHeatTerminalCLM V hV)]))
  · intro g
    simp

/-- The norm for a joint mass/variance/terminal direction, with the paper's
terminal sum norm. It dominates the inherited product max norm. -/
def revisedColeHopfParameterSumNorm (p : ColeHopfParameter) : ℝ :=
  |p.1.1|+|p.1.2|+terminalSumNorm p.2

theorem revised_norm_le_parameterSumNorm (p : ColeHopfParameter) :
    ‖p‖ ≤ revisedColeHopfParameterSumNorm p := by
  rw [Prod.norm_def,Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
  have ht := norm_le_terminalSumNorm p.2
  have hn := norm_nonneg p.2
  unfold revisedColeHopfParameterSumNorm
  apply max_le
  · apply max_le <;> nlinarith [abs_nonneg p.1.1,abs_nonneg p.1.2]
  · nlinarith [abs_nonneg p.1.1,abs_nonneg p.1.2]

/-- All joint derivatives are uniformly bounded as multilinear maps for
exact terminal sum norms; the constants depend only on the printed bounds
and order, and are chosen before the point and all directions. -/
theorem revised_one_step_sum_norm_bounds (alo ahi Vlo Vhi M : ℝ)
    (halo : 0 < alo) (ha : alo ≤ ahi) (hVlo : 0 < Vlo) (hV : Vlo ≤ Vhi)
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ColeHopfParameter,
      p.1.1 ∈ Icc alo ahi → p.1.2 ∈ Icc Vlo Vhi → terminalSumNorm p.2 ≤ M →
      ∀ v : Fin n → ColeHopfParameter,
        terminalSumNorm (iteratedFDeriv ℝ n coleHopfTerminal p v) ≤
          C*∏ i, revisedColeHopfParameterSumNorm (v i) := by
  obtain ⟨C,hC,hb⟩ := (revised_one_step_smooth_bounds alo ahi Vlo Vhi M halo ha hVlo hV).2 n
  refine ⟨4*C,by positivity,fun p hpa hpv hpg v => ?_⟩
  have hs : (∏ i, ‖v i‖) ≤ ∏ i, revisedColeHopfParameterSumNorm (v i) := Finset.prod_le_prod₀ (fun i _ => norm_nonneg (v i))
    (fun i _ => revised_norm_le_parameterSumNorm (v i))
  calc
    _ ≤ 4*‖iteratedFDeriv ℝ n coleHopfTerminal p v‖ := terminalSumNorm_le_four_norm _
    _ ≤ 4*(‖iteratedFDeriv ℝ n coleHopfTerminal p‖*∏ i,‖v i‖) :=
      mul_le_mul_of_nonneg_left (ContinuousMultilinearMap.le_opNorm _ _) (by norm_num)
    _ ≤ 4*(C*∏ i,revisedColeHopfParameterSumNorm (v i)) := by
      gcongr
      exact hb p hpa hpv hpg
    _ = (4*C)*∏ i,revisedColeHopfParameterSumNorm (v i) := by ring

end DepthPaper
