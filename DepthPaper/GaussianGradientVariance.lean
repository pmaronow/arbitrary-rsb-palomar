module

public import DepthPaper.GaussianVarianceHeat

@[expose] public section


/-! Variance differentiation of the actual first Cole–Hopf spatial derivative.
The normalized heat ratio treats zero mass directly and is valid at variance
zero as a one-sided derivative. Only the three prescribed terminal jets enter. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace DepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000
open ColeHopfFoundation.ProbabilityTheory

def gaussianGradientHeatSource (a : ℝ) (g : TerminalSpace) : ℝ →ᵇ ℝ :=
  terminalJet g 2+(3*a)•(terminalJet g 0*terminalJet g 1)+a^2•(terminalJet g 0^3)

def gaussianNormalizerHeatSource (a : ℝ) (g : TerminalSpace) : ℝ →ᵇ ℝ :=
  a•terminalJet g 1+a^2•(terminalJet g 0^2)

theorem hasDerivWithinAt_uncenteredGaussianGradient_variance
    (a : ℝ) (g : TerminalSpace) (V : ℝ) (hV : 0 ≤ V) (x : ℝ) :
    HasDerivWithinAt (fun v : ℝ =>
      uncenteredGaussianTiltMean a v.toNNReal g (terminalJet g 0) x)
      ((1/2:ℝ)*(uncenteredGaussianTiltMean a V.toNNReal g (gaussianGradientHeatSource a g) x-
        uncenteredGaussianTiltMean a V.toNNReal g (terminalJet g 0) x*
          uncenteredGaussianTiltMean a V.toNNReal g (gaussianNormalizerHeatSource a g) x))
      (Ici 0) V := by
  let B := terminalJet g 0
  let C := terminalJet g 1
  let D := terminalJet g 2
  let E := fun y => Real.exp (a*terminalValue g y)
  let R := gaussianNormalizerHeatSource a g
  let S := gaussianGradientHeatSource a g
  let N' : ℝ →ᵇ ℝ := C+a•(B^2)
  have hE (y : ℝ) : HasDerivAt E (a*B y*E y) y := by
    exact (((hasDerivAt_terminalValue g y).const_mul a).exp).congr_deriv (by dsimp [B,E]; ring)
  have hE' (y : ℝ) : HasDerivAt (fun z => a*B z*E z) (R y*E y) y := by
    convert! ((hasDerivAt_terminalJet_zero g y).const_mul a).mul (hE y) using 1
    dsimp [R,gaussianNormalizerHeatSource,B,C,E]
    try simp only [BoundedContinuousFunction.add_apply,BoundedContinuousFunction.smul_apply,
      BoundedContinuousFunction.pow_apply,smul_eq_mul]
    ring
  have hN (y : ℝ) : HasDerivAt (fun z => B z*E z) (N' y*E y) y := by
    convert! (hasDerivAt_terminalJet_zero g y).mul (hE y) using 1
    dsimp [N',B,C,E]
    try simp only [BoundedContinuousFunction.add_apply,BoundedContinuousFunction.smul_apply,
      BoundedContinuousFunction.pow_apply,smul_eq_mul]
    ring
  have hNp (y : ℝ) : HasDerivAt N' (D y+2*a*B y*C y) y := by
    convert! (hasDerivAt_terminalJet_one g y).add
      (((hasDerivAt_terminalJet_zero g y).pow 2).const_mul a) using 1
    dsimp [B,C,D]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one]
    ring
  have hN' (y : ℝ) : HasDerivAt (fun z => N' z*E z) (S y*E y) y := by
    convert! (hNp y).mul (hE y) using 1
    dsimp [S,N',gaussianGradientHeatSource,B,C,D,E]
    try simp only [BoundedContinuousFunction.add_apply,BoundedContinuousFunction.smul_apply,
      BoundedContinuousFunction.pow_apply,BoundedContinuousFunction.mul_apply,smul_eq_mul]
    ring
  have hEg : HasExpGrowth E := (hasLinearGrowth_terminalValue g).exp_mul a
  have hEc : Continuous E := Real.continuous_exp.comp
    (continuous_const.mul (contDiff_terminalValue g).continuous)
  have hDp := hasDerivWithinAt_gaussianHeat_variance_nonneg E
    (fun y => a*B y*E y) (fun y => R y*E y) hE hE'
    hEg (((hasExpGrowth_bcf B).const_mul a).mul hEg) ((hasExpGrowth_bcf R).mul hEg)
    (R.continuous.mul hEc) V hV x
  have hNp' := hasDerivWithinAt_gaussianHeat_variance_nonneg
    (fun y => B y*E y) (fun y => N' y*E y) (fun y => S y*E y) hN hN'
    ((hasExpGrowth_bcf B).mul hEg) ((hasExpGrowth_bcf N').mul hEg)
    ((hasExpGrowth_bcf S).mul hEg) (S.continuous.mul hEc) V hV x
  have hp := integral_exp_mul_comp_add_pos (hasLinearGrowth_terminalValue g)
    (contDiff_terminalValue g).continuous.measurable a V.toNNReal x
  apply (hNp'.div hDp hp.ne').congr_deriv
  unfold uncenteredGaussianTiltMean
  dsimp only [B,E,R,S]
  field_simp [hp.ne']
  <;> ring

theorem hasDerivWithinAt_boundaryGaussianJetOne_variance
    (a : ℝ) (g : TerminalSpace) (V : ℝ) (hV : 0 ≤ V) (x : ℝ) :
    HasDerivWithinAt (fun v : ℝ => boundaryGaussianJetOne ((a,v),g) x)
      ((1/2:ℝ)*(boundaryGaussianJetThree ((a,V),g) x+
        2*a*boundaryGaussianJetOne ((a,V),g) x*boundaryGaussianJetTwo ((a,V),g) x))
      (Ici 0) V := by
  have hfun : (fun v : ℝ => boundaryGaussianJetOne ((a,v),g) x) =ᶠ[𝓝[Ici 0] V]
      (fun v : ℝ => uncenteredGaussianTiltMean a v.toNNReal g (terminalJet g 0) x) := by
    apply eventually_nhdsWithin_of_forall
    intro v hv
    exact varianceGaussianTiltMean_apply_nonneg _ ((a,v),g) hv (uniformContinuous_terminalJet g 0) x
  have hd := hasDerivWithinAt_uncenteredGaussianGradient_variance a g V hV x
  have he := varianceGaussianTiltMean_apply_nonneg (fun g => terminalJet g 0)
    ((a,V),g) hV (uniformContinuous_terminalJet g 0) x
  apply (hd.congr_of_eventuallyEq hfun he).congr_deriv
  rw [gaussianGradientHeatSource,gaussianNormalizerHeatSource]
  simp only [uncenteredGaussianTiltMean_add,uncenteredGaussianTiltMean_smul]
  have hm (H : TerminalSpace → ℝ →ᵇ ℝ) (hU : UniformContinuous (H g)) :=
    varianceGaussianTiltMean_apply_nonneg H ((a,V),g) hV hU x
  simp only [boundaryGaussianJetThree,boundaryGaussianJetTwo,boundaryGaussianJetOne,
    BoundedContinuousFunction.add_apply,BoundedContinuousFunction.sub_apply,
    BoundedContinuousFunction.smul_apply,BoundedContinuousFunction.mul_apply,
    BoundedContinuousFunction.pow_apply,smul_eq_mul]
  rw [hm (fun g => terminalJet g 0) (uniformContinuous_terminalJet g 0),
    hm (fun g => terminalJet g 1) (uniformContinuous_terminalJet g 1),
    hm (fun g => terminalJet g 2) (uniformContinuous_terminalJet g 2),
    hm (fun g => terminalJet g 0*terminalJet g 1)
      (uniformContinuous_bcf_mul _ _ (uniformContinuous_terminalJet g 0) (uniformContinuous_terminalJet g 1)),
    hm (fun g => terminalJet g 0^2) (uniformContinuous_bcf_pow _ (uniformContinuous_terminalJet g 0) 2),
    hm (fun g => terminalJet g 0^3) (uniformContinuous_bcf_pow _ (uniformContinuous_terminalJet g 0) 3)]
  ring

end DepthPaper
