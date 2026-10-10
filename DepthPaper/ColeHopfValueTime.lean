module

public import DepthPaper.ColeHopfGradientTime

@[expose] public section


/-! The actual Cole–Hopf heat equation for arbitrary real mass and every
nonnegative variance, with a one-sided derivative at variance zero. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace DepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64
open ColeHopfFoundation.ProbabilityTheory

theorem hasDerivWithinAt_coleHopf_terminalValue_variance
    (a : ℝ) (g : TerminalSpace) (V : ℝ) (hV : 0 ≤ V) (x : ℝ) :
    HasDerivWithinAt (fun v : ℝ => coleHopf a v.toNNReal (terminalValue g) x)
      ((1/2:ℝ)*(boundaryGaussianJetTwo ((a,V),g) x+
        a*(boundaryGaussianJetOne ((a,V),g) x)^2)) (Ici 0) V := by
  by_cases ha : a = 0
  · subst a
    have hd := hasDerivWithinAt_gaussianHeat_variance_nonneg (terminalValue g)
      (terminalJet g 0) (terminalJet g 1)
      (hasDerivAt_terminalValue g) (hasDerivAt_terminalJet_zero g)
      (hasLinearGrowth_terminalValue g).toHasExpGrowth
      (hasExpGrowth_bcf (terminalJet g 0)) (hasExpGrowth_bcf (terminalJet g 1))
      (terminalJet g 1).continuous V hV x
    simp only [coleHopf_zero]
    apply hd.congr_deriv
    simp only [boundaryGaussianJetTwo,BoundedContinuousFunction.add_apply,
      BoundedContinuousFunction.smul_apply,smul_eq_mul,zero_mul,add_zero]
    rw [varianceGaussianTiltMean_apply_nonneg (fun g => terminalJet g 1)
      ((0,V),g) hV (uniformContinuous_terminalJet g 1) x]
    simp [uncenteredGaussianTiltMean]
  · let E := fun y => Real.exp (a*terminalValue g y)
    let B := terminalJet g 0
    let R := gaussianNormalizerHeatSource a g
    have hE (y : ℝ) : HasDerivAt E (a*B y*E y) y := by
      exact (((hasDerivAt_terminalValue g y).const_mul a).exp).congr_deriv
        (by dsimp [B,E]; ring)
    have hE' (y : ℝ) : HasDerivAt (fun z => a*B z*E z) (R y*E y) y := by
      convert! ((hasDerivAt_terminalJet_zero g y).const_mul a).mul (hE y) using 1
      dsimp [R,gaussianNormalizerHeatSource,B,E]
      ring
    have hEg : HasExpGrowth E := (hasLinearGrowth_terminalValue g).exp_mul a
    have hEc : Continuous E := Real.continuous_exp.comp
      (continuous_const.mul (contDiff_terminalValue g).continuous)
    have hd := hasDerivWithinAt_gaussianHeat_variance_nonneg E
      (fun y => a*B y*E y) (fun y => R y*E y) hE hE'
      hEg (((hasExpGrowth_bcf B).const_mul a).mul hEg) ((hasExpGrowth_bcf R).mul hEg)
      (R.continuous.mul hEc) V hV x
    have hp := integral_exp_mul_comp_add_pos (hasLinearGrowth_terminalValue g)
      (contDiff_terminalValue g).continuous.measurable a V.toNNReal x
    have he : (fun v : ℝ => coleHopf a v.toNNReal (terminalValue g) x) =
        (fun v => (1/a)*Real.log (∫z,E (x+z) ∂gaussianReal 0 v.toNNReal)) :=
      funext fun v => coleHopf_of_ne ha v.toNNReal (terminalValue g) x
    rw [he]
    apply ((hd.log hp.ne').const_mul (1/a)).congr_deriv
    have hc := varianceGaussianTiltMean_apply_nonneg (fun g => terminalJet g 1)
      ((a,V),g) hV (uniformContinuous_terminalJet g 1) x
    have hb := varianceGaussianTiltMean_apply_nonneg (fun g => terminalJet g 0^2)
      ((a,V),g) hV (uniformContinuous_bcf_pow _ (uniformContinuous_terminalJet g 0) 2) x
    simp only [boundaryGaussianJetTwo,BoundedContinuousFunction.add_apply,
      BoundedContinuousFunction.sub_apply,BoundedContinuousFunction.smul_apply,
      BoundedContinuousFunction.pow_apply,smul_eq_mul]
    rw [hc,hb]
    have hR : (∫z,R (x+z)*E (x+z) ∂gaussianReal 0 V.toNNReal) /
        (∫z,E (x+z) ∂gaussianReal 0 V.toNNReal) =
          a*uncenteredGaussianTiltMean a V.toNNReal g (terminalJet g 1) x+
            a^2*uncenteredGaussianTiltMean a V.toNNReal g (terminalJet g 0^2) x := by
      change uncenteredGaussianTiltMean a V.toNNReal g
        (a•terminalJet g 1+a^2•(terminalJet g 0^2)) x = _
      rw [uncenteredGaussianTiltMean_add,uncenteredGaussianTiltMean_smul,
        uncenteredGaussianTiltMean_smul]
    rw [mul_div_assoc,hR]
    field_simp [ha]
    <;> ring

theorem hasDerivWithinAt_coleHopfTerminal_value_variance
    (a : ℝ) (g : TerminalSpace) (V : ℝ) (hV : 0 ≤ V) (x : ℝ) :
    HasDerivWithinAt (fun v : ℝ => terminalValue (coleHopfTerminal ((a,v),g)) x)
      ((1/2:ℝ)*(terminalJet (coleHopfTerminal ((a,V),g)) 1 x+
        a*(terminalJet (coleHopfTerminal ((a,V),g)) 0 x)^2)) (Ici 0) V := by
  have hd := hasDerivWithinAt_coleHopf_terminalValue_variance a g V hV x
  have hfun : (fun v : ℝ => terminalValue (coleHopfTerminal ((a,v),g)) x)
      =ᶠ[𝓝[Ici 0] V] (fun v => coleHopf a v.toNNReal (terminalValue g) x) := by
    apply eventually_nhdsWithin_of_forall
    intro v hv
    exact terminalValue_coleHopfTerminal_nonneg ((a,v),g) hv x
  apply (hd.congr_of_eventuallyEq hfun
    (terminalValue_coleHopfTerminal_nonneg ((a,V),g) hV x)).congr_deriv
  simp [terminalJet_coleHopfTerminal_boundary ((a,V),g) hV]

end DepthPaper
