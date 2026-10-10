module

public import DepthPaper.TerminalGaussianJets
public import DepthPaper.GaussianTiltedLinear

@[expose] public section


/-! Spatial differentiation of actual normalized Gaussian observables, with
arbitrary bounded terminal jets and every real mass, including zero. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace DepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000
open ColeHopfFoundation.ProbabilityTheory

def shiftedGaussianObservable (G : ℝ →ᵇ ℝ) : GaussianObservable :=
  G.compContinuous ⟨fun s:ℝ×ℝ=>s.2+s.1,by fun_prop⟩

@[simp] theorem shiftedGaussianObservable_apply (G : ℝ →ᵇ ℝ) (d x : ℝ) :
    shiftedGaussianObservable G (d,x)=G (x+d) := rfl

def gaussianTerminalTiltMean (p : ColeHopfParameter) (G : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  tiltedGaussianOperator (p,shiftedGaussianObservable G)

def uncenteredGaussianTiltMean (a : ℝ) (v : ℝ≥0) (g : TerminalSpace) (G : ℝ →ᵇ ℝ) (x : ℝ) : ℝ :=
  (∫d,G (x+d)*Real.exp (a*terminalValue g (x+d)) ∂gaussianReal 0 v)/
    (∫d,Real.exp (a*terminalValue g (x+d)) ∂gaussianReal 0 v)

theorem hasExpGrowth_bcf (G : ℝ →ᵇ ℝ) : HasExpGrowth G :=
  HasExpGrowth.of_bounded fun x=>by simpa only [Real.norm_eq_abs] using G.norm_coe_le_norm x

theorem gaussianTerminalTiltMean_apply (p : ColeHopfParameter) (G : ℝ →ᵇ ℝ)
    (hv : 0<p.1.2) (x : ℝ) :
    gaussianTerminalTiltMean p G x=uncenteredGaussianTiltMean p.1.1 p.1.2.toNNReal p.2 G x := by
  rw [gaussianTerminalTiltMean,tiltedGaussianOperator_apply _ hv]
  simp only [shiftedGaussianObservable_apply]
  let c := Real.exp (-p.1.1*terminalValue p.2 x)
  have hc : c≠0 := (Real.exp_pos _).ne'
  have hn : (∫d,Real.exp (p.1.1*(terminalValue p.2 (x+d)-terminalValue p.2 x))*G (x+d)
      ∂gaussianReal 0 p.1.2.toNNReal)=c*(∫d,G (x+d)*Real.exp (p.1.1*terminalValue p.2 (x+d))
      ∂gaussianReal 0 p.1.2.toNNReal) := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    exact .of_forall fun d=>by
      dsimp [c]
      have he : p.1.1*(terminalValue p.2 (x+d)-terminalValue p.2 x)=
        -p.1.1*terminalValue p.2 x+p.1.1*terminalValue p.2 (x+d) := by ring
      rw [he,Real.exp_add]
      ring
  have hd : (∫d,Real.exp (p.1.1*(terminalValue p.2 (x+d)-terminalValue p.2 x))
      ∂gaussianReal 0 p.1.2.toNNReal)=c*(∫d,Real.exp (p.1.1*terminalValue p.2 (x+d))
      ∂gaussianReal 0 p.1.2.toNNReal) := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    exact .of_forall fun d=>by
      dsimp [c]
      rw [←Real.exp_add]
      congr 1
      ring
  rw [hn,hd]
  exact mul_div_mul_left _ _ hc

theorem hasDerivAt_uncenteredGaussianTiltMean (a : ℝ) (v : ℝ≥0) (g : TerminalSpace)
    (G G' : ℝ →ᵇ ℝ) (hG : ∀x,HasDerivAt G (G' x) x) (x : ℝ) :
    HasDerivAt (uncenteredGaussianTiltMean a v g G)
      (uncenteredGaussianTiltMean a v g (G'+a•(G*terminalJet g 0)) x-
        a*uncenteredGaussianTiltMean a v g G x*
          uncenteredGaussianTiltMean a v g (terminalJet g 0) x) x := by
  let A := terminalValue g
  let A' := terminalJet g 0
  have hA : ∀y,HasDerivAt A (A' y) y := hasDerivAt_terminalValue g
  have hg : HasLinearGrowth A := hasLinearGrowth_terminalValue g
  have hpoly : HasExpGrowth (fun y=>G' y+a*G y*A' y) :=
    (hasExpGrowth_bcf G').add (((hasExpGrowth_bcf G).const_mul a).mul (hasExpGrowth_bcf A'))
  have hnum := hasDerivAt_integral_comp_add_gaussianReal
    (F:=fun y=>G y*Real.exp (a*A y))
    (F':=fun y=>(G' y+a*G y*A' y)*Real.exp (a*A y))
    (fun y=>by
      convert! (hG y).mul (((hA y).const_mul a).exp) using 1
      ring)
    ((hasExpGrowth_bcf G).mul (hg.exp_mul a))
    (hpoly.mul (hg.exp_mul a))
    (((G'.continuous.measurable.add ((G.continuous.measurable.const_mul a).mul A'.continuous.measurable))).mul
      (Real.measurable_exp.comp ((contDiff_terminalValue g).continuous.measurable.const_mul a))) 0 v x
  have hden := hasDerivAt_integral_exp_mul hA hg (hasExpGrowth_bcf A') A'.continuous.measurable a v x
  have hp := integral_exp_mul_comp_add_pos hg (contDiff_terminalValue g).continuous.measurable a v x
  have hd : (∫d,a*A' (x+d)*Real.exp (a*A (x+d)) ∂gaussianReal 0 v)=
      a*(∫d,A' (x+d)*Real.exp (a*A (x+d)) ∂gaussianReal 0 v) := by
    simpa only [mul_assoc] using integral_const_mul a
      (fun d=>A' (x+d)*Real.exp (a*A (x+d)))
  rw [hd] at hden
  convert! hnum.div hden hp.ne' using 1
  · unfold uncenteredGaussianTiltMean
    dsimp only [A,A']
    simp only [BoundedContinuousFunction.coe_add,Pi.add_apply,BoundedContinuousFunction.coe_smul,
      Pi.smul_apply,smul_eq_mul,BoundedContinuousFunction.coe_mul,Pi.mul_apply]
    field_simp [hp.ne']

theorem hasDerivAt_gaussianTerminalTiltMean (p : ColeHopfParameter) (hv : 0<p.1.2)
    (G G' : ℝ →ᵇ ℝ) (hG : ∀x,HasDerivAt G (G' x) x) (x : ℝ) :
    HasDerivAt (gaussianTerminalTiltMean p G)
      (gaussianTerminalTiltMean p (G'+p.1.1•(G*terminalJet p.2 0)) x-
        p.1.1*gaussianTerminalTiltMean p G x*gaussianTerminalTiltMean p (terminalJet p.2 0) x) x := by
  have he (J : ℝ →ᵇ ℝ) : (gaussianTerminalTiltMean p J : ℝ→ℝ)=
      uncenteredGaussianTiltMean p.1.1 p.1.2.toNNReal p.2 J :=
    funext (gaussianTerminalTiltMean_apply p J hv)
  simp_rw [he]
  exact hasDerivAt_uncenteredGaussianTiltMean _ _ _ G G' hG x

end DepthPaper
