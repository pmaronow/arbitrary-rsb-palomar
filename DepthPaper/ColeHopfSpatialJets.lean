module

public import DepthPaper.GaussianTiltedSpatial

@[expose] public section


/-! The Gaussian moment polynomials are the genuine first three spatial
Cole–Hopf derivatives for the complete terminal-data Banach space. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace DepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000
open ColeHopfFoundation.ProbabilityTheory

@[simp] theorem gaussianTerminalTiltMean_add (p : ColeHopfParameter) (G H : ℝ →ᵇ ℝ) :
    gaussianTerminalTiltMean p (G+H)=gaussianTerminalTiltMean p G+gaussianTerminalTiltMean p H := by
  have he : shiftedGaussianObservable (G+H)=shiftedGaussianObservable G+shiftedGaussianObservable H := by
    ext t
    rfl
  unfold gaussianTerminalTiltMean
  rw [he,tiltedGaussianOperator_add]

@[simp] theorem gaussianTerminalTiltMean_smul (p : ColeHopfParameter) (c : ℝ) (G : ℝ →ᵇ ℝ) :
    gaussianTerminalTiltMean p (c•G)=c•gaussianTerminalTiltMean p G := by
  have he : shiftedGaussianObservable (c•G)=c•shiftedGaussianObservable G := by
    ext t
    rfl
  unfold gaussianTerminalTiltMean
  rw [he,tiltedGaussianOperator_smul]

@[simp] theorem shiftedGaussianObservable_mul (G H : ℝ →ᵇ ℝ) :
    shiftedGaussianObservable (G*H)=shiftedGaussianObservable G*shiftedGaussianObservable H := by ext s; rfl
@[simp] theorem shiftedGaussianObservable_pow (G : ℝ →ᵇ ℝ) (n : ℕ) :
    shiftedGaussianObservable (G^n)=(shiftedGaussianObservable G)^n := by ext s; rfl
@[simp] theorem shiftedGaussianObservable_jet (g : TerminalSpace) (i : Fin 3) :
    shiftedGaussianObservable (terminalJet g i)=shiftedTerminalJetCLM i g := by ext s; rfl

@[simp] theorem gaussianTerminalTiltMean_jet_zero (p : ColeHopfParameter) :
    gaussianTerminalTiltMean p (terminalJet p.2 0)=terminalGaussianJetOne p := rfl

theorem hasDerivAt_terminalGaussianJetOne (p : ColeHopfParameter) (hv : 0<p.1.2) (x : ℝ) :
    HasDerivAt (terminalGaussianJetOne p) (terminalGaussianJetTwo p x) x := by
  have H := hasDerivAt_gaussianTerminalTiltMean p hv (terminalJet p.2 0) (terminalJet p.2 1)
    (hasDerivAt_terminalJet_zero p.2) x
  rw [gaussianTerminalTiltMean_jet_zero] at H
  apply H.congr_deriv
  rw [gaussianTerminalTiltMean_add,gaussianTerminalTiltMean_smul]
  change gaussianTerminalTiltMean p (terminalJet p.2 1) x+
    p.1.1*gaussianTerminalTiltMean p (terminalJet p.2 0*terminalJet p.2 0) x-
    p.1.1*terminalGaussianJetOne p x*terminalGaussianJetOne p x=terminalGaussianJetTwo p x
  simp only [terminalGaussianJetTwo,terminalGaussianMoment,pow_two,gaussianTerminalTiltMean,
    shiftedGaussianObservable_mul,shiftedGaussianObservable_jet,BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.smul_apply,BoundedContinuousFunction.sub_apply,
    BoundedContinuousFunction.mul_apply,smul_eq_mul]
  ring

theorem hasDerivAt_coleHopf_terminalValue (p : ColeHopfParameter) (hv : 0<p.1.2) (x : ℝ) :
    HasDerivAt (coleHopf p.1.1 p.1.2.toNNReal (terminalValue p.2)) (terminalGaussianJetOne p x) x := by
  have hA := hasDerivAt_terminalValue p.2
  have hg := hasLinearGrowth_terminalValue p.2
  have hJg := hasExpGrowth_bcf (terminalJet p.2 0)
  have hJm := (terminalJet p.2 0).continuous.measurable
  by_cases ha : p.1.1=0
  · have hd := hasDerivAt_integral_comp_add_gaussianReal hA hg.toHasExpGrowth hJg hJm 0 p.1.2.toNNReal x
    have he := gaussianTerminalTiltMean_apply p (terminalJet p.2 0) hv x
    rw [gaussianTerminalTiltMean_jet_zero] at he
    simp [ha,uncenteredGaussianTiltMean] at he
    have hf : coleHopf p.1.1 p.1.2.toNNReal (terminalValue p.2)=
        fun y=>∫d,terminalValue p.2 (y+d) ∂gaussianReal 0 p.1.2.toNNReal := by
      rw [ha]
      funext y
      exact coleHopf_zero _ _ y
    rw [hf,he]
    exact hd
  · have hd := hasDerivAt_coleHopf hA hg hJg hJm ha p.1.2.toNNReal x
    apply hd.congr_deriv
    rw [←gaussianTerminalTiltMean_jet_zero,gaussianTerminalTiltMean_apply p _ hv x]
    unfold uncenteredGaussianTiltMean
    rw [←integral_div]
    apply integral_congr_ae
    exact .of_forall fun d=>by
      dsimp only
      rw [coleHopfQ_eq hg (contDiff_terminalValue p.2).continuous.measurable ha]
      ring

theorem hasDerivAt_terminalGaussianJetTwo (p : ColeHopfParameter) (hv : 0<p.1.2) (x : ℝ) :
    HasDerivAt (terminalGaussianJetTwo p) (terminalGaussianJetThree p x) x := by
  let B := terminalJet p.2 0
  let C := terminalJet p.2 1
  let D := terminalJet p.2 2
  have hB := hasDerivAt_terminalJet_zero p.2
  have hC := hasDerivAt_terminalJet_one p.2
  have hSq (y : ℝ) : HasDerivAt (fun z:ℝ=>(B z)^2) (((2:ℝ)•(B*C)) y) y := by
    convert! (hB y).pow 2 using 1
    simp only [BoundedContinuousFunction.coe_smul,Pi.smul_apply,smul_eq_mul,
      BoundedContinuousFunction.coe_mul,Pi.mul_apply]
    ring
  have H1 := hasDerivAt_gaussianTerminalTiltMean p hv C D hC x
  have H2 := hasDerivAt_gaussianTerminalTiltMean p hv (B^2) ((2:ℝ)•(B*C)) hSq x
  have H0 := hasDerivAt_terminalGaussianJetOne p hv x
  have H := H1.add ((H2.sub (H0.pow 2)).const_mul p.1.1)
  have he : (fun y=>gaussianTerminalTiltMean p C y+
      p.1.1*(gaussianTerminalTiltMean p (B^2) y-(terminalGaussianJetOne p y)^2))=
      (terminalGaussianJetTwo p : ℝ→ℝ) := rfl
  change HasDerivAt (fun y=>gaussianTerminalTiltMean p C y+
    p.1.1*(gaussianTerminalTiltMean p (B^2) y-(terminalGaussianJetOne p y)^2)) _ x at H
  rw [he] at H
  apply H.congr_deriv
  rw [gaussianTerminalTiltMean_add,gaussianTerminalTiltMean_smul,
    gaussianTerminalTiltMean_add,gaussianTerminalTiltMean_smul,gaussianTerminalTiltMean_smul]
  simp only [BoundedContinuousFunction.coe_add,Pi.add_apply,BoundedContinuousFunction.coe_smul,
    Pi.smul_apply,smul_eq_mul,gaussianTerminalTiltMean_jet_zero,pow_one,one_mul]
  norm_num only [Nat.reduceSub,Nat.cast_ofNat,pow_one]
  change gaussianTerminalTiltMean p D x+p.1.1*gaussianTerminalTiltMean p (C*B) x-
    p.1.1*gaussianTerminalTiltMean p C x*terminalGaussianJetOne p x+
    p.1.1*(2*gaussianTerminalTiltMean p (B*C) x+p.1.1*gaussianTerminalTiltMean p (B^2*B) x-
      p.1.1*gaussianTerminalTiltMean p (B^2) x*terminalGaussianJetOne p x-
      2*terminalGaussianJetOne p x*terminalGaussianJetTwo p x)=terminalGaussianJetThree p x
  have hCB : C*B=B*C := mul_comm _ _
  have hBB : B^2*B=B^3 := (pow_succ B 2).symm
  rw [hCB,hBB]
  simp only [terminalGaussianJetTwo,terminalGaussianJetThree,terminalGaussianMoment,
    B,C,D,gaussianTerminalTiltMean,shiftedGaussianObservable_mul,shiftedGaussianObservable_pow,
    shiftedGaussianObservable_jet,BoundedContinuousFunction.add_apply,BoundedContinuousFunction.smul_apply,
    BoundedContinuousFunction.sub_apply,BoundedContinuousFunction.mul_apply,BoundedContinuousFunction.pow_apply,smul_eq_mul]
  ring

theorem hasDerivAt_centeredColeHopfValue_spatial (p : ColeHopfParameter) (hv : 0<p.1.2) (x : ℝ) :
    HasDerivAt (centeredColeHopfValue p)
      (terminalGaussianJetOne p x-terminalJet p.2 0 x) x := by
  have hd := (hasDerivAt_coleHopf_terminalValue p hv x).sub (hasDerivAt_terminalValue p.2 x)
  have he : (fun y=>coleHopf p.1.1 p.1.2.toNNReal (terminalValue p.2) y-terminalValue p.2 y)=
      (centeredColeHopfValue p : ℝ→ℝ) :=
    funext fun y=>(centeredColeHopfValue_apply p hv y).symm
  exact he ▸ hd

end DepthPaper
