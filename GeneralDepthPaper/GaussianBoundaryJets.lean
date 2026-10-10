module

public import GeneralDepthPaper.ScaledGaussianIdentification
public import GeneralDepthPaper.ColeHopfSpatialJets

@[expose] public section


/-! Actual spatial Cole–Hopf moment formulas extended continuously through
zero variance. At variance zero the three jets are exactly the terminal jets. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000

def boundaryGaussianJetOne (p : ColeHopfParameter) : ℝ →ᵇ ℝ :=
  varianceGaussianTiltMean (fun g => terminalJet g 0) p

def boundaryGaussianJetTwo (p : ColeHopfParameter) : ℝ →ᵇ ℝ :=
  varianceGaussianTiltMean (fun g => terminalJet g 1) p +
    p.1.1 • (varianceGaussianTiltMean (fun g => terminalJet g 0^2) p - boundaryGaussianJetOne p^2)

def boundaryGaussianJetThree (p : ColeHopfParameter) : ℝ →ᵇ ℝ :=
  varianceGaussianTiltMean (fun g => terminalJet g 2) p +
    (3*p.1.1) • (varianceGaussianTiltMean (fun g => terminalJet g 0*terminalJet g 1) p -
      boundaryGaussianJetOne p*varianceGaussianTiltMean (fun g => terminalJet g 1) p) +
    p.1.1^2 • (varianceGaussianTiltMean (fun g => terminalJet g 0^3) p -
      (3:ℝ) • (boundaryGaussianJetOne p*varianceGaussianTiltMean (fun g => terminalJet g 0^2) p) +
      (2:ℝ) • boundaryGaussianJetOne p^3)

theorem continuous_boundaryGaussianJetOne : Continuous boundaryGaussianJetOne :=
  continuous_varianceGaussianTiltMean _ (terminalJetCLM 0).continuous
    (fun g => uniformContinuous_terminalJet g 0)

theorem continuous_boundaryGaussianJetTwo : Continuous boundaryGaussianJetTwo := by
  have h1 := continuous_varianceGaussianTiltMean _ (terminalJetCLM 1).continuous
    (fun g => uniformContinuous_terminalJet g 1)
  have h00 := continuous_varianceGaussianTiltMean _ ((terminalJetCLM 0).continuous.pow 2)
    (fun g => uniformContinuous_bcf_pow _ (uniformContinuous_terminalJet g 0) 2)
  exact h1.add ((continuous_fst.comp continuous_fst).smul
    (h00.sub (continuous_boundaryGaussianJetOne.pow 2)))

theorem continuous_boundaryGaussianJetThree : Continuous boundaryGaussianJetThree := by
  have h1 := continuous_varianceGaussianTiltMean _ (terminalJetCLM 1).continuous
    (fun g => uniformContinuous_terminalJet g 1)
  have h2 := continuous_varianceGaussianTiltMean _ (terminalJetCLM 2).continuous
    (fun g => uniformContinuous_terminalJet g 2)
  have h00 := continuous_varianceGaussianTiltMean _ ((terminalJetCLM 0).continuous.pow 2)
    (fun g => uniformContinuous_bcf_pow _ (uniformContinuous_terminalJet g 0) 2)
  have h000 := continuous_varianceGaussianTiltMean _ ((terminalJetCLM 0).continuous.pow 3)
    (fun g => uniformContinuous_bcf_pow _ (uniformContinuous_terminalJet g 0) 3)
  have h01 := continuous_varianceGaussianTiltMean _
    ((terminalJetCLM 0).continuous.mul (terminalJetCLM 1).continuous)
    (fun g => uniformContinuous_bcf_mul _ _ (uniformContinuous_terminalJet g 0)
      (uniformContinuous_terminalJet g 1))
  have ha : Continuous (fun p : ColeHopfParameter => p.1.1) := continuous_fst.comp continuous_fst
  exact (h2.add ((continuous_const.mul ha).smul
    (h01.sub (continuous_boundaryGaussianJetOne.mul h1)))).add
      ((ha.pow 2).smul ((h000.sub
        ((continuous_boundaryGaussianJetOne.mul h00).const_smul (3:ℝ))).add
          ((continuous_boundaryGaussianJetOne.pow 3).const_smul (2:ℝ))))

@[simp] theorem boundaryGaussianJetOne_zero (a : ℝ) (g : TerminalSpace) :
    boundaryGaussianJetOne ((a,0),g) = terminalJet g 0 := by
  simp [boundaryGaussianJetOne]

@[simp] theorem boundaryGaussianJetTwo_zero (a : ℝ) (g : TerminalSpace) :
    boundaryGaussianJetTwo ((a,0),g) = terminalJet g 1 := by
  simp [boundaryGaussianJetTwo]

@[simp] theorem boundaryGaussianJetThree_zero (a : ℝ) (g : TerminalSpace) :
    boundaryGaussianJetThree ((a,0),g) = terminalJet g 2 := by
  ext x
  simp only [boundaryGaussianJetThree,varianceGaussianTiltMean_zero,boundaryGaussianJetOne_zero,
    BoundedContinuousFunction.add_apply,BoundedContinuousFunction.sub_apply,
    BoundedContinuousFunction.mul_apply,BoundedContinuousFunction.smul_apply,
    BoundedContinuousFunction.pow_apply,smul_eq_mul]
  ring

theorem boundaryGaussianJetOne_eq (p : ColeHopfParameter) (hv : 0 < p.1.2) :
    boundaryGaussianJetOne p = terminalGaussianJetOne p := by
  rw [boundaryGaussianJetOne,varianceGaussianTiltMean_eq_actual _ p hv
    (uniformContinuous_terminalJet p.2 0)]
  simp only [gaussianTerminalTiltMean,shiftedGaussianObservable_jet,
    terminalGaussianJetOne,terminalGaussianMoment]

theorem boundaryGaussianJetTwo_eq (p : ColeHopfParameter) (hv : 0 < p.1.2) :
    boundaryGaussianJetTwo p = terminalGaussianJetTwo p := by
  rw [boundaryGaussianJetTwo,varianceGaussianTiltMean_eq_actual _ p hv
    (uniformContinuous_terminalJet p.2 1),varianceGaussianTiltMean_eq_actual _ p hv
      (uniformContinuous_bcf_pow _ (uniformContinuous_terminalJet p.2 0) 2),
    boundaryGaussianJetOne_eq p hv]
  simp only [gaussianTerminalTiltMean,shiftedGaussianObservable_pow,shiftedGaussianObservable_jet,
    terminalGaussianJetTwo,terminalGaussianMoment]

theorem boundaryGaussianJetThree_eq (p : ColeHopfParameter) (hv : 0 < p.1.2) :
    boundaryGaussianJetThree p = terminalGaussianJetThree p := by
  rw [boundaryGaussianJetThree,varianceGaussianTiltMean_eq_actual _ p hv
    (uniformContinuous_terminalJet p.2 2),varianceGaussianTiltMean_eq_actual _ p hv
      (uniformContinuous_bcf_mul _ _ (uniformContinuous_terminalJet p.2 0)
        (uniformContinuous_terminalJet p.2 1)),boundaryGaussianJetOne_eq p hv,
    varianceGaussianTiltMean_eq_actual _ p hv (uniformContinuous_terminalJet p.2 1),
    varianceGaussianTiltMean_eq_actual _ p hv
      (uniformContinuous_bcf_pow _ (uniformContinuous_terminalJet p.2 0) 3),
    varianceGaussianTiltMean_eq_actual _ p hv
      (uniformContinuous_bcf_pow _ (uniformContinuous_terminalJet p.2 0) 2)]
  simp only [gaussianTerminalTiltMean,shiftedGaussianObservable_pow,shiftedGaussianObservable_mul,
    shiftedGaussianObservable_jet,terminalGaussianJetThree,terminalGaussianMoment]

end GeneralDepthPaper
