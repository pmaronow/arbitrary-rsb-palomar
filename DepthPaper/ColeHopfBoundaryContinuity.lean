module

public import DepthPaper.GaussianBoundaryJets
public import DepthPaper.GaussianBoundaryValue
public import DepthPaper.ColeHopfTerminal

@[expose] public section


/-! Continuity in the complete terminal-function norm at variance zero. The
operator is the actual Cole–Hopf map at every mass, not a separate extension
with an assumed identification. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace DepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000
open ColeHopfFoundation.ProbabilityTheory

theorem varianceGaussianTiltMean_nonpos (H : TerminalSpace → ℝ →ᵇ ℝ)
    (p : ColeHopfParameter) (hv : p.1.2 ≤ 0) : varianceGaussianTiltMean H p = H p.2 := by
  rw [varianceGaussianTiltMean,Real.sqrt_eq_zero_of_nonpos hv]
  exact scaledGaussianTiltMean_zero _ _ _

theorem varianceGaussianCenteredValue_nonpos (p : ColeHopfParameter) (hv : p.1.2 ≤ 0) :
    varianceGaussianCenteredValue p = 0 := by
  rw [varianceGaussianCenteredValue,Real.sqrt_eq_zero_of_nonpos hv]
  exact scaledGaussianCenteredValue_zero _ _

theorem boundaryGaussianJetOne_nonpos (p : ColeHopfParameter) (hv : p.1.2 ≤ 0) :
    boundaryGaussianJetOne p = terminalJet p.2 0 := by
  exact varianceGaussianTiltMean_nonpos _ p hv

theorem boundaryGaussianJetTwo_nonpos (p : ColeHopfParameter) (hv : p.1.2 ≤ 0) :
    boundaryGaussianJetTwo p = terminalJet p.2 1 := by
  simp only [boundaryGaussianJetTwo,varianceGaussianTiltMean_nonpos _ p hv,
    boundaryGaussianJetOne_nonpos p hv,sub_self,smul_zero,add_zero]

theorem boundaryGaussianJetThree_nonpos (p : ColeHopfParameter) (hv : p.1.2 ≤ 0) :
    boundaryGaussianJetThree p = terminalJet p.2 2 := by
  ext x
  simp only [boundaryGaussianJetThree,varianceGaussianTiltMean_nonpos _ p hv,
    boundaryGaussianJetOne_nonpos p hv,BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.sub_apply,BoundedContinuousFunction.mul_apply,
    BoundedContinuousFunction.smul_apply,BoundedContinuousFunction.pow_apply,smul_eq_mul]
  ring

def boundaryCenteredJets (p : ColeHopfParameter) : Fin 3 → ℝ →ᵇ ℝ :=
  ![boundaryGaussianJetOne p-terminalJet p.2 0,
    boundaryGaussianJetTwo p-terminalJet p.2 1,
    boundaryGaussianJetThree p-terminalJet p.2 2]

def boundaryCenteredRaw (p : ColeHopfParameter) : TerminalJetData :=
  (varianceGaussianCenteredValue p 0,boundaryCenteredJets p)

theorem continuous_boundaryCenteredRaw : Continuous boundaryCenteredRaw := by
  have hv : Continuous (fun p : ColeHopfParameter => varianceGaussianCenteredValue p 0) :=
    (BoundedContinuousFunction.evalCLM ℝ (0:ℝ)).continuous.comp continuous_varianceGaussianCenteredValue
  have hj : Continuous boundaryCenteredJets := by
    apply continuous_pi
    intro i
    have hT (j : Fin 3) : Continuous (fun p : ColeHopfParameter => terminalJet p.2 j) :=
      (terminalJetCLM j).continuous.comp continuous_snd
    fin_cases i
    · exact continuous_boundaryGaussianJetOne.sub (hT 0)
    · exact continuous_boundaryGaussianJetTwo.sub (hT 1)
    · exact continuous_boundaryGaussianJetThree.sub (hT 2)
  exact hv.prodMk hj

theorem boundaryCenteredRaw_eq (p : ColeHopfParameter) :
    boundaryCenteredRaw p = (centeredColeHopfTerminal p : TerminalJetData) := by
  by_cases hv : 0 < p.1.2
  · rw [centeredColeHopfTerminal_raw p hv]
    apply Prod.ext
    · exact (varianceGaussianCenteredValue_apply p hv.le 0).trans
        (centeredColeHopfValue_apply p hv 0).symm
    · funext i
      fin_cases i <;> simp only [boundaryCenteredRaw,boundaryCenteredJets,centeredColeHopfJets,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
        boundaryGaussianJetOne_eq p hv,boundaryGaussianJetTwo_eq p hv,boundaryGaussianJetThree_eq p hv]
  · rw [centeredColeHopfTerminal,dif_neg hv]
    have hle := le_of_not_gt hv
    change (varianceGaussianCenteredValue p 0,boundaryCenteredJets p) = (0,0)
    apply Prod.ext
    · rw [varianceGaussianCenteredValue_nonpos p hle]
      rfl
    · funext i
      fin_cases i <;> simp [boundaryCenteredJets,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_two,boundaryGaussianJetOne_nonpos p hle,boundaryGaussianJetTwo_nonpos p hle,
        boundaryGaussianJetThree_nonpos p hle,sub_self,Pi.zero_apply]

theorem continuous_centeredColeHopfTerminal : Continuous centeredColeHopfTerminal := by
  have hm (p : ColeHopfParameter) : boundaryCenteredRaw p ∈ terminalJetSubmodule := by
    rw [boundaryCenteredRaw_eq]
    exact (centeredColeHopfTerminal p).property
  have h := continuous_boundaryCenteredRaw.subtype_mk hm
  convert! h using 1
  funext p
  exact Subtype.ext (boundaryCenteredRaw_eq p).symm

theorem terminalValue_centeredColeHopfTerminal_nonneg (p : ColeHopfParameter)
    (hv : 0 ≤ p.1.2) (x : ℝ) :
    terminalValue (centeredColeHopfTerminal p) x =
      coleHopf p.1.1 p.1.2.toNNReal (terminalValue p.2) x-terminalValue p.2 x := by
  by_cases hp : 0 < p.1.2
  · exact terminalValue_centeredColeHopfTerminal p hp x
  · have he : p.1.2 = 0 := le_antisymm (le_of_not_gt hp) hv
    rw [centeredColeHopfTerminal,dif_neg hp,terminalValue_zeroDatum,he]
    simp

end DepthPaper
