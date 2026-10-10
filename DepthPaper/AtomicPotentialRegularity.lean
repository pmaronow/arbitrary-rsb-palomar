module

public import DepthPaper.AtomicCorrection
public import DepthPaper.ColeHopfChain
public import DepthPaper.LogCoshTerminal
public import DepthPaper.Nondegeneracy

@[expose] public section


/-! The explicit smooth Gaussian recursion is identified with the actual
mixed-model Parisi potential and functional on the open atomic chart. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff BoundedContinuousFunction
namespace DepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000

 def atomicPotentialRecursion (Ξ:AdmissibleCovariance) {r:ℕ} (z:AtomicPoint r) : TerminalSpace :=
   coleHopfRecursion (r+1) (atomicRecursionData Ξ z,logCoshTerminal)

theorem potential_atomicMeasure_eq_recursion (Ξ:AdmissibleCovariance) {r:ℕ}
    (z:AtomicPoint r) (hz:IsAtomicPoint z) (x:ℝ) :
    potential Ξ (atomicMeasure z hz) 0 x=terminalValue (atomicPotentialRecursion Ξ z) x := by
  have H := coleHopf_chain_eq_recursion (r+1) (atomicRecursionData Ξ z) logCoshTerminal
    (fun i x=>FourPapersCommon.mixedPotential Ξ.toEvenMixture (atomicMeasure z hz) (atomicNode z i,x))
    (atomicRecursionData_variance_pos Ξ z hz)
    (fun x=>by rw [atomicNode_last,FourPapersCommon.mixedPotential_terminal,terminalValue_logCoshTerminal])
    (mixedPotential_atomic_step Ξ z hz) x
  simpa only [atomicNode_zero,potential,atomicPotentialRecursion] using H

def atomicFunctionalRecursion (Ξ:AdmissibleCovariance) {r:ℕ} (z:AtomicPoint r) : ℝ :=
  Real.log 2+terminalValue (atomicPotentialRecursion Ξ z) 0-(1/2:ℝ)*atomicCorrection Ξ z

theorem atomicFunctional_eq_recursion (Ξ:AdmissibleCovariance) {r:ℕ}
    (z:AtomicPoint r) (hz:IsAtomicPoint z) :
    parisiFunctional Ξ (atomicMeasure z hz)=atomicFunctionalRecursion Ξ z := by
  rw [parisiFunctional_eq,potential_atomicMeasure_eq_recursion Ξ z hz,
    ←atomicCorrection_eq_integral Ξ z hz]
  rfl

theorem contDiff_atomicLocation {r:ℕ} (i:Fin (r+1)) :
    ContDiff ℝ ∞ (fun z:AtomicPoint r=>atomicLocation z i) := by
  refine Fin.cases ?_ (fun j=>?_) i
  · exact contDiff_const
  · exact contDiff_apply ℝ ℝ j |>.comp contDiff_fst

theorem contDiff_atomicWeight {r:ℕ} (i:Fin (r+1)) :
    ContDiff ℝ ∞ (fun z:AtomicPoint r=>atomicWeight z i) := by
  refine Fin.lastCases ?_ (fun j=>?_) i
  · simp only [atomicWeight_last]
    change ContDiff ℝ ∞ (fun z:AtomicPoint r=>1-∑j:Fin r,z.2 j)
    exact contDiff_const.sub (ContDiff.sum fun j _=> (contDiff_apply ℝ ℝ j).comp contDiff_snd)
  · simpa only [atomicWeight_castSucc,Function.comp_def] using (contDiff_apply ℝ ℝ j).comp (contDiff_snd (E:=Fin r→ℝ))

theorem contDiff_atomicNode {r:ℕ} (i:Fin (r+2)) :
    ContDiff ℝ ∞ (fun z:AtomicPoint r=>atomicNode z i) := by
  refine Fin.lastCases ?_ (fun j=>?_) i
  · simp only [atomicNode_last]
    change ContDiff ℝ ∞ (fun _:AtomicPoint r=>(1:ℝ))
    exact contDiff_const
  · simpa only [atomicNode_castSucc] using contDiff_atomicLocation j

theorem contDiff_atomicLevel {r:ℕ} (i:Fin (r+1)) :
    ContDiff ℝ ∞ (fun z:AtomicPoint r=>atomicLevel z i) := by
  apply ContDiff.sum
  intro j _
  by_cases h:j ≤ i
  · simpa only [if_pos h] using contDiff_atomicWeight j
  · simp only [if_neg h]
    exact contDiff_const

theorem AdmissibleCovariance.contDiff_first (Ξ:AdmissibleCovariance) : ContDiff ℝ ∞ Ξ.first := by
  apply ContDiff.sum
  intro p _
  exact contDiff_const.mul (contDiff_id.pow (p-1))

theorem AdmissibleCovariance.contDiff_value (Ξ:AdmissibleCovariance) : ContDiff ℝ ∞ Ξ.value := by
  apply ContDiff.sum
  intro p _
  exact contDiff_const.mul (contDiff_id.pow p)

theorem contDiff_atomicRecursionData (Ξ:AdmissibleCovariance) (r:ℕ) :
    ContDiff ℝ ∞ (atomicRecursionData Ξ (r:=r)) := by
  rw [contDiff_pi]
  intro i
  exact (contDiff_atomicLevel i).prodMk
    ((Ξ.contDiff_first.comp (contDiff_atomicNode i.succ)).sub
      (Ξ.contDiff_first.comp (contDiff_atomicNode i.castSucc)))

theorem contDiffAt_atomicPotentialRecursion (Ξ:AdmissibleCovariance) {r:ℕ}
    (z:AtomicPoint r) (hz:IsAtomicPoint z) : ContDiffAt ℝ ∞ (atomicPotentialRecursion Ξ) z :=
  (contDiffAt_coleHopfRecursion (r+1) (atomicRecursionData Ξ z,logCoshTerminal)
    (atomicRecursionData_variance_pos Ξ z hz)).comp z
      ((contDiff_atomicRecursionData Ξ r).contDiffAt.prodMk contDiffAt_const)

theorem contDiff_atomicCorrection (Ξ:AdmissibleCovariance) (r:ℕ) :
    ContDiff ℝ ∞ (atomicCorrection Ξ (r:=r)) := by
  apply ContDiff.sum
  intro i _
  have hp : ContDiff ℝ ∞ (covarianceCorrectionPrimitive Ξ) :=
    (contDiff_id.mul Ξ.contDiff_first).sub Ξ.contDiff_value
  exact (contDiff_atomicWeight i).mul (contDiff_const.sub (hp.comp (contDiff_atomicLocation i)))

theorem contDiffAt_atomicFunctionalRecursion (Ξ:AdmissibleCovariance) {r:ℕ}
    (z:AtomicPoint r) (hz:IsAtomicPoint z) : ContDiffAt ℝ ∞ (atomicFunctionalRecursion Ξ) z := by
  have hval : ContDiffAt ℝ ∞ (fun y:AtomicPoint r=>terminalValue (atomicPotentialRecursion Ξ y) 0) z := by
    let h := (ContinuousLinearMap.fst ℝ ℝ (Fin 3→ℝ →ᵇ ℝ)).comp terminalJetSubmodule.subtypeL
    simp only [terminalValue_zero]
    convert! h.contDiff.contDiffAt.comp z (contDiffAt_atomicPotentialRecursion Ξ z hz) using 1
  exact (contDiffAt_const.add hval).sub
    (contDiffAt_const.mul (contDiff_atomicCorrection Ξ r).contDiffAt)

theorem contDiffAt_atomicFunctionalExtension (Ξ:AdmissibleCovariance) {r:ℕ}
    (z:AtomicPoint r) (hz:IsAtomicPoint z) : ContDiffAt ℝ ∞ (atomicFunctionalExtension Ξ r) z := by
  apply (contDiffAt_atomicFunctionalRecursion Ξ z hz).congr_of_eventuallyEq
  filter_upwards [(isOpen_atomic_domain r).mem_nhds hz] with y hy
  rw [atomicFunctionalExtension_eq Ξ y hy,atomicFunctional_eq_recursion Ξ y hy]

end DepthPaper
