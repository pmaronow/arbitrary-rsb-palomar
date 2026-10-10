module

public import DepthPaper.RevisedOrigin
public import DepthPaper.AtomicPotentialRegularity
public import FourPapersCommon.WeightedCDF

@[expose] public section

/-! Actual finite atomic Parisi functional and smooth Gaussian recursion for
all finite positive even covariances, including quadratic interactions. The
old positive atomic coordinate chart is reused without changing its measure. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff BoundedContinuousFunction
namespace DepthPaper.RevisedCovariance
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 1000000

def atomicFunctional (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) : ℝ := parisiFunctional Ξ (atomicMeasure z hz)

def atomicFunctionalExtension (Ξ : RevisedCovariance) (r : ℕ) (z : AtomicPoint r) : ℝ :=
  @dite ℝ (IsAtomicPoint z) (Classical.propDecidable _)
    (fun hz => atomicFunctional Ξ z hz) (fun _ => 0)

theorem atomicFunctionalExtension_eq (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) :
    atomicFunctionalExtension Ξ r z=parisiFunctional Ξ (atomicMeasure z hz) := by
  simp only [atomicFunctionalExtension,dif_pos hz,atomicFunctional]

def atomicRecursionData (Ξ:RevisedCovariance) {r:ℕ} (z:AtomicPoint r) : Fin (r+1)→ℝ×ℝ :=
  fun i=>(atomicLevel z i,Ξ.first (atomicNode z i.succ)-Ξ.first (atomicNode z i.castSucc))

theorem atomicRecursionData_variance_pos (Ξ:RevisedCovariance) {r:ℕ}
    (z:AtomicPoint r) (hz:IsAtomicPoint z) (i:Fin (r+1)) : 0<(atomicRecursionData Ξ z i).2 := by
  exact sub_pos.mpr (Ξ.first_strictMonoOn (atomicNode_mem_unit z hz i.castSucc).1
    (atomicNode_mem_unit z hz i.succ).1 ((atomicNode_strictMono z hz) i.castSucc_lt_succ))

theorem mixedPotential_atomic_step (Ξ:RevisedCovariance) {r:ℕ}
    (z:AtomicPoint r) (hz:IsAtomicPoint z) (i:Fin (r+1)) (x:ℝ) :
    FourPapersCommon.mixedPotential Ξ.toEvenMixture (atomicMeasure z hz) (atomicNode z i.castSucc,x)=
      ColeHopfFoundation.ProbabilityTheory.coleHopf (atomicRecursionData Ξ z i).1
        (atomicRecursionData Ξ z i).2.toNNReal
        (fun y=>FourPapersCommon.mixedPotential Ξ.toEvenMixture (atomicMeasure z hz)
          (atomicNode z i.succ,y)) x := by
  have H := FourPapersCommon.mixedPotential_coleHopf_on_constantCDF Ξ.toEvenMixture
    (atomicMeasure z hz) (atomicNode_mem_unit z hz i.castSucc) (atomicNode_mem_unit z hz i.succ)
    ((atomicNode_strictMono z hz) i.castSucc_lt_succ)
    (fun q hq=>parisiCDF_atomicMeasure_cell z hz i hq) x
  simpa only [RevisedCovariance.toEvenMixture_first,atomicRecursionData] using H

def covarianceCorrectionPrimitive (Ξ:RevisedCovariance) (q:ℝ) : ℝ := q*Ξ.first q-Ξ.value q

theorem hasDerivAt_covarianceCorrectionPrimitive (Ξ:RevisedCovariance) (q:ℝ) :
    HasDerivAt (covarianceCorrectionPrimitive Ξ) (q*Ξ.second q) q := by
  convert! ((hasDerivAt_id q).mul (Ξ.hasDerivAt_first q)).sub (Ξ.hasDerivAt_value q) using 1
  simp only [id_eq]
  ring

def atomicCorrection (Ξ:RevisedCovariance) {r:ℕ} (z:AtomicPoint r) : ℝ :=
  ∑i:Fin (r+1),atomicWeight z i*
    (covarianceCorrectionPrimitive Ξ 1-covarianceCorrectionPrimitive Ξ (atomicLocation z i))

theorem atomicCorrection_eq_integral (Ξ:RevisedCovariance) {r:ℕ}
    (z:AtomicPoint r) (hz:IsAtomicPoint z) :
    atomicCorrection Ξ z=∫q in (0:ℝ)..1,q*Ξ.second q*Paper.parisiCDF (atomicMeasure z hz) q := by
  symm
  change FourPapersCommon.weightedCDFIntegral (fun q=>q*Ξ.second q) (atomicMeasure z hz)=atomicCorrection Ξ z
  rw [FourPapersCommon.weightedCDFIntegral_eq_measure_integral
    (fun q=>q*Ξ.second q) (continuous_id.mul Ξ.continuous_second).continuousOn]
  rw [atomicMeasure_measure,integral_finset_sum_measure]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal (hz.2.2 i).le]
    change atomicWeight z i*(∫q in atomicLocation z i..1,q*Ξ.second q)=_
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun q _=>hasDerivAt_covarianceCorrectionPrimitive Ξ q)
      ((continuous_id.mul Ξ.continuous_second).intervalIntegrable _ _)]
  · intro i _
    exact (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top

 def atomicPotentialRecursion (Ξ:RevisedCovariance) {r:ℕ} (z:AtomicPoint r) : TerminalSpace :=
   coleHopfRecursion (r+1) (atomicRecursionData Ξ z,logCoshTerminal)

theorem potential_atomicMeasure_eq_recursion (Ξ:RevisedCovariance) {r:ℕ}
    (z:AtomicPoint r) (hz:IsAtomicPoint z) (x:ℝ) :
    potential Ξ (atomicMeasure z hz) 0 x=terminalValue (atomicPotentialRecursion Ξ z) x := by
  have H := coleHopf_chain_eq_recursion (r+1) (atomicRecursionData Ξ z) logCoshTerminal
    (fun i x=>FourPapersCommon.mixedPotential Ξ.toEvenMixture (atomicMeasure z hz) (atomicNode z i,x))
    (atomicRecursionData_variance_pos Ξ z hz)
    (fun x=>by rw [atomicNode_last,FourPapersCommon.mixedPotential_terminal,terminalValue_logCoshTerminal])
    (mixedPotential_atomic_step Ξ z hz) x
  simpa only [atomicNode_zero,potential,atomicPotentialRecursion] using H

def atomicFunctionalRecursion (Ξ:RevisedCovariance) {r:ℕ} (z:AtomicPoint r) : ℝ :=
  Real.log 2+terminalValue (atomicPotentialRecursion Ξ z) 0-(1/2:ℝ)*atomicCorrection Ξ z

theorem atomicFunctional_eq_recursion (Ξ:RevisedCovariance) {r:ℕ}
    (z:AtomicPoint r) (hz:IsAtomicPoint z) :
    parisiFunctional Ξ (atomicMeasure z hz)=atomicFunctionalRecursion Ξ z := by
  rw [parisiFunctional_eq,potential_atomicMeasure_eq_recursion Ξ z hz,
    ←atomicCorrection_eq_integral Ξ z hz]
  rfl

theorem contDiff_first (Ξ:RevisedCovariance) : ContDiff ℝ ∞ Ξ.first := by
  apply ContDiff.sum
  intro p _
  exact contDiff_const.mul (contDiff_id.pow (p-1))

theorem contDiff_value (Ξ:RevisedCovariance) : ContDiff ℝ ∞ Ξ.value := by
  apply ContDiff.sum
  intro p _
  exact contDiff_const.mul (contDiff_id.pow p)

theorem contDiff_atomicRecursionData (Ξ:RevisedCovariance) (r:ℕ) :
    ContDiff ℝ ∞ (atomicRecursionData Ξ (r:=r)) := by
  rw [contDiff_pi]
  intro i
  exact (contDiff_atomicLevel i).prodMk
    ((Ξ.contDiff_first.comp (contDiff_atomicNode i.succ)).sub
      (Ξ.contDiff_first.comp (contDiff_atomicNode i.castSucc)))

theorem contDiffAt_atomicPotentialRecursion (Ξ:RevisedCovariance) {r:ℕ}
    (z:AtomicPoint r) (hz:IsAtomicPoint z) : ContDiffAt ℝ ∞ (atomicPotentialRecursion Ξ) z :=
  (contDiffAt_coleHopfRecursion (r+1) (atomicRecursionData Ξ z,logCoshTerminal)
    (atomicRecursionData_variance_pos Ξ z hz)).comp z
      ((contDiff_atomicRecursionData Ξ r).contDiffAt.prodMk contDiffAt_const)

theorem contDiff_atomicCorrection (Ξ:RevisedCovariance) (r:ℕ) :
    ContDiff ℝ ∞ (atomicCorrection Ξ (r:=r)) := by
  apply ContDiff.sum
  intro i _
  have hp : ContDiff ℝ ∞ (covarianceCorrectionPrimitive Ξ) :=
    (contDiff_id.mul Ξ.contDiff_first).sub Ξ.contDiff_value
  exact (contDiff_atomicWeight i).mul (contDiff_const.sub (hp.comp (contDiff_atomicLocation i)))

theorem contDiffAt_atomicFunctionalRecursion (Ξ:RevisedCovariance) {r:ℕ}
    (z:AtomicPoint r) (hz:IsAtomicPoint z) : ContDiffAt ℝ ∞ (atomicFunctionalRecursion Ξ) z := by
  have hval : ContDiffAt ℝ ∞ (fun y:AtomicPoint r=>terminalValue (atomicPotentialRecursion Ξ y) 0) z := by
    let h := (ContinuousLinearMap.fst ℝ ℝ (Fin 3→ℝ →ᵇ ℝ)).comp terminalJetSubmodule.subtypeL
    simp only [terminalValue_zero]
    convert! h.contDiff.contDiffAt.comp z (contDiffAt_atomicPotentialRecursion Ξ z hz) using 1
  exact (contDiffAt_const.add hval).sub
    (contDiffAt_const.mul (contDiff_atomicCorrection Ξ r).contDiffAt)

theorem contDiffAt_atomicFunctionalExtension (Ξ:RevisedCovariance) {r:ℕ}
    (z:AtomicPoint r) (hz:IsAtomicPoint z) : ContDiffAt ℝ ∞ (atomicFunctionalExtension Ξ r) z := by
  apply (contDiffAt_atomicFunctionalRecursion Ξ z hz).congr_of_eventuallyEq
  filter_upwards [(isOpen_atomic_domain r).mem_nhds hz] with y hy
  rw [atomicFunctionalExtension_eq Ξ y hy,atomicFunctional_eq_recursion Ξ y hy]

end DepthPaper.RevisedCovariance
