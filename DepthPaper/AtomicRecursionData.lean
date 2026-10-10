module

public import DepthPaper.AtomicCoordinates
public import DepthPaper.ColeHopfRecursion
public import FourPapersCommon.MixedColeHopf

@[expose] public section


/-! Literal chronological mass levels and Gaussian variances of an actual
atomic mixed-model order parameter. The normalized variance clock is converted
back to ξ′-increments, retaining the actual atomic CDF coefficients. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace DepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 600000

def atomicNode {r:ℕ} (z:AtomicPoint r) : Fin (r+2)→ℝ := Fin.lastCases 1 (atomicLocation z)
@[simp] theorem atomicNode_castSucc {r:ℕ} (z:AtomicPoint r) (i:Fin (r+1)) :
    atomicNode z i.castSucc=atomicLocation z i := by simp [atomicNode]
@[simp] theorem atomicNode_last {r:ℕ} (z:AtomicPoint r) : atomicNode z (Fin.last (r+1))=1 := by simp [atomicNode]
@[simp] theorem atomicNode_zero {r:ℕ} (z:AtomicPoint r) : atomicNode z 0=0 := by
  change atomicNode z (0:Fin (r+1)).castSucc=0
  rw [atomicNode_castSucc]
  rfl

theorem atomicNode_strictMono {r:ℕ} (z:AtomicPoint r) (hz:IsAtomicPoint z) : StrictMono (atomicNode z) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  refine Fin.lastCases ?_ (fun j=>?_) i
  · simpa using hz.2.1
  · simpa only [Fin.succ_castSucc,atomicNode_castSucc] using hz.1 j.castSucc_lt_succ

theorem atomicNode_mem_unit {r:ℕ} (z:AtomicPoint r) (hz:IsAtomicPoint z) (i:Fin (r+2)) :
    atomicNode z i∈Icc (0:ℝ) 1 := by
  constructor
  · simpa only [atomicNode_zero] using (atomicNode_strictMono z hz).monotone (Fin.zero_le i)
  · simpa only [atomicNode_last] using (atomicNode_strictMono z hz).monotone (Fin.le_last i)

def atomicLevel {r:ℕ} (z:AtomicPoint r) (p:Fin (r+1)) : ℝ :=
  ∑i:Fin (r+1),if i≤p then atomicWeight z i else 0

theorem parisiCDF_atomicMeasure_cell {r:ℕ} (z:AtomicPoint r) (hz:IsAtomicPoint z)
    (p:Fin (r+1)) {q:ℝ} (hq:q∈Ico (atomicNode z p.castSucc) (atomicNode z p.succ)) :
    Paper.parisiCDF (atomicMeasure z hz) q=atomicLevel z p := by
  rw [parisiCDF_atomicMeasure]
  apply Finset.sum_congr rfl
  intro i _
  have hi : atomicLocation z i≤q ↔ i≤p := by
    constructor
    · intro hqi
      by_contra hn
      have hpi : p.succ ≤ i.castSucc := by
        simp only [Fin.le_def,Fin.val_succ,Fin.val_castSucc]
        have hnpi : ¬i.val≤p.val := hn
        omega
      have hnq := (atomicNode_strictMono z hz).monotone hpi
      rw [atomicNode_castSucc] at hnq
      linarith [hq.2]
    · intro hip
      have hie := hz.1.monotone hip
      rw [atomicNode_castSucc] at hq
      exact hie.trans hq.1
  simp only [hi]

def atomicRecursionData (Ξ:AdmissibleCovariance) {r:ℕ} (z:AtomicPoint r) : Fin (r+1)→ℝ×ℝ :=
  fun i=>(atomicLevel z i,Ξ.first (atomicNode z i.succ)-Ξ.first (atomicNode z i.castSucc))

theorem atomicRecursionData_variance_pos (Ξ:AdmissibleCovariance) {r:ℕ}
    (z:AtomicPoint r) (hz:IsAtomicPoint z) (i:Fin (r+1)) : 0<(atomicRecursionData Ξ z i).2 := by
  exact sub_pos.mpr (Ξ.first_strictMonoOn (atomicNode_mem_unit z hz i.castSucc).1
    (atomicNode_mem_unit z hz i.succ).1 ((atomicNode_strictMono z hz) i.castSucc_lt_succ))

theorem mixedPotential_atomic_step (Ξ:AdmissibleCovariance) {r:ℕ}
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
  simpa only [AdmissibleCovariance.toEvenMixture_first,atomicRecursionData] using H

end DepthPaper
