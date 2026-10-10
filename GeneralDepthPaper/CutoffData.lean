module

public import GeneralDepthPaper.TruncatedAtomicData
public import GeneralDepthPaper.CandidateTopSolution

@[expose] public section


/-! Genuine truncated data below an arbitrary cutoff above the lower atoms.
The final node is the cutoff, and every finite mass level is multiplied by
the actual total lower mass. No selected-solution identity is assumed here. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

def cutoffCovarianceJetMap (Ξ : AdmissibleCovariance) (qc : ℝ) (j : Fin 4) :
    C(TruncatedClockDomain qc,ℝ) :=
  ⟨fun q => iteratedDeriv j Ξ.value q,
    (Ξ.contDiff_value.continuous_iteratedDeriv j (by simp)).comp continuous_subtype_val⟩

theorem cutoffCovarianceJetMap_derivative (Ξ : AdmissibleCovariance) (qc : ℝ)
    (hc : 0 < qc) (j : Fin 3) (q : TruncatedClockDomain qc) :
    HasDerivWithinAt
      (fun t => cutoffCovarianceJetMap Ξ qc j.castSucc (projIcc 0 qc hc.le t))
      (cutoffCovarianceJetMap Ξ qc j.succ q) (Icc (0:ℝ) qc) q := by
  have hd := (Ξ.contDiff_value.differentiable_iteratedDeriv j
    (by exact_mod_cast ENat.natCast_lt_top (j:ℕ)) q).hasDerivAt
  rw [←iteratedDeriv_succ] at hd
  apply hd.hasDerivWithinAt.congr
  · intro t ht
    simp only [cutoffCovarianceJetMap,ContinuousMap.coe_mk,projIcc_of_mem hc.le ht]
    rfl
  · simp only [cutoffCovarianceJetMap,ContinuousMap.coe_mk,
      projIcc_of_mem hc.le q.property,Fin.val_castSucc]

@[simp] theorem cutoffCovarianceJetMap_one (Ξ : AdmissibleCovariance) (qc : ℝ)
    (q : TruncatedClockDomain qc) : cutoffCovarianceJetMap Ξ qc 1 q=Ξ.first q := by
  change iteratedDeriv 1 Ξ.value q=Ξ.first q
  rw [iteratedDeriv_covariance_one]

@[simp] theorem cutoffCovarianceJetMap_two (Ξ : AdmissibleCovariance) (qc : ℝ)
    (q : TruncatedClockDomain qc) : cutoffCovarianceJetMap Ξ qc 2 q=Ξ.second q := by
  change iteratedDeriv 2 Ξ.value q=Ξ.second q
  rw [iteratedDeriv_covariance_two]

def cutoffAtomicNode {r : ℕ} (z : AtomicPoint r) (qc : ℝ) : Fin (r+2)→ℝ :=
  Fin.lastCases qc (atomicLocation z)

@[simp] theorem cutoffAtomicNode_castSucc {r : ℕ} (z : AtomicPoint r) (qc : ℝ)
    (i : Fin (r+1)) : cutoffAtomicNode z qc i.castSucc=atomicLocation z i := by
  simp [cutoffAtomicNode]

@[simp] theorem cutoffAtomicNode_last {r : ℕ} (z : AtomicPoint r) (qc : ℝ) :
    cutoffAtomicNode z qc (Fin.last (r+1))=qc := by simp [cutoffAtomicNode]

@[simp] theorem cutoffAtomicNode_zero {r : ℕ} (z : AtomicPoint r) (qc : ℝ) :
    cutoffAtomicNode z qc 0=0 := by
  change cutoffAtomicNode z qc (0:Fin (r+1)).castSucc=0
  rw [cutoffAtomicNode_castSucc,atomicLocation_zero]

theorem cutoffAtomicNode_strictMono {r : ℕ} (z : AtomicPoint r)
    (hz : IsAtomicPoint z) (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc) :
    StrictMono (cutoffAtomicNode z qc) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using hc
  · simpa only [Fin.succ_castSucc,cutoffAtomicNode_castSucc] using
      hz.1 j.castSucc_lt_succ

theorem cutoff_pos {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc) : 0<qc :=
  lt_of_le_of_lt (atomicLocation_mem_unit hz (Fin.last r)).1 hc

theorem cutoffAtomicNode_mem {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc) (i : Fin (r+2)) :
    cutoffAtomicNode z qc i∈Icc (0:ℝ) qc := by
  constructor
  · simpa only [cutoffAtomicNode_zero] using
      (cutoffAtomicNode_strictMono z hz qc hc).monotone (Fin.zero_le i)
  · simpa only [cutoffAtomicNode_last] using
      (cutoffAtomicNode_strictMono z hz qc hc).monotone (Fin.le_last i)

def cutoffTruncatedData (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc)
    (g : TerminalSpace) (hg : ‖terminalJet g 0‖≤1) : TruncatedParisiData r qc where
  qc_pos := cutoff_pos z hz qc hc
  covarianceJet := cutoffCovarianceJetMap Ξ qc
  covariance_derivative := cutoffCovarianceJetMap_derivative Ξ qc (cutoff_pos z hz qc hc)
  covariance_second_nonneg := fun q => by
    rw [cutoffCovarianceJetMap_two]
    exact Ξ.second_nonneg q.property.1
  node := fun i => ⟨cutoffAtomicNode z qc i,cutoffAtomicNode_mem z hz qc hc i⟩
  node_strictMono := cutoffAtomicNode_strictMono z hz qc hc
  node_zero := cutoffAtomicNode_zero z qc
  node_last := cutoffAtomicNode_last z qc
  level := fun i => m*atomicLevel z i
  level_mem := fun i => ⟨mul_nonneg hm.1 (atomicLevel_mem_unit z hz i).1,
    (mul_le_mul_of_nonneg_left (atomicLevel_mem_unit z hz i).2 hm.1).trans
      (by simpa using hm.2)⟩
  terminal := g
  terminal_first_bound := hg

theorem cutoffTruncatedData_covarianceField_two (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc)
    (g : TerminalSpace) (hg : ‖terminalJet g 0‖≤1)
    (q : ℝ) (hq : q∈Icc (0:ℝ) qc) :
    (cutoffTruncatedData Ξ z hz m hm qc hc g hg).covarianceField 2 q=Ξ.second q := by
  simp only [TruncatedParisiData.covarianceField,cutoffTruncatedData,
    cutoffCovarianceJetMap_two,projIcc_of_mem (cutoff_pos z hz qc hc).le hq]

end GeneralDepthPaper
