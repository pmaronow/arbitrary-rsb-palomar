module

public import DepthPaper.ObservableContinuity
public import DepthPaper.AtomicGradient

@[expose] public section


/-! Actual Appendix A.2 data associated to a finite positive atomic order
parameter of the finite mixed covariance. The terminal datum is log-cosh. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff
namespace DepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

def covarianceJetMap (Ξ : AdmissibleCovariance) (j : Fin 4) :
    C(TruncatedClockDomain 1,ℝ) :=
  ⟨fun q=>iteratedDeriv j Ξ.value q,
    (Ξ.contDiff_value.continuous_iteratedDeriv j (by simp)).comp continuous_subtype_val⟩

@[simp] theorem iteratedDeriv_covariance_one (Ξ : AdmissibleCovariance) :
    iteratedDeriv 1 Ξ.value=Ξ.first := by
  rw [iteratedDeriv_one]
  exact funext fun q=>(Ξ.hasDerivAt_value q).deriv

@[simp] theorem iteratedDeriv_covariance_two (Ξ : AdmissibleCovariance) :
    iteratedDeriv 2 Ξ.value=Ξ.second := by
  rw [show 2=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_covariance_one]
  exact funext fun q=>(Ξ.hasDerivAt_first q).deriv

theorem covarianceJetMap_derivative (Ξ : AdmissibleCovariance) (j : Fin 3)
    (q : TruncatedClockDomain 1) :
    HasDerivWithinAt (fun t=>covarianceJetMap Ξ j.castSucc (projIcc 0 1 (by norm_num) t))
      (covarianceJetMap Ξ j.succ q) (Icc (0:ℝ) 1) q := by
  have hd:=(Ξ.contDiff_value.differentiable_iteratedDeriv j
    (by exact_mod_cast ENat.natCast_lt_top (j:ℕ)) q).hasDerivAt
  rw [←iteratedDeriv_succ] at hd
  apply hd.hasDerivWithinAt.congr
  · intro t ht
    simp only [covarianceJetMap,ContinuousMap.coe_mk,projIcc_of_mem (by norm_num : (0:ℝ)≤1) ht]
    rfl
  · simp only [covarianceJetMap,ContinuousMap.coe_mk,projIcc_of_mem (by norm_num : (0:ℝ)≤1) q.property,
      Fin.val_castSucc]

theorem atomicLevel_mem_unit {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (i : Fin (r+1)) : atomicLevel z i∈Icc (0:ℝ) 1 := by
  unfold atomicLevel
  constructor
  · apply Finset.sum_nonneg
    intro j _
    split_ifs
    · exact (hz.2.2 j).le
    · exact le_rfl
  · rw [←sum_atomicWeight z]
    apply Finset.sum_le_sum
    intro j _
    split_ifs
    · exact le_rfl
    · exact (hz.2.2 j).le

def atomicTruncatedData (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) : TruncatedParisiData r 1 where
  qc_pos := by norm_num
  covarianceJet := covarianceJetMap Ξ
  covariance_derivative := covarianceJetMap_derivative Ξ
  covariance_second_nonneg := fun q=>by
    change 0 ≤ iteratedDeriv 2 Ξ.value q
    rw [iteratedDeriv_covariance_two]
    exact Ξ.second_nonneg q.property.1
  node := fun i=>⟨atomicNode z i,atomicNode_mem_unit z hz i⟩
  node_strictMono := atomicNode_strictMono z hz
  node_zero := atomicNode_zero z
  node_last := atomicNode_last z
  level := atomicLevel z
  level_mem := atomicLevel_mem_unit z hz
  terminal := logCoshTerminal
  terminal_first_bound := norm_terminalJet_logCoshTerminal_le_one

@[simp] theorem covarianceJetMap_one (Ξ : AdmissibleCovariance) (q : TruncatedClockDomain 1) :
    covarianceJetMap Ξ 1 q=Ξ.first q := by
  simp only [covarianceJetMap,ContinuousMap.coe_mk,iteratedDeriv_covariance_one]
  change iteratedDeriv 1 Ξ.value q=Ξ.first q
  rw [iteratedDeriv_covariance_one]

@[simp] theorem covarianceJetMap_two (Ξ : AdmissibleCovariance) (q : TruncatedClockDomain 1) :
    covarianceJetMap Ξ 2 q=Ξ.second q := by
  simp only [covarianceJetMap,ContinuousMap.coe_mk,iteratedDeriv_covariance_two]
  change iteratedDeriv 2 Ξ.value q=Ξ.second q
  rw [iteratedDeriv_covariance_two]

theorem atomicTruncatedData_covarianceField_two (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (q : ℝ) (hq : q∈Icc (0:ℝ) 1) :
    (atomicTruncatedData Ξ z hz).covarianceField 2 q=Ξ.second q := by
  simp only [TruncatedParisiData.covarianceField,atomicTruncatedData,covarianceJetMap_two,
    projIcc_of_mem (by norm_num : (0:ℝ)≤1) hq]

end DepthPaper
