module

public import GeneralDepthPaper.TruncatedTimePDE
public import GeneralDepthPaper.TruncatedCoefficientConvergence

@[expose] public section


/-! Literal truncated Parisi data from Appendix A.2. The covariance is given
by its actual compatible closed-interval C³ jets. The finite masses are merely
in [0,1]; no monotonicity of the mass levels is imposed. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction NNReal ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

structure TruncatedParisiData (r : ℕ) (qc : ℝ) where
  qc_pos : 0 < qc
  covarianceJet : Fin 4 → C(TruncatedClockDomain qc,ℝ)
  covariance_derivative : ∀ (j : Fin 3) (q : TruncatedClockDomain qc),
    HasDerivWithinAt (fun t => covarianceJet j.castSucc (projIcc 0 qc qc_pos.le t))
      (covarianceJet j.succ q) (Icc (0:ℝ) qc) q
  covariance_second_nonneg : ∀ q,0 ≤ covarianceJet 2 q
  node : Fin (r+2) → TruncatedClockDomain qc
  node_strictMono : StrictMono node
  node_zero : (node 0 : ℝ) = 0
  node_last : (node (Fin.last (r+1)) : ℝ) = qc
  level : Fin (r+1) → ℝ
  level_mem : ∀i,level i ∈ Icc (0:ℝ) 1
  terminal : TerminalSpace
  terminal_first_bound : ‖terminalJet terminal 0‖ ≤ 1

namespace TruncatedParisiData

def parameter {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) :
    TruncatedRecursionParameter (r+1) qc :=
  (d.covarianceJet 1,(d.node,(d.level,d.terminal)))

def covarianceField {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) (j : Fin 4) (t : ℝ) : ℝ :=
  d.covarianceJet j (projIcc 0 qc d.qc_pos.le t)

@[fun_prop] theorem continuous_covarianceField {r : ℕ} {qc : ℝ}
    (d : TruncatedParisiData r qc) (j : Fin 4) : Continuous (d.covarianceField j) :=
  (d.covarianceJet j).continuous.comp continuous_projIcc

theorem covarianceField_nonneg {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) (t : ℝ) :
    0 ≤ d.covarianceField 2 t := d.covariance_second_nonneg _

theorem norm_covarianceField_le {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc)
    (j : Fin 4) (t : ℝ) : ‖d.covarianceField j t‖ ≤ ‖d.covarianceJet j‖ :=
  (d.covarianceJet j).norm_coe_le_norm _

theorem hasDerivWithinAt_covarianceField {r : ℕ} {qc : ℝ}
    (d : TruncatedParisiData r qc) (j : Fin 3) (t : ℝ) (ht : t ∈ Icc (0:ℝ) qc) :
    HasDerivWithinAt (d.covarianceField j.castSucc) (d.covarianceField j.succ t)
      (Icc (0:ℝ) qc) t := by
  change HasDerivWithinAt (fun s => d.covarianceJet j.castSucc (projIcc 0 qc d.qc_pos.le s))
    (d.covarianceJet j.succ (projIcc 0 qc d.qc_pos.le t)) (Icc (0:ℝ) qc) t
  rw [projIcc_of_mem d.qc_pos.le ht]
  exact d.covariance_derivative j ⟨t,ht⟩

theorem hasDerivAt_covarianceField {r : ℕ} {qc : ℝ}
    (d : TruncatedParisiData r qc) (j : Fin 3) (t : ℝ) (ht : t ∈ Ioo (0:ℝ) qc) :
    HasDerivAt (d.covarianceField j.castSucc) (d.covarianceField j.succ t) t :=
  (d.hasDerivWithinAt_covarianceField j t ⟨ht.1.le,ht.2.le⟩).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

theorem contDiffOn_covarianceField {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) :
    ContDiffOn ℝ 3 (d.covarianceField 0) (Icc (0:ℝ) qc) := by
  have hu := uniqueDiffOn_Icc d.qc_pos
  have he (j : Fin 3) : EqOn (derivWithin (d.covarianceField j.castSucc) (Icc (0:ℝ) qc))
      (d.covarianceField j.succ) (Icc (0:ℝ) qc) := by
    intro t ht
    exact (d.hasDerivWithinAt_covarianceField j t ht).derivWithin (hu t ht)
  have hc2 : ContDiffOn ℝ 1 (d.covarianceField 2) (Icc (0:ℝ) qc) := by
    rw [contDiffOn_one_iff_derivWithin hu]
    refine ⟨fun t ht => (d.hasDerivWithinAt_covarianceField 2 t ht).differentiableWithinAt,?_⟩
    exact (d.continuous_covarianceField 3).continuousOn.congr (he 2)
  have hc1 : ContDiffOn ℝ 2 (d.covarianceField 1) (Icc (0:ℝ) qc) := by
    change ContDiffOn ℝ ((1:ℕ∞ω)+1) _ _
    rw [contDiffOn_succ_iff_derivWithin hu]
    refine ⟨fun t ht => (d.hasDerivWithinAt_covarianceField 1 t ht).differentiableWithinAt,by simp,?_⟩
    exact hc2.congr (he 1)
  change ContDiffOn ℝ ((2:ℕ∞ω)+1) _ _
  rw [contDiffOn_succ_iff_derivWithin hu]
  refine ⟨fun t ht => (d.hasDerivWithinAt_covarianceField 0 t ht).differentiableWithinAt,by simp,?_⟩
  exact hc1.congr (he 0)

theorem first_monotone {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) :
    Monotone (d.covarianceJet 1) := by
  have hd : MonotoneOn (d.covarianceField 1) (Icc (0:ℝ) qc) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 qc)
      (d.continuous_covarianceField 1).continuousOn
      (fun t ht => (d.hasDerivWithinAt_covarianceField 1 t (interior_subset ht)).mono interior_subset)
      (fun t _ => d.covarianceField_nonneg t)
  intro s t hst
  have he := hd s.property t.property hst
  simpa only [covarianceField,projIcc_of_mem d.qc_pos.le s.property,
    projIcc_of_mem d.qc_pos.le t.property] using he

def spatialField {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) (j : Fin 3) : (ℝ×ℝ) →ᵇ ℝ :=
  truncatedSpatialField d.qc_pos.le d.parameter j

def potential {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) (t x : ℝ) : ℝ :=
  truncatedPotential d.qc_pos.le d.parameter t x

def coefficient {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) : ℝ → ℝ :=
  truncatedCoefficient d.parameter

theorem coefficient_mem {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) (t : ℝ) :
    d.coefficient t ∈ Icc (0:ℝ) 1 :=
  truncatedCoefficient_mem_Icc d.parameter d.node_strictMono.monotone d.level_mem t

theorem spatialField_zero_bound {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) :
    ‖d.spatialField 0‖ ≤ 1 :=
  norm_truncatedSpatialField_zero_le_one d.qc_pos.le d.parameter d.first_monotone d.terminal_first_bound

theorem hasDerivAt_potential_time {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc)
    (i : Fin (r+1)) (t x : ℝ) (ht : t ∈ Ioo (d.node i.castSucc : ℝ) (d.node i.succ : ℝ)) :
    HasDerivAt (fun q => d.potential q x)
      (-d.covarianceField 2 t/2*(d.spatialField 1 (t,x)+d.level i*(d.spatialField 0 (t,x))^2)) t := by
  have ht0 : t ∈ Ioo (0:ℝ) qc :=
    ⟨lt_of_le_of_lt (d.node i.castSucc).property.1 ht.1,
      lt_of_lt_of_le ht.2 (d.node i.succ).property.2⟩
  exact hasDerivAt_truncatedPotential_time d.qc_pos.le d.parameter d.node_strictMono.monotone
    d.first_monotone i t (d.covarianceField 2 t) x ht (d.hasDerivAt_covarianceField 1 t ht0)

theorem hasDerivAt_spatialField_zero_time {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc)
    (i : Fin (r+1)) (t x : ℝ) (ht : t ∈ Ioo (d.node i.castSucc : ℝ) (d.node i.succ : ℝ)) :
    HasDerivAt (fun q => d.spatialField 0 (q,x))
      (-d.covarianceField 2 t/2*(d.spatialField 2 (t,x)+
        2*d.coefficient t*d.spatialField 0 (t,x)*d.spatialField 1 (t,x))) t := by
  have ht0 : t ∈ Ioo (0:ℝ) qc :=
    ⟨lt_of_le_of_lt (d.node i.castSucc).property.1 ht.1,
      lt_of_lt_of_le ht.2 (d.node i.succ).property.2⟩
  exact hasDerivAt_truncatedSpatialField_zero_time_coefficient d.qc_pos.le d.parameter
    d.node_strictMono.monotone d.first_monotone i t (d.covarianceField 2 t) x ht
    (d.hasDerivAt_covarianceField 1 t ht0)

end TruncatedParisiData
end GeneralDepthPaper
