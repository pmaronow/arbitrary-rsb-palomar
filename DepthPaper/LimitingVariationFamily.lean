module

public import DepthPaper.StationaryMassDerivative
public import DepthPaper.AtomicVariationContinuity

@[expose] public section


/-! The actual limiting first variation is a continuous closed-interval
C² family in the mass parameter. Its endpoint is strictly negative. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 64

namespace LimitingStandingData
variable {Ξ:AdmissibleCovariance} {r:ℕ} {seed:AtomicPoint r}

abbrev MassInterval (d:LimitingStandingData Ξ seed) := Icc d.massLower (1:ℝ)

def limitingVariationData (d:LimitingStandingData Ξ seed) (m:d.MassInterval) : TruncatedParisiData r 1 :=
  atomicTruncatedData ((temperatureCovarianceFamily Ξ).covariance m) (d.branch m)
    (d.branch_nondegenerate m m.property).choose

def limitingVariationJets (d:LimitingStandingData Ξ seed) (m:d.MassInterval) :
    Fin 3→C(TruncatedClockDomain 1,ℝ) :=
  (m:ℝ)⁻¹^2 • (d.limitingVariationData m).firstVariationJets

theorem continuous_limitingVariationJets (d:LimitingStandingData Ξ seed) :
    Continuous d.limitingVariationJets := by
  apply continuous_iff_seqContinuous.mpr
  intro mn m ht
  have hmt:Tendsto (fun n=>(mn n:ℝ)) atTop (𝓝 (m:ℝ)) := continuous_subtype_val.tendsto m |>.comp ht
  have hmp:0 < (m:ℝ) := d.massLower_mem.1.trans_le m.property.1
  have hmnp:∀n,(mn n:ℝ)∈(temperatureCovarianceFamily Ξ).domain :=
    fun n=>d.massLower_mem.1.trans_le (mn n).property.1
  have hzt:Tendsto (fun n=>d.branch (mn n)) atTop (𝓝 (d.branch m)) :=
    ((d.branch_smooth.contDiffAt (d.massDomain_open.mem_nhds (d.massWindow_subset m.property))).continuousAt.tendsto).comp hmt
  have hd:TruncatedDataConvergence (fun n=>d.limitingVariationData (mn n)) (d.limitingVariationData m) :=
    (temperatureCovarianceFamily Ξ).atomicTruncatedData_convergence hmp (d.branch m)
      (d.branch_nondegenerate m m.property).choose (fun n=>(mn n:ℝ)) hmnp
      (fun n=>d.branch (mn n)) (fun n=>(d.branch_nondegenerate (mn n) (mn n).property).choose) hmt hzt
  exact ((hmt.inv₀ hmp.ne').pow 2).smul hd.firstVariation_C2

theorem limitingVariationJets_apply (d:LimitingStandingData Ξ seed) (m:d.MassInterval)
    (j:Fin 3) (q:TruncatedClockDomain 1) :
    d.limitingVariationJets m j q=(m:ℝ)⁻¹^2 * closedJet 1 j
      (firstVariation ((temperatureCovarianceFamily Ξ).covariance m)
        (atomicMeasure (d.branch m) (d.branch_nondegenerate m m.property).choose)) q := by
  rw [closedJet_firstVariation_atomicMeasure _ _ _ j q q.property]
  rfl

theorem limitingVariation_endpoint_neg (d:LimitingStandingData Ξ seed) (m:d.MassInterval) :
    d.limitingVariationJets m 0 ⟨1,by norm_num⟩ < 0 := by
  obtain ⟨hz,hnd⟩:=d.branch_nondegenerate m m.property
  have hnd':Nondegenerate ((temperatureCovarianceFamily Ξ).covariance m) (d.branch m)
      (d.branch_nondegenerate m m.property).choose := hnd
  have hgeom:=hnd'.2.1 1 (by norm_num)
  have hne:firstVariation ((temperatureCovarianceFamily Ξ).covariance m)
      (atomicMeasure (d.branch m) (d.branch_nondegenerate m m.property).choose) 1≠0 := by
    intro hzero
    obtain ⟨i,hi⟩:=hgeom.2.mp hzero
    have hle:atomicLocation (d.branch m) i ≤ atomicLocation (d.branch m) (Fin.last r) :=
      hz.1.monotone (Fin.le_last i)
    have hlast:=hz.2.1
    linarith
  have hn: firstVariation ((temperatureCovarianceFamily Ξ).covariance m)
      (atomicMeasure (d.branch m) (d.branch_nondegenerate m m.property).choose) 1 < 0 :=
    lt_of_le_of_ne hgeom.1 hne
  rw [d.limitingVariationJets_apply m 0 ⟨1,by norm_num⟩]
  change (m:ℝ)⁻¹^2 * firstVariation ((temperatureCovarianceFamily Ξ).covariance m)
      (atomicMeasure (d.branch m) (d.branch_nondegenerate m m.property).choose) 1 < 0
  exact mul_neg_of_pos_of_neg (sq_pos_of_pos (inv_pos.mpr
    (d.massLower_mem.1.trans_le m.property.1))) hn

theorem limitingVariationJets_uniform_bound (d:LimitingStandingData Ξ seed) :
    ∃B:ℝ,0 ≤ B ∧ ∀m:d.MassInterval,∀j:Fin 3,∀q:TruncatedClockDomain 1,
      |d.limitingVariationJets m j q| ≤ B := by
  obtain ⟨B,hB⟩:=isCompact_univ.exists_bound_of_continuousOn
    d.continuous_limitingVariationJets.continuousOn
  refine ⟨max B 0,le_max_right _ _,fun m j q=>?_⟩
  have hh:‖d.limitingVariationJets m j q‖ ≤ ‖d.limitingVariationJets m j‖ :=
    ContinuousMap.norm_coe_le_norm _ q
  have hj:‖d.limitingVariationJets m j‖ ≤ ‖d.limitingVariationJets m‖ := norm_le_pi_norm _ j
  simpa only [Real.norm_eq_abs] using (hh.trans hj).trans ((hB m (mem_univ m)).trans (le_max_left _ _))

end LimitingStandingData
end DepthPaper
