module

public import DepthPaper.TruncatedStateStability
public import FourPapersCommon.L2ObservableConvergence

@[expose] public section


/-! The actual Γ and curvature-square moments converge uniformly under the
precise terminal-jet/covariance/grid hypotheses of Appendix A.2. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal BoundedContinuousFunction
namespace DepthPaper
open FourPapersCommon Paper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem lipschitzWith_truncatedSpatialField_one {L : ℕ} {qc : ℝ} (hqc : 0 ≤ qc)
    (p : TruncatedRecursionParameter L qc) (q : ℝ) :
    LipschitzWith ‖truncatedPotentialFamily p‖₊ (fun x => truncatedSpatialField hqc p 1 (q,x)) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun x => (hasDerivAt_truncatedSpatialField_one hqc p q x).differentiableAt)
  intro x
  rw [(hasDerivAt_truncatedSpatialField_one hqc p q x).deriv]
  exact_mod_cast (BoundedContinuousFunction.norm_coe_le_norm (truncatedSpatialField hqc p 2) (q,x)).trans
    (norm_truncatedSpatialField_le hqc p 2)

namespace TruncatedParisiData

theorem memLp_state {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) (t : ℝ≥0) :
    MemLp (d.state t) 2 canonicalBrownianMeasure :=
  memLp_clockedItoState d.driftData d.rateData 0 qc d.qc_pos.le t

theorem lipschitzWith_spatialField {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc)
    (j : Fin 2) (t : ℝ) :
    LipschitzWith ‖truncatedPotentialFamily d.parameter‖₊ (fun x => d.spatialField j.castSucc (t,x)) := by
  fin_cases j
  · exact lipschitzWith_truncatedSpatialField_zero d.qc_pos.le d.parameter t
  · exact lipschitzWith_truncatedSpatialField_one d.qc_pos.le d.parameter t

end TruncatedParisiData
namespace TruncatedDataConvergence
variable {r : ℕ} {qc : ℝ} {d : ℕ → TruncatedParisiData r qc} {d0 : TruncatedParisiData r qc}

theorem squared_spatial_moment (h : TruncatedDataConvergence d d0) (j : Fin 2) :
    TendstoUniformlyOn (fun n t => ∫ω,((d n).spatialField j.castSucc (t,(d n).state t.toNNReal ω))^2
      ∂canonicalBrownianMeasure)
      (fun t => ∫ω,(d0.spatialField j.castSucc (t,d0.state t.toNNReal ω))^2
        ∂canonicalBrownianMeasure) atTop (Icc (0:ℝ) qc) := by
  obtain ⟨C,hC,hCB⟩ := (Metric.isBounded_range_of_tendsto
    (fun n => (d n).spatialField j.castSucc) (h.spatialField j.castSucc)).exists_pos_norm_lt
  let B := max C ‖d0.spatialField j.castSucc‖
  have hB : 0 ≤ B := (norm_nonneg _).trans (le_max_right _ _)
  refine tendstoUniformlyOn_integral_squared_observable (Icc (0:ℝ) qc)
    (fun n t => (d n).state t.toNNReal) (fun t => d0.state t.toNNReal)
    (fun n t => (d n).memLp_state t.toNNReal) (fun t => d0.memLp_state t.toNNReal)
    (fun n t x => (d n).spatialField j.castSucc (t,x))
    (fun t x => d0.spatialField j.castSucc (t,x))
    (fun n t => (d n).integrable_spatial_observable_square j.castSucc t)
    (fun t => d0.integrable_spatial_observable_square j.castSucc t)
    hB (norm_nonneg (truncatedPotentialFamily d0.parameter)) ?_ ?_ ?_
    (fun n => ‖(d n).spatialField j.castSucc-d0.spatialField j.castSucc‖)
    (fun _ => norm_nonneg _) (h.spatialField_difference_norm j.castSucc) ?_ h.state_mean_square
  · intro n t _ x
    have hn : |(d n).spatialField j.castSucc (t,x)| ≤ ‖(d n).spatialField j.castSucc‖ :=
      by simpa only [Real.norm_eq_abs] using ((d n).spatialField j.castSucc).norm_coe_le_norm (t,x)
    exact hn.trans ((hCB _ ⟨n,rfl⟩).le.trans (le_max_left _ _))
  · intro t _ x
    have hn : |d0.spatialField j.castSucc (t,x)| ≤ ‖d0.spatialField j.castSucc‖ :=
      by simpa only [Real.norm_eq_abs] using (d0.spatialField j.castSucc).norm_coe_le_norm (t,x)
    exact hn.trans (le_max_right _ _)
  · intro t _ x y
    simpa only [Real.dist_eq,coe_nnnorm] using (d0.lipschitzWith_spatialField j t).dist_le_mul x y
  · intro n t _ x
    simpa only [Real.norm_eq_abs,BoundedContinuousFunction.sub_apply] using
      ((d n).spatialField j.castSucc-d0.spatialField j.castSucc).norm_coe_le_norm (t,x)

theorem Gamma (h : TruncatedDataConvergence d d0) :
    TendstoUniformlyOn (fun n => (d n).Gamma) d0.Gamma atTop (Icc (0:ℝ) qc) :=
  h.squared_spatial_moment 0

theorem Gamma2 (h : TruncatedDataConvergence d d0) :
    TendstoUniformlyOn (fun n => (d n).Gamma2) d0.Gamma2 atTop (Icc (0:ℝ) qc) :=
  h.squared_spatial_moment 1

end TruncatedDataConvergence
end DepthPaper
