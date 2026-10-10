module

public import DepthPaper.TruncatedDataConvergence
public import FourPapersCommon.ProductCoefficientConvergence

@[expose] public section


/-! Actual mean-square convergence of the coupled truncated Parisi diffusions,
including moving nodes and covariance clocks with flat portions. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal BoundedContinuousFunction
namespace DepthPaper
open FourPapersCommon Paper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem intervalIntegrable_square_of_measurable_bound (f : ℝ → ℝ) (hf : Measurable f)
    (T C : ℝ) (hT : 0 ≤ T) (hC : 0 ≤ C) (hb : ∀t,‖f t‖ ≤ C) :
    IntervalIntegrable (fun t => (f t)^2) volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]
  apply (integrableOn_const (C := C^2) isCompact_Icc.measure_ne_top).mono'
    (hf.pow_const 2).aestronglyMeasurable.restrict
  exact .of_forall fun t => by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb t) 2

namespace TruncatedDataConvergence
variable {r : ℕ} {qc : ℝ} {d : ℕ → TruncatedParisiData r qc} {d0 : TruncatedParisiData r qc}

theorem driftCoefficient_L2 (h : TruncatedDataConvergence d d0) :
    Tendsto (fun n => ∫t in 0..qc,((d n).driftData.coefficient t-d0.driftData.coefficient t)^2)
      atTop (𝓝 0) := by
  have hi (n : ℕ) : IntervalIntegrable
      (fun t => ((d n).driftData.coefficient t-d0.driftData.coefficient t)^2) volume 0 qc :=
    intervalIntegrable_square_of_measurable_bound _
      ((d n).driftData.coefficient_measurable.sub d0.driftData.coefficient_measurable)
      qc (((d n).driftData.radius:ℝ)+(d0.driftData.radius:ℝ)) d0.qc_pos.le
      (add_nonneg (d n).driftData.radius.coe_nonneg d0.driftData.radius.coe_nonneg)
      (fun t => (norm_sub_le _ _).trans (add_le_add
        ((d n).driftData.coefficient_bound t) (d0.driftData.coefficient_bound t)))
  have hj (n : ℕ) : IntervalIntegrable
      (fun t => ((d n).coefficient t-d0.coefficient t)^2) volume 0 qc :=
    intervalIntegrable_square_of_measurable_bound _
      ((measurable_truncatedCoefficient (d n).parameter).sub
        (measurable_truncatedCoefficient d0.parameter)) qc 2 d0.qc_pos.le (by norm_num)
      (fun t => (norm_sub_le _ _).trans (by
        have h1 := norm_truncatedCoefficient_le_one (d n).parameter (d n).node_strictMono.monotone (d n).level_mem t
        have h0 := norm_truncatedCoefficient_le_one d0.parameter d0.node_strictMono.monotone d0.level_mem t
        linarith))
  have haLim : Tendsto (fun n => ∫t in 0..qc,((d n).coefficient t-d0.coefficient t)^2)
      atTop (𝓝 0) := by
    have hh := h.coefficient_L2
    simp only [Real.norm_eq_abs,sq_abs] at hh
    simpa only [intervalIntegral.integral_of_le d0.qc_pos.le,integral_Icc_eq_integral_Ioc] using hh
  exact tendsto_productCoefficient_square_integral (fun n => (d n).coefficient)
    (fun n => (d n).covarianceField 2) d0.coefficient (d0.covarianceField 2)
    d0.qc_pos.le (norm_nonneg (d0.covarianceJet 2)) hi hj
    (fun n t _ => by change |truncatedCoefficient (d n).parameter t| ≤ 1; simpa only [Real.norm_eq_abs] using
      norm_truncatedCoefficient_le_one (d n).parameter (d n).node_strictMono.monotone (d n).level_mem t)
    (fun t _ => by simpa only [Real.norm_eq_abs] using d0.norm_covarianceField_le 2 t)
    (fun n => ‖(d n).covarianceJet 2-d0.covarianceJet 2‖) (fun n => norm_nonneg _)
    (fun n t _ => by simpa only [Real.norm_eq_abs] using h.covarianceField_difference_bound n 2 t)
    (h.covariance_difference_norm 2) haLim

theorem state_mean_square (h : TruncatedDataConvergence d d0) :
    TendstoUniformlyOn (fun n t => ∫ω,((d n).state t.toNNReal ω-d0.state t.toNNReal ω)^2
      ∂canonicalBrownianMeasure) (fun _ => 0) atTop (Icc (0:ℝ) qc) := by
  apply tendstoUniformlyOn_clockedItoState_difference_square (fun n => (d n).driftData) d0.driftData
    (fun n => (d n).rateData) d0.rateData 0 qc d0.qc_pos.le
    ‖d0.covarianceJet 2‖ ‖truncatedPotentialFamily d0.parameter‖
    (norm_nonneg _) (norm_nonneg _) (by simp [TruncatedParisiData.driftData])
    (by simp [TruncatedParisiData.driftData])
    (fun n => ‖(d n).spatialField 0-d0.spatialField 0‖)
    (fun n => ‖(d n).covarianceJet 2-d0.covarianceJet 2‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  · intro n t _ x
    exact ((d n).spatialField 0-d0.spatialField 0).norm_coe_le_norm (t,x)
  · intro n t ht
    simpa only [TruncatedParisiData.rateData,Real.coe_toNNReal t ht.1] using
      h.covarianceField_difference_bound n 2 t
  · exact h.spatialField_difference_norm 0
  · exact h.covariance_difference_norm 2
  · exact h.driftCoefficient_L2

end TruncatedDataConvergence
end DepthPaper
