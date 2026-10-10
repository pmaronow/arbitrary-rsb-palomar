module

public import GeneralDepthPaper.TruncatedJetStability
public import GeneralDepthPaper.TruncatedMomentContinuity
public import FourPapersCommon.ClockedStateConvergence

@[expose] public section


/-! Literal convergence of the covariance's compatible C³ jets, finite nodes,
levels, and the first three terminal derivatives. Terminal constants are free. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal BoundedContinuousFunction
namespace GeneralDepthPaper
open FourPapersCommon Paper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

structure TruncatedDataConvergence {r : ℕ} {qc : ℝ}
    (d : ℕ → TruncatedParisiData r qc) (d0 : TruncatedParisiData r qc) : Prop where
  covariance : ∀j : Fin 4,Tendsto (fun n => (d n).covarianceJet j) atTop (𝓝 (d0.covarianceJet j))
  node : Tendsto (fun n => (d n).node) atTop (𝓝 d0.node)
  level : Tendsto (fun n => (d n).level) atTop (𝓝 d0.level)
  terminal : ∀j : Fin 3,Tendsto (fun n => terminalJet (d n).terminal j) atTop
    (𝓝 (terminalJet d0.terminal j))

namespace TruncatedDataConvergence
variable {r : ℕ} {qc : ℝ} {d : ℕ → TruncatedParisiData r qc} {d0 : TruncatedParisiData r qc}

theorem spatialField (h : TruncatedDataConvergence d d0) (j : Fin 3) :
    Tendsto (fun n => (d n).spatialField j) atTop (𝓝 (d0.spatialField j)) :=
  tendsto_truncatedSpatialField_of_terminal_jets d0.qc_pos.le
    (fun n => (d n).parameter) d0.parameter (h.covariance 1) h.node h.level h.terminal
    (fun n => (d n).first_monotone) d0.first_monotone j

theorem normalizedParameter (h : TruncatedDataConvergence d d0) :
    Tendsto (fun n => normalizedTruncatedParameter (d n).parameter) atTop
      (𝓝 (normalizedTruncatedParameter d0.parameter)) := by
  have hN := (tendsto_terminalNormalize_iff (fun n => (d n).terminal) d0.terminal).mpr h.terminal
  simpa only [normalizedTruncatedParameter,TruncatedParisiData.parameter,nhds_prod_eq] using
    (h.covariance 1).prodMk (h.node.prodMk (h.level.prodMk hN))

theorem coefficient_L2 (h : TruncatedDataConvergence d d0) :
    Tendsto (fun n => ∫t in Icc (0:ℝ) qc,‖(d n).coefficient t-d0.coefficient t‖^2)
      atTop (𝓝 0) :=
  tendsto_truncatedCoefficient_L2 (fun n => normalizedTruncatedParameter (d n).parameter)
    (normalizedTruncatedParameter d0.parameter) h.normalizedParameter
    (fun n => (d n).node_strictMono.monotone) d0.node_strictMono.monotone
    (fun n => (d n).level_mem) d0.level_mem

theorem covarianceField_difference_bound (h : TruncatedDataConvergence d d0)
    (n : ℕ) (j : Fin 4) (t : ℝ) :
    ‖(d n).covarianceField j t-d0.covarianceField j t‖ ≤
      ‖(d n).covarianceJet j-d0.covarianceJet j‖ := by
  change ‖((d n).covarianceJet j-d0.covarianceJet j) (projIcc 0 qc d0.qc_pos.le t)‖ ≤ _
  exact ContinuousMap.norm_coe_le_norm _ _

theorem covariance_difference_norm (h : TruncatedDataConvergence d d0) (j : Fin 4) :
    Tendsto (fun n => ‖(d n).covarianceJet j-d0.covarianceJet j‖) atTop (𝓝 0) := by
  simpa only [sub_self,norm_zero] using
    ((h.covariance j).sub (tendsto_const_nhds (x := d0.covarianceJet j))).norm

theorem spatialField_difference_norm (h : TruncatedDataConvergence d d0) (j : Fin 3) :
    Tendsto (fun n => ‖(d n).spatialField j-d0.spatialField j‖) atTop (𝓝 0) := by
  simpa only [sub_self,norm_zero] using
    ((h.spatialField j).sub (tendsto_const_nhds (x := d0.spatialField j))).norm

end TruncatedDataConvergence
end GeneralDepthPaper
