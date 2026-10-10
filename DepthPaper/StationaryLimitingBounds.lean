module

public import DepthPaper.StationaryMassDerivative
public import DepthPaper.CompositionDifferenceBounds

@[expose] public section


/-! All derivatives of the actual fixed limiting objective are bounded
on the compact physical chart box, including the fourth jet needed for
quantitative C² stationary-selector comparison. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 1200000

namespace LimitingStandingData
variable {Ξ:AdmissibleCovariance} {r:ℕ} {seed:AtomicPoint r}

def stationaryInputWindow (d:LimitingStandingData Ξ seed) : Set ((ℝ×ℝ)×AtomicPoint r) :=
  d.parameterWindow×ˢclosedBall seed d.radius

theorem stationaryInputWindow_compact (d:LimitingStandingData Ξ seed) :
    IsCompact d.stationaryInputWindow :=
  (isCompact_Icc.prod isCompact_Icc).prod (isCompact_closedBall seed d.radius)

theorem stationaryInputWindow_convex (d:LimitingStandingData Ξ seed) :
    Convex ℝ d.stationaryInputWindow :=
  ((convex_Icc _ _).prod (convex_Icc _ _)).prod (convex_closedBall seed d.radius)

theorem boundedSmoothOn_stationaryLimitingObjective (d:LimitingStandingData Ξ seed) :
    BoundedSmoothOn (stationaryLimitingObjective Ξ) d.stationaryInputWindow := by
  apply BoundedSmoothOn.of_compact d.stationaryInputWindow_compact
  intro w hw
  exact contDiffAt_stationaryLimitingObjective Ξ w.2 (d.ball_valid w.2 hw.2) w.1
    (d.massLower_mem.1.trans_le hw.1.2.1)

theorem boundedSmoothOn_stationaryLimitingGradient (d:LimitingStandingData Ξ seed) :
    BoundedSmoothOn (fun w:(ℝ×ℝ)×AtomicPoint r=>partialGradient (stationaryLimitingObjective Ξ) w.1 w.2)
      d.stationaryInputWindow := by
  apply BoundedSmoothOn.of_compact d.stationaryInputWindow_compact
  intro w hw
  exact contDiffAt_partialGradient _ (d.boundedSmoothOn_stationaryLimitingObjective.smooth w hw)

theorem limiting_branch_bounded_smooth (d:LimitingStandingData Ξ seed) :
    BoundedSmoothOn (fun theta:ℝ×ℝ=>d.branch theta.2) d.parameterWindow := by
  apply BoundedSmoothOn.of_compact (isCompact_Icc.prod isCompact_Icc)
  intro theta ht
  exact (d.branch_smooth.contDiffAt (d.massDomain_open.mem_nhds
    (d.massWindow_subset ht.2))).comp theta contDiffAt_snd

end LimitingStandingData
end DepthPaper
