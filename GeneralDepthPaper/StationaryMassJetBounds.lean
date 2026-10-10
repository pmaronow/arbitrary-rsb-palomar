module

public import GeneralDepthPaper.StationaryLimitingBounds

@[expose] public section


/-! The actual mass-response field consumes one full scalar Fréchet
order. Its fixed limiting counterpart has all compact-box bounds. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 64
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_directional_jet_difference_le {f g:E→ℝ} {x:E}
    (hf:ContDiffAt ℝ ∞ f x) (hg:ContDiffAt ℝ ∞ g x)
    (v:E) (hv:‖v‖ ≤ 1) (j:ℕ) :
    ‖iteratedFDeriv ℝ j (fun y=>fderiv ℝ f y v-fderiv ℝ g y v) x‖ ≤
      ‖iteratedFDeriv ℝ (j+1) (fun y=>f y-g y) x‖ := by
  have he:(fun y=>fderiv ℝ f y v-fderiv ℝ g y v)=ᶠ[𝓝 x]
      (fun y=>fderiv ℝ (fun z=>f z-g z) y v) := by
    filter_upwards [eventually_fderiv_sub_formula hf hg] with y hy
    rw [hy,ContinuousLinearMap.sub_apply]
  rw [(he.iteratedFDeriv (𝕜:=ℝ) j).eq_of_nhds]
  exact norm_iteratedFDeriv_directional_derivative_le (hf.sub hg) v hv j

namespace LimitingStandingData
variable {Ξ:AdmissibleCovariance} {r:ℕ} {seed:AtomicPoint r}

def limitingMassJetField (d:LimitingStandingData Ξ seed) (w:(ℝ×ℝ)×AtomicPoint r) : ℝ :=
  fderiv ℝ (stationaryLimitingObjective Ξ) w ((0,1),0)

theorem boundedSmoothOn_limitingMassJetField (d:LimitingStandingData Ξ seed) :
    BoundedSmoothOn d.limitingMassJetField d.stationaryInputWindow := by
  exact d.boundedSmoothOn_stationaryLimitingObjective.fderiv.compCLM
    (ContinuousLinearMap.apply ℝ ℝ (((0,1),0):(ℝ×ℝ)×AtomicPoint r))

theorem limitingMassJetField_on_branch (d:LimitingStandingData Ξ seed)
    (theta:ℝ×ℝ) (ht:theta∈d.parameterWindow) :
    d.limitingMassJetField (theta,d.branch theta.2)=
      (theta.1-pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) theta.2)/2 :=
  d.limiting_mass_jet_eq theta ht.2

theorem stationaryMassFunction_smooth_at (d:LimitingStandingData Ξ seed) (p:ℕ) (theta:ℝ×ℝ)
    (hz:ContDiffAt ℝ ∞ (d.stationaryBranch p) theta)
    (hf:ContDiffAt ℝ ∞ (stationaryReducedObjective Ξ p d.cutoff d.stripRateLower d.stripRateUpper)
      (theta,d.stationaryBranch p theta)) :
    ContDiffAt ℝ ∞ (d.stationaryMassFunction p) theta :=
  ((hf.fderiv_right (m:=∞) (by simp)).comp theta
    (contDiffAt_id.prodMk hz)).clm_apply contDiffAt_const

end LimitingStandingData
end GeneralDepthPaper
