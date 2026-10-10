module

public import DepthPaper.GardnerOptimizer
public import DepthPaper.StationaryCandidateHessian

@[expose] public section


/-! The literal Gardner transition for every nondegenerate finite-depth
mixed-even seed. The actual minimizing branches, contact sets, and both
atomic Hessians are all supplied by closed theorems. -/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology
namespace DepthPaper
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 64
namespace LimitingStandingData
variable {Ξ : AdmissibleCovariance} {r : ℕ} {seed : AtomicPoint r}

def GardnerNondegenerateAt (d : LimitingStandingData Ξ seed) (p : ℕ) (hp : 4≤p)
    (he : Even p) (hn : p∉Ξ.degrees) (lam : ℝ) (hlam : lam∈d.transitionWindow) : Prop :=
  let X:=Ξ.addHighDegree p hp he hn lam (d.transition_coupling_pos hlam)
  (lam<d.couplingCurve p 1 →
    ∃hz:IsAtomicPoint (d.stationaryBranch p (lam,1)),
      Nondegenerate X (d.stationaryBranch p (lam,1)) hz) ∧
  (d.couplingCurve p 1<lam →
    ∃hw:IsAtomicPoint (twoLevelAtomicCoordinates
      (d.stationaryBranch p (lam,d.bifurcatingMass p lam),
        d.bifurcatingMass p lam,(d.interiorTop p lam:ℝ))),
      Nondegenerate X (twoLevelAtomicCoordinates
        (d.stationaryBranch p (lam,d.bifurcatingMass p lam),
          d.bifurcatingMass p lam,(d.interiorTop p lam:ℝ))) hw)

theorem gardner_nondegenerate (d : LimitingStandingData Ξ seed) {gamma : ℝ}
    (hg : 0<gamma) (hmargin : ∀m:d.MassInterval,d.limitingVariation m d.cutoff≤ -4*gamma)
    (hcost : (1/2:ℝ)*(∫q in d.cutoff..1,(1-q)*Ξ.second q)≤gamma) :
    ∀ᶠp:ℕ in atTop,4≤p ∧ ∀he:Even p,∃hp:4≤p,∃hn:p∉Ξ.degrees,
      ∀lam:ℝ,∀hlam:lam∈d.transitionWindow,d.GardnerNondegenerateAt p hp he hn lam hlam := by
  obtain ⟨_,_,_,_,_,Hs⟩:=d.stationaryBranch_eventually
  have Hr:=distinguished_endpoint_smooth_eventually Ξ (isCompact_closedBall seed d.radius)
    d.ball_valid d.massLower_mem d.couplingLower_pos d.couplingLower_le_upper d.cutoff_mem
    d.ball_below_cutoff d.strip_rates.1 d.strip_rates.2.1 d.strip_rates.2.2
  filter_upwards [d.gardner_mass_one_geometry hg hmargin hcost,
    d.gardner_interior_geometry hg hmargin hcost,d.stationary_candidate_hessian,
    d.stationary_interior_response_zero,Hs,Hr] with p hminus hplus hh hzero hs hr
  refine ⟨hminus.1,?_⟩
  intro he
  obtain ⟨hp,hn,Hminus⟩:=hminus.2 he
  obtain ⟨hp',hn',Hplus⟩:=hplus.2 he
  obtain ⟨hpH,hnH,HH⟩:=hh.2 he
  refine ⟨hp,hn,?_⟩
  intro lam hlam
  let X:=Ξ.addHighDegree p hp he hn lam (d.transition_coupling_pos hlam)
  refine ⟨?_,?_⟩
  · intro hlt
    have ht : (lam,(1:ℝ))∈d.parameterWindow:=
      ⟨d.transitionWindow_subset hlam,⟨d.massLower_mem.2.le,le_rfl⟩⟩
    obtain ⟨hz,Hm⟩:=Hminus lam hlam
    obtain ⟨hzH,Hh⟩:=HH (lam,1) ht
    refine ⟨hz,Hm.nondegenerate hlt ?_⟩
    exact Hh.1 rfl
  · intro hlt
    let m:=d.bifurcatingMass p lam
    obtain ⟨hz,Hm⟩:=Hplus lam hlam hlt
    have hm : m∈Ioo d.massLower 1:=
      (hzero he lam ⟨hlt,hlam.2⟩).1
    have ht : (lam,m)∈d.parameterWindow:=⟨d.transitionWindow_subset hlam,Ioo_subset_Icc_self hm⟩
    obtain ⟨hzH,Hh⟩:=HH (lam,m) ht
    let z:=d.stationaryBranch p (lam,m)
    let eta:HighDegreeLowerParameter r:=(z,(m,lam))
    have hb:z∈closedBall seed d.radius:=ball_subset_closedBall (hs he (lam,m) ht).1
    have Hroot:=hr he eta hb ht.2 ht.1
    have hu:distinguishedEndpoint Ξ p d.cutoff d.stripRateLower d.stripRateUpper eta∈Icc (0:ℝ) 1 :=
      ⟨(endpointStrip_mem_unit d.strip_rates.1 p (Ioo_subset_Icc_self Hroot.2.1)).1,
        (endpointStrip_mem_unit d.strip_rates.1 p (Ioo_subset_Icc_self Hroot.2.1)).2.le⟩
    have hQeq : (d.interiorTop p lam:ℝ)=
        distinguishedEndpoint Ξ p d.cutoff d.stripRateLower d.stripRateUpper eta :=
      distinguishedOverlap_coe Ξ p d.cutoff d.stripRateLower d.stripRateUpper eta hu
    have hresponse:d.stationaryMassFunction p (lam,m)=0:=
      (hzero he lam ⟨hlt,hlam.2⟩).2
    have hH : positiveAtomicHessian X (twoLevelAtomicCoordinates (z,m,(d.interiorTop p lam:ℝ))) := by
      rw [hQeq]
      exact (Hh.2 hm.2 hresponse).2
    exact ⟨_,Hm.nondegenerate hH⟩

end LimitingStandingData

def GardnerTransitionTarget (Ξ : AdmissibleCovariance) {r : ℕ} (seed : AtomicPoint r) : Prop :=
  ∃d:LimitingStandingData Ξ seed,d.couplingMargin∈Ioo (0:ℝ) d.criticalCoupling ∧
    d.criticalCoupling=2*((scaledThermodynamicPressure Ξ.toEvenMixture) 1-
      deriv (scaledThermodynamicPressure Ξ.toEvenMixture) 1) ∧
    Tendsto (fun p:ℕ=>d.couplingCurve p 1) (atTop⊓𝓟 {p:ℕ|Even p}) (𝓝 d.criticalCoupling) ∧
    ∀ᶠp:ℕ in atTop,4≤p ∧ ∀he:Even p,∃hp:4≤p,∃hn:p∉Ξ.degrees,
      d.couplingCurve p 1∈Ioo (d.criticalCoupling-d.couplingMargin)
        (d.criticalCoupling+d.couplingMargin) ∧
      ∀lam:ℝ,∀hlam:lam∈d.transitionWindow,
        d.GardnerOptimizerAt p hp he hn lam hlam ∧ d.GardnerNondegenerateAt p hp he hn lam hlam

/-- The earlier manuscript's Theorem 5.1 transition, corresponding to the
phase conclusions of Revision (16)'s Theorem 4.12. This declaration uses
degrees at least four and the stronger nondegeneracy definition including
positive atomic Hessian. All standing choices are constructed from that
seed. See COVERAGE.md for the revised target and scope distinctions. -/
theorem gardner_transition (Ξ : AdmissibleCovariance) {r : ℕ} (seed : AtomicPoint r)
    (hz : IsAtomicPoint seed) (hnd : Nondegenerate Ξ seed hz) : GardnerTransitionTarget Ξ seed := by
  obtain ⟨d,gamma,hg,_,htail,hcost⟩:=exists_standing_cutoff_data Ξ seed hz hnd
  have hmargin:=fun m=>htail m d.cutoff ⟨le_rfl,d.cutoff_mem.2.le⟩
  refine ⟨d,d.couplingMargin_mem,d.criticalCoupling_eq_entropy,d.couplingCurve_critical_limit,?_⟩
  filter_upwards [d.gardner_optimizer hg hmargin hcost,d.gardner_nondegenerate hg hmargin hcost]
    with p hop hndp
  refine ⟨hop.1,?_⟩
  intro he
  obtain ⟨hp,hn,hcrit,Hopt⟩:=hop.2 he
  obtain ⟨hp',hn',Hnd⟩:=hndp.2 he
  exact ⟨hp,hn,hcrit,fun lam hlam=>⟨Hopt lam hlam,Hnd lam hlam⟩⟩

end DepthPaper
