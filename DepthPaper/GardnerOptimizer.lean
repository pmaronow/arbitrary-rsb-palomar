module

public import DepthPaper.GardnerNondegeneracyTransfer

@[expose] public section


/-! Closed identification of the actual Parisi optimizer throughout the
transition window, with exact depth and the critical zero-mass contact. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace DepthPaper
set_option maxHeartbeats 2400000
namespace LimitingStandingData
variable {Ξ : AdmissibleCovariance} {r : ℕ} {seed : AtomicPoint r}

def GardnerOptimizerAt (d : LimitingStandingData Ξ seed) (p : ℕ) (hp : 4≤p)
    (he : Even p) (hn : p∉Ξ.degrees) (lam : ℝ) (hlam : lam∈d.transitionWindow) : Prop :=
  let X:=Ξ.addHighDegree p hp he hn lam (d.transition_coupling_pos hlam)
  let critical:=d.couplingCurve p 1
  (lam≤critical → d.massOneCandidate p lam=parisiMinimizer X ∧
    IsFiniteRSB r (parisiMinimizer X)) ∧
  (lam<critical →
    {q∈Icc (0:ℝ) 1|firstVariation X (d.massOneCandidate p lam) q=0}=
      FRSB.parisiSupport (d.massOneCandidate p lam)) ∧
  (lam=critical →
    {q∈Icc (0:ℝ) 1|firstVariation X (d.massOneCandidate p lam) q=0}=
      FRSB.parisiSupport (d.massOneCandidate p lam)∪{(d.massOneTop p lam:ℝ)} ∧
    (d.massOneCandidate p lam : Measure Overlap) {d.massOneTop p lam}=0) ∧
  (critical<lam → d.interiorCandidate p lam=parisiMinimizer X ∧
    IsFiniteRSB (r+1) (parisiMinimizer X)) ∧
  (IsFiniteRSB r (parisiMinimizer X)↔lam≤critical) ∧
  (IsFiniteRSB (r+1) (parisiMinimizer X)↔critical<lam)

theorem gardner_optimizer (d : LimitingStandingData Ξ seed) {gamma : ℝ}
    (hg : 0<gamma) (hmargin : ∀m:d.MassInterval,d.limitingVariation m d.cutoff≤ -4*gamma)
    (hcost : (1/2:ℝ)*(∫q in d.cutoff..1,(1-q)*Ξ.second q)≤gamma) :
    ∀ᶠp:ℕ in atTop,4≤p ∧ ∀he:Even p,∃hp:4≤p,∃hn:p∉Ξ.degrees,
      d.couplingCurve p 1∈Ioo (d.criticalCoupling-d.couplingMargin)
        (d.criticalCoupling+d.couplingMargin) ∧
      ∀lam:ℝ,∀hlam:lam∈d.transitionWindow,d.GardnerOptimizerAt p hp he hn lam hlam := by
  filter_upwards [d.gardner_mass_one_geometry hg hmargin hcost,
    d.gardner_interior_geometry hg hmargin hcost,d.criticalCoupling_in_transition_eventually]
    with p hminus hplus hcrit
  refine ⟨hminus.1,?_⟩
  intro he
  obtain ⟨hp,hn,Hminus⟩:=hminus.2 he
  obtain ⟨hp',hn',Hplus⟩:=hplus.2 he
  refine ⟨hp,hn,hcrit he,?_⟩
  intro lam hlam
  let X:=Ξ.addHighDegree p hp he hn lam (d.transition_coupling_pos hlam)
  obtain ⟨hz,Hm⟩:=Hminus lam hlam
  have hmu:=d.massOneCandidate_eq p lam hz
  have Hlo (h : lam≤d.couplingCurve p 1) :
      d.massOneCandidate p lam=parisiMinimizer X ∧ IsFiniteRSB r (parisiMinimizer X) := by
    have H:=(Hm.1 h)
    refine ⟨hmu.trans H.1,?_⟩
    rw [←H.1]
    exact H.2
  have Hhi (h : d.couplingCurve p 1<lam) :
      d.interiorCandidate p lam=parisiMinimizer X ∧ IsFiniteRSB (r+1) (parisiMinimizer X) := by
    obtain ⟨hzb,Hb⟩:=Hplus lam hlam h
    have hmb:=d.interiorCandidate_eq p lam hzb
    refine ⟨hmb.trans Hb.2.2.2.1,?_⟩
    rw [←Hb.2.2.2.1]
    exact Hb.2.2.2.2.1
  refine ⟨Hlo,?_,?_,Hhi,?_,?_⟩
  · intro h
    rw [hmu]
    exact (Hm.2.1 h).2.1
  · intro h
    rw [hmu]
    exact ⟨(Hm.2.2 h).2.1,(Hm.2.2 h).2.2⟩
  · constructor
    · intro hd
      by_contra h
      have hh:=hd.unique_depth (Hhi (lt_of_not_ge h)).2
      omega
    · intro h
      exact (Hlo h).2
  · constructor
    · intro hd
      by_contra h
      have hh:=hd.unique_depth (Hlo (le_of_not_gt h)).2
      omega
    · intro h
      exact (Hhi h).2

end LimitingStandingData

def GardnerOptimizerTarget (Ξ : AdmissibleCovariance) {r : ℕ} (seed : AtomicPoint r) : Prop :=
  ∃d:LimitingStandingData Ξ seed,d.couplingMargin∈Ioo (0:ℝ) d.criticalCoupling ∧
    Tendsto (fun p:ℕ=>d.couplingCurve p 1) (atTop⊓𝓟 {p:ℕ|Even p}) (𝓝 d.criticalCoupling) ∧
    ∀ᶠp:ℕ in atTop,4≤p ∧ ∀he:Even p,∃hp:4≤p,∃hn:p∉Ξ.degrees,
      d.couplingCurve p 1∈Ioo (d.criticalCoupling-d.couplingMargin)
        (d.criticalCoupling+d.couplingMargin) ∧
      ∀lam:ℝ,∀hlam:lam∈d.transitionWindow,d.GardnerOptimizerAt p hp he hn lam hlam

theorem gardner_optimizer (Ξ : AdmissibleCovariance) {r : ℕ} (seed : AtomicPoint r)
    (hz : IsAtomicPoint seed) (hnd : Nondegenerate Ξ seed hz) : GardnerOptimizerTarget Ξ seed := by
  obtain ⟨d,gamma,hg,_,htail,hcost⟩:=exists_standing_cutoff_data Ξ seed hz hnd
  exact ⟨d,d.couplingMargin_mem,d.couplingCurve_critical_limit,
    d.gardner_optimizer hg (fun m=>htail m d.cutoff ⟨le_rfl,d.cutoff_mem.2.le⟩) hcost⟩

end DepthPaper
