module

public import DepthPaper.GardnerMeasureGeometry
public import DepthPaper.GardnerTransitionWindow

@[expose] public section


/-! The actual minimizing measures and exact support sizes on both sides
of the Gardner transition. Every contact sign follows from the genuine
stationary response, with no minimizing-measure premise. -/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 64

def MassOneGardnerGeometry {r : ℕ} (X : AdmissibleCovariance) (z : AtomicPoint r)
    (hz : IsAtomicPoint z) (Q : Overlap) (critical lam : ℝ) : Prop :=
  (lam≤critical → atomicMeasure z hz=parisiMinimizer X ∧
    IsFiniteRSB r (atomicMeasure z hz)) ∧
  (lam<critical →
    (∀q∈Icc (0:ℝ) 1,firstVariation X (atomicMeasure z hz) q≤0) ∧
    {q∈Icc (0:ℝ) 1|firstVariation X (atomicMeasure z hz) q=0}=
      FRSB.parisiSupport (atomicMeasure z hz) ∧
    (∀i:Fin r,deriv (deriv (firstVariation X (atomicMeasure z hz))) (z.1 i)<0)) ∧
  (lam=critical →
    (∀q∈Icc (0:ℝ) 1,firstVariation X (atomicMeasure z hz) q≤0) ∧
    {q∈Icc (0:ℝ) 1|firstVariation X (atomicMeasure z hz) q=0}=
      FRSB.parisiSupport (atomicMeasure z hz)∪{(Q:ℝ)} ∧
    (atomicMeasure z hz : Measure Overlap) {Q}=0)

def InteriorGardnerGeometry {r : ℕ} (X : AdmissibleCovariance) (z : AtomicPoint r)
    (hz : IsAtomicPoint z) (m : ℝ) (Q : Overlap) : Prop :=
  m∈Ioo (0:ℝ) 1 ∧ atomicLocation z (Fin.last r)<(Q:ℝ) ∧ (Q:ℝ)<1 ∧
  twoLevelMeasure z hz m Q=parisiMinimizer X ∧
  IsFiniteRSB (r+1) (twoLevelMeasure z hz m Q) ∧
  (∀q∈Icc (0:ℝ) 1,firstVariation X (twoLevelMeasure z hz m Q) q≤0) ∧
  {q∈Icc (0:ℝ) 1|firstVariation X (twoLevelMeasure z hz m Q) q=0}=
    FRSB.parisiSupport (twoLevelMeasure z hz m Q) ∧
  (∀i:Fin r,deriv (deriv (firstVariation X (twoLevelMeasure z hz m Q))) (z.1 i)<0) ∧
  deriv (deriv (firstVariation X (twoLevelMeasure z hz m Q))) Q<0

namespace LimitingStandingData
variable {Ξ : AdmissibleCovariance} {r : ℕ} {seed : AtomicPoint r}

theorem gardner_mass_one_geometry (d : LimitingStandingData Ξ seed) {gamma : ℝ}
    (hg : 0<gamma) (hmargin : ∀m:d.MassInterval,d.limitingVariation m d.cutoff≤ -4*gamma)
    (hcost : (1/2:ℝ)*(∫q in d.cutoff..1,(1-q)*Ξ.second q)≤gamma) :
    ∀ᶠp:ℕ in atTop,4≤p ∧ ∀he:Even p,∃hp:4≤p,∃hn:p∉Ξ.degrees,
      ∀lam:ℝ,∀hlam:lam∈d.transitionWindow,∃hz:IsAtomicPoint (d.stationaryBranch p (lam,1)),
        let z:=d.stationaryBranch p (lam,1)
        let X:=Ξ.addHighDegree p hp he hn lam (d.transition_coupling_pos hlam)
        let Q:=distinguishedOverlap Ξ p d.cutoff d.stripRateLower d.stripRateUpper (z,(1,lam))
        MassOneGardnerGeometry X z hz Q (d.couplingCurve p 1) lam := by
  obtain ⟨_,_,_,_,_,Hs⟩:=d.stationaryBranch_eventually
  obtain ⟨L,_,_,Hh⟩:=d.high_overlap_geometry hg hmargin hcost
  filter_upwards [d.stationary_candidate_contacts,Hh,d.lower_geometry hg hmargin,
    d.stationary_mass_one_phase_signs,Hs] with p hc hh hl hsign hs
  refine ⟨hc.1,?_⟩
  intro he
  obtain ⟨hp,hn,Hcontact⟩:=hc.2 he
  refine ⟨hp,hn,?_⟩
  intro lam hlam
  have ht : (lam,(1:ℝ))∈d.parameterWindow:=
    ⟨d.transitionWindow_subset hlam,⟨d.massLower_mem.2.le,le_rfl⟩⟩
  obtain ⟨hz,hcontacts⟩:=Hcontact (lam,1) ht
  refine ⟨hz,?_⟩
  let z:=d.stationaryBranch p (lam,1)
  let X:=Ξ.addHighDegree p hp he hn lam (d.transition_coupling_pos hlam)
  let Q:=distinguishedOverlap Ξ p d.cutoff d.stripRateLower d.stripRateUpper (z,(1,lam))
  have H:=hh he (lam,1) ht ht hp he hn hz
  change HighOverlapContactGeometry X (twoLevelMeasure z hz 1 Q) z hz _ _ _ _ at H
  dsimp only at hcontacts
  rw [twoLevelMeasure_mass_one] at H hcontacts
  obtain ⟨hqa,haQ,hQ1,_,_,_,_,_,Hneg,Hzero⟩:=H
  have hQc : d.cutoff<(Q:ℝ):=hqa.trans haQ
  have hlast : atomicLocation z (Fin.last r)<d.cutoff:=
    d.ball_below_cutoff z (ball_subset_closedBall (hs he (lam,1) ht).1)
  have Hlow:=hl he (lam,1) ht ht hp he hn hz
  change LowerContactGeometry X (twoLevelMeasure z hz 1 Q) z d.cutoff gamma at Hlow
  rw [twoLevelMeasure_mass_one] at Hlow
  have Hv : d.stationaryMassFunction p (lam,1)=firstVariation X (atomicMeasure z hz) Q:=hcontacts.2.2.2
  have Hsign:=hsign he lam (d.transitionWindow_subset hlam)
  have Hn (h : lam<d.couplingCurve p 1) := Hneg (by rw [←Hv];exact Hsign.1.mpr h)
  have Hz (h : lam=d.couplingCurve p 1) := Hzero (by rw [←Hv];exact Hsign.2.1.mpr h)
  refine ⟨?_,?_,?_⟩
  · intro hle
    refine ⟨?_,atomicMeasure_isFiniteRSB z hz⟩
    rcases hle.eq_or_lt with heq|hlt
    · obtain ⟨hnon,hset⟩:=Hz heq
      apply minimizer_of_contact_zero_set X (atomicMeasure z hz) hnon
      rw [hset]
      exact subset_union_left
    · obtain ⟨hnon,hset⟩:=Hn hlt
      apply minimizer_of_contact_zero_set X (atomicMeasure z hz) hnon
      rw [hset]
  · intro hlt
    exact ⟨(Hn hlt).1,(Hn hlt).2,Hlow.2.2.1⟩
  · intro heq
    exact ⟨(Hz heq).1,(Hz heq).2,atomicMeasure_top_mass_zero z hz Q (hlast.trans hQc)⟩

theorem gardner_interior_geometry (d : LimitingStandingData Ξ seed) {gamma : ℝ}
    (hg : 0<gamma) (hmargin : ∀m:d.MassInterval,d.limitingVariation m d.cutoff≤ -4*gamma)
    (hcost : (1/2:ℝ)*(∫q in d.cutoff..1,(1-q)*Ξ.second q)≤gamma) :
    ∀ᶠp:ℕ in atTop,4≤p ∧ ∀he:Even p,∃hp:4≤p,∃hn:p∉Ξ.degrees,
      ∀lam:ℝ,∀hlam:lam∈d.transitionWindow,d.couplingCurve p 1<lam →
        ∃hz:IsAtomicPoint (d.stationaryBranch p (lam,d.bifurcatingMass p lam)),
          let z:=d.stationaryBranch p (lam,d.bifurcatingMass p lam)
          let X:=Ξ.addHighDegree p hp he hn lam (d.transition_coupling_pos hlam)
          let Q:=distinguishedOverlap Ξ p d.cutoff d.stripRateLower d.stripRateUpper
            (z,(d.bifurcatingMass p lam,lam))
          InteriorGardnerGeometry X z hz (d.bifurcatingMass p lam) Q := by
  obtain ⟨_,_,_,_,_,Hs⟩:=d.stationaryBranch_eventually
  obtain ⟨L,_,_,Hh⟩:=d.high_overlap_geometry hg hmargin hcost
  filter_upwards [d.stationary_candidate_contacts,Hh,d.lower_geometry hg hmargin,
    d.stationary_interior_response_zero,Hs] with p hc hh hl hzero hs
  refine ⟨hc.1,?_⟩
  intro he
  obtain ⟨hp,hn,Hcontact⟩:=hc.2 he
  refine ⟨hp,hn,?_⟩
  intro lam hlam hcrit
  have hla : lam∈Ioc (d.couplingCurve p 1) (d.criticalCoupling+d.couplingMargin):=
    ⟨hcrit,hlam.2⟩
  obtain ⟨hm,hresponse⟩:=hzero he lam hla
  let m:=d.bifurcatingMass p lam
  have hm01 : m∈Ioo (0:ℝ) 1:=⟨d.massLower_mem.1.trans hm.1,hm.2⟩
  have ht : (lam,m)∈d.parameterWindow:=⟨d.transitionWindow_subset hlam,Ioo_subset_Icc_self hm⟩
  obtain ⟨hz,hcontacts⟩:=Hcontact (lam,m) ht
  refine ⟨hz,?_⟩
  let z:=d.stationaryBranch p (lam,m)
  let X:=Ξ.addHighDegree p hp he hn lam (d.transition_coupling_pos hlam)
  let Q:=distinguishedOverlap Ξ p d.cutoff d.stripRateLower d.stripRateUpper (z,(m,lam))
  have H:=hh he (lam,m) ht ht hp he hn hz
  change HighOverlapContactGeometry X (twoLevelMeasure z hz m Q) z hz _ _ _ _ at H
  obtain ⟨hqa,haQ,hQ1,_,_,_,_,hdd,_,Hzero⟩:=H
  have hlast : atomicLocation z (Fin.last r)<(Q:ℝ):=
    (d.ball_below_cutoff z (ball_subset_closedBall (hs he (lam,m) ht).1)).trans (hqa.trans haQ)
  have Hv : d.stationaryMassFunction p (lam,m)=firstVariation X (twoLevelMeasure z hz m Q) Q:=hcontacts.2.2.2
  obtain ⟨hnon,hset⟩:=Hzero (by rw [←Hv];exact hresponse)
  have Hsupport:=parisiSupport_twoLevelMeasure z hz m hm01 Q hlast hQ1
  have hzeros : {q∈Icc (0:ℝ) 1|firstVariation X (twoLevelMeasure z hz m Q) q=0}=
      FRSB.parisiSupport (twoLevelMeasure z hz m Q) := hset.trans Hsupport.symm
  have hmin : twoLevelMeasure z hz m Q=parisiMinimizer X := by
    apply minimizer_of_contact_zero_set X (twoLevelMeasure z hz m Q) hnon
    rw [hzeros]
  have Hlow:=hl he (lam,m) ht ht hp he hn hz
  exact ⟨hm01,hlast,hQ1,hmin,twoLevelMeasure_isFiniteRSB z hz m hm01 Q hlast hQ1,
    hnon,hzeros,Hlow.2.2.1,hdd⟩

end LimitingStandingData
end DepthPaper
