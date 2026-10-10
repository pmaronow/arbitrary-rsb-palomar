module

public import GeneralDepthPaper.RevisedSectionFourScalar
public import GeneralDepthPaper.StationaryHighOverlapGeometry
public import GeneralDepthPaper.RevisedSectionFourHighGeometry

@[expose] public section

/-! Literal revised Definition 4.7 and Lemmas/Propositions 4.8–4.11.
All standing data and strict margins are constructed from paper
nondegeneracy and admissibility; the conclusion concerns the actual
stationary probability measures and selected first variations. -/
noncomputable section
open Set Filter Metric MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal ENNReal
namespace GeneralDepthPaper
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 64

/-- The actual candidate measure, including the vanishing top mass at m=1. -/
theorem revised_candidate_measure {r:ℕ} (z:AtomicPoint r) (hz:IsAtomicPoint z)
    (m:ℝ) (hm:m∈Icc (0:ℝ) 1) (Q:Overlap) :
    (twoLevelMeasure z hz m Q:Measure Overlap)=
      ENNReal.ofReal m • (atomicMeasure z hz:Measure Overlap)+
        ENNReal.ofReal (1-m) • Measure.dirac Q := by
  change (Paper.parisiMix (Measure.dirac Q).toProbabilityMeasure (atomicMeasure z hz) m:Measure Overlap)=_
  rw [Paper.parisiMix_measure _ _ m hm]
  change ENNReal.ofReal (1-m) • Measure.dirac Q+
    ENNReal.ofReal m • (atomicMeasure z hz:Measure Overlap)=_
  exact add_comm _ _

@[simp] theorem revised_candidate_mass_one {r:ℕ} (z:AtomicPoint r) (hz:IsAtomicPoint z)
    (Q:Overlap) : twoLevelMeasure z hz 1 Q=atomicMeasure z hz :=
  Paper.parisiMix_one _ _

/-- One common construction proves every lower-contact, smoothing,
strict upper-contact and global-sign assertion on the exact paper Λ. -/
theorem revised_stationary_candidate_geometry (Ξ:AdmissibleCovariance) {r:ℕ}
    (seed:AtomicPoint r) (hz:IsAtomicPoint seed) (hND:PaperNondegenerate Ξ seed hz)
    (hsub:Ξ.IsSubcritical) :
    ∃d:LimitingStandingData Ξ seed,∃gamma:ℝ,0<gamma ∧
      (∀m:d.MassInterval,d.limitingVariation m 1≤ -5*gamma) ∧
      (∀m:d.MassInterval,∀q∈Icc d.cutoff 1,d.limitingVariation m q≤ -4*gamma) ∧
      (1/2:ℝ)*(∫q in d.cutoff..1,(1-q)*Ξ.second q)≤gamma ∧
      ∃L:ℝ,0<L ∧ L=10/d.massLower^2 ∧ 10≤d.massLower^2*L ∧
        ∀ᶠp:ℕ in atTop,4≤p ∧ ∀he:Even p,∃hp:4≤p,∃hn:p∉Ξ.degrees,
          ∀theta:ℝ×ℝ,∀ht:theta∈d.revisedParameterWindow,
            ∃hzp:IsAtomicPoint (d.stationaryBranch p theta),
              let z:=d.stationaryBranch p theta
              let Ψ:=Ξ.addHighDegree p hp he hn theta.1 (d.couplingLower_pos.trans_le ht.1.1)
              let Q:=distinguishedOverlap Ξ p d.cutoff d.stripRateLower d.stripRateUpper (z,(theta.2,theta.1))
              let μ:=twoLevelMeasure z hzp theta.2 Q
              let a:=logarithmicOverlapThreshold p theta.1 L
              ((μ:Measure Overlap)=ENNReal.ofReal theta.2 • (atomicMeasure z hzp:Measure Overlap)+
                ENNReal.ofReal (1-theta.2) • Measure.dirac Q) ∧
              (theta.2=1→μ=atomicMeasure z hzp) ∧
              (∀q∈(atomicMeasure z hzp:Measure Overlap).support,firstVariation Ψ μ q=0) ∧
              (∀q∈(atomicMeasure z hzp:Measure Overlap).support,q≠⟨0,by norm_num⟩→
                deriv (firstVariation Ψ μ) q=0) ∧
              deriv (firstVariation Ψ μ) Q=0 ∧
              d.stationaryMassFunction p theta=firstVariation Ψ μ Q ∧
              (∀q∈Icc (0:ℝ) d.cutoff,firstVariation Ψ μ q≤0 ∧
                (firstVariation Ψ μ q=0↔q∈FRSB.parisiSupport (atomicMeasure z hzp))) ∧
              (∀i:Fin r,deriv (deriv (firstVariation Ψ μ)) (z.1 i)<0) ∧
              firstVariation Ψ μ d.cutoff≤ -3*gamma ∧
              d.cutoff<a ∧ a<(Q:ℝ) ∧ (Q:ℝ)<1 ∧
              theta.1*(p:ℝ)*a^(p-1)=(10/d.massLower^2)*Real.log (p:ℝ) ∧
              (∀t∈Ioo (0:ℝ) 1,theta.1*(p:ℝ)*t^(p-1)=(10/d.massLower^2)*Real.log (p:ℝ)→t=a) ∧
              (∀q∈Icc d.cutoff a,firstVariation Ψ μ q≤ -gamma) ∧
              (∀q∈Icc a 1,derivWithin (Gamma Ψ μ) (Icc (0:ℝ) 1) q≤1/2) ∧
              StrictMonoOn (firstVariation Ψ μ) (Icc a (Q:ℝ)) ∧
              StrictAntiOn (firstVariation Ψ μ) (Icc (Q:ℝ) 1) ∧
              deriv (deriv (firstVariation Ψ μ)) Q<0 ∧
              (firstVariation Ψ μ Q<0→
                (∀q∈Icc (0:ℝ) 1,firstVariation Ψ μ q≤0) ∧
                {q∈Icc (0:ℝ) 1|firstVariation Ψ μ q=0}=FRSB.parisiSupport (atomicMeasure z hzp)) ∧
              (firstVariation Ψ μ Q=0→
                (∀q∈Icc (0:ℝ) 1,firstVariation Ψ μ q≤0) ∧
                {q∈Icc (0:ℝ) 1|firstVariation Ψ μ q=0}=FRSB.parisiSupport (atomicMeasure z hzp)∪{(Q:ℝ)}) := by
  obtain ⟨d,gamma,hg,hend,htail,hcost⟩:=exists_standing_cutoff_data Ξ seed hz
    (nondegenerate_of_paperNondegenerate Ξ seed hz hND hsub)
  have hmargin:∀m:d.MassInterval,d.limitingVariation m d.cutoff≤ -4*gamma:=
    fun m=>htail m d.cutoff ⟨le_rfl,d.cutoff_mem.2.le⟩
  let L:ℝ:=10/d.massLower^2
  have hsq:0<d.massLower^2:=pow_pos d.massLower_mem.1 _
  have hL:0<L:=div_pos (by norm_num) hsq
  have hscale:10≤d.massLower^2*L:=by dsimp [L];rw [mul_div_cancel₀ _ hsq.ne']
  have Hhigh:=d.revised_high_overlap_geometry_exact hg hmargin hcost
  refine ⟨d,gamma,hg,hend,htail,hcost,L,hL,rfl,hscale,?_⟩
  filter_upwards [d.stationary_candidate_contacts,d.lower_geometry hg hmargin,Hhigh]
    with p hc hl hh
  refine ⟨hc.1,?_⟩
  intro he
  obtain ⟨hp,hn,Hcontact⟩:=hc.2 he
  refine ⟨hp,hn,?_⟩
  intro theta ht
  have htold:=d.revisedParameterWindow_subset ht
  obtain ⟨hzp,Hcontacts⟩:=Hcontact theta htold
  refine ⟨hzp,?_⟩
  let z:=d.stationaryBranch p theta
  let Ψ:=Ξ.addHighDegree p hp he hn theta.1 (d.couplingLower_pos.trans_le ht.1.1)
  let Q:=distinguishedOverlap Ξ p d.cutoff d.stripRateLower d.stripRateUpper (z,(theta.2,theta.1))
  let μ:=twoLevelMeasure z hzp theta.2 Q
  let a:=logarithmicOverlapThreshold p theta.1 L
  have Hlower:=hl he theta htold htold hp he hn hzp
  have Hhigh:=hh he theta htold htold hp he hn hzp
  dsimp only [LimitingStandingData.StationaryHighOverlapGeometryAt,HighOverlapContactGeometry] at Hhigh
  rcases Hhigh with ⟨hca,haQ,hQ1,hnegative,hslope,hmono,hanti,hcurv,hneg,hzero⟩
  refine ⟨revised_candidate_measure _ _ _ ⟨d.massLower_mem.1.le.trans ht.2.1,ht.2.2⟩ _,
    ?_,Hcontacts.1,?_,?_,Hcontacts.2.2.2,
    ?_,Hlower.2.2.1,Hlower.2.2.2,hca,haQ,hQ1,?_,?_,hnegative,?_,hmono,hanti,hcurv,hneg,hzero⟩
  · intro hm
    simp only [hm,revised_candidate_mass_one]
  · intro q hq hq0
    have hqpos:0<(q:ℝ):=lt_of_le_of_ne q.property.1
      (Ne.symm (fun h=>hq0 (Subtype.ext h)))
    have hq1:(q:ℝ)<1:=by
      rw [support_atomicMeasure] at hq
      obtain ⟨i,rfl⟩:=hq
      exact (hzp.1.monotone (Fin.le_last i)).trans_lt hzp.2.1
    rw [(hasDerivAt_firstVariation Ψ μ ⟨hqpos,hq1⟩).deriv]
    exact Hcontacts.2.1 q hq hq0
  · rw [(hasDerivAt_firstVariation Ψ μ
      ⟨d.cutoff_mem.1.trans (hca.trans haQ),hQ1⟩).deriv]
    exact Hcontacts.2.2.1
  · intro q hq
    exact ⟨Hlower.1 q hq,Hlower.zero_iff_support hzp hq⟩
  · exact logarithmicOverlapThreshold_power (by omega : 2≤p) (d.couplingLower_pos.trans_le ht.1.1) hL
  · intro t htunit htpow
    have hapos:0<a:=d.cutoff_mem.1.trans hca
    have hcoeff:0<theta.1*(p:ℝ):=mul_pos (d.couplingLower_pos.trans_le ht.1.1)
      (by exact_mod_cast (show 0<p by omega))
    have hapow:=logarithmicOverlapThreshold_power (by omega : 2≤p) (d.couplingLower_pos.trans_le ht.1.1) hL
    have hpow:t^(p-1)=a^(p-1):=mul_left_cancel₀ hcoeff.ne' (htpow.trans hapow.symm)
    exact (pow_left_inj₀ htunit.1.le hapos.le (by omega : p-1≠0)).mp hpow
  · intro q hq
    rw [derivWithin_Gamma _ _ ⟨d.cutoff_mem.1.le.trans (hca.le.trans hq.1),hq.2⟩]
    exact hslope q hq

end GeneralDepthPaper
