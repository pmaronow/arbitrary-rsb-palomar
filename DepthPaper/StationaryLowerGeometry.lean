module

public import DepthPaper.LowerGeometrySequence
public import DepthPaper.CompactSequentialEventuality
public import DepthPaper.StationaryCandidateContacts

@[expose] public section


/-! Literal Lemma 4.9 for the actual stationary candidates, uniformly on
the closed physical parameter window. Compactness, actual cutoff moment
convergence, and the proved stationary contacts discharge every input. -/
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 64

def LowerContactGeometry {r : ℕ} (X : AdmissibleCovariance) (mu : ParisiMeasure)
    (z : AtomicPoint r) (qc gamma : ℝ) : Prop :=
  (∀q∈Icc (0:ℝ) qc,firstVariation X mu q≤0) ∧
  (∀q∈Icc (0:ℝ) qc,firstVariation X mu q=0↔q=0∨∃i:Fin r,q=z.1 i) ∧
  (∀i:Fin r,deriv (deriv (firstVariation X mu)) (z.1 i)<0) ∧
  firstVariation X mu qc≤ -3*gamma

namespace LimitingStandingData
variable {Ξ : AdmissibleCovariance} {r : ℕ} {seed : AtomicPoint r}

def StationaryLowerGeometryAt (d : LimitingStandingData Ξ seed) (gamma : ℝ)
    (p : ℕ) (theta : ℝ×ℝ) : Prop :=
  ∀ht:theta∈d.parameterWindow,∀hp:4≤p,∀he:Even p,∀hn:p∉Ξ.degrees,
    ∀hz:IsAtomicPoint (d.stationaryBranch p theta),
      let z:=d.stationaryBranch p theta
      let X:=Ξ.addHighDegree p hp he hn theta.1 (d.couplingLower_pos.trans_le ht.1.1)
      let Q:=distinguishedOverlap Ξ p d.cutoff d.stripRateLower d.stripRateUpper (z,(theta.2,theta.1))
      LowerContactGeometry X (twoLevelMeasure z hz theta.2 Q) z d.cutoff gamma

theorem lower_geometry (d : LimitingStandingData Ξ seed) {gamma : ℝ} (hg : 0<gamma)
    (hmargin : ∀m:d.MassInterval,d.limitingVariation m d.cutoff≤ -4*gamma) :
    ∀ᶠp:ℕ in atTop,∀he:Even p,∀theta∈d.parameterWindow,
      d.StationaryLowerGeometryAt gamma p theta := by
  obtain ⟨_,_,_,_,_,Hs⟩:=d.stationaryBranch_eventually
  have Hr:=distinguished_endpoint_smooth_eventually Ξ
    (isCompact_closedBall seed d.radius) d.ball_valid d.massLower_mem
    d.couplingLower_pos d.couplingLower_le_upper d.cutoff_mem d.ball_below_cutoff
    d.strip_rates.1 d.strip_rates.2.1 d.strip_rates.2.2
  have Hq:=endpointStrip_above_cutoff_eventually (CQ:=d.stripRateUpper)
    d.cutoff_mem.2 d.strip_rates.1
  obtain ⟨P,hP⟩:=eventually_atTop.mp
    (d.stationary_candidate_contacts.and (Hs.and (Hr.and Hq)))
  have hK : IsCompact d.parameterWindow:=isCompact_Icc.prod isCompact_Icc
  have HG : ∀ᶠp:ℕ in atTop,(Even p∧P≤p)→∀theta∈d.parameterWindow,
      d.StationaryLowerGeometryAt gamma p theta := by
    apply compact_eventually_allowed_of_sequential hK
    intro p hallowed hpt theta ht theta0 ht0 htt
    have he : ∀n,Even (p n):=fun n=>(hallowed n).1
    have hdegree := fun n=>(hP (p n) (hallowed n).2).1.2 (he n)
    choose hp hn hcontactAll using hdegree
    let z n:=d.stationaryBranch (p n) (theta n)
    let m n:ℝ:=(theta n).2
    let lam n:ℝ:=(theta n).1
    let Q n:=distinguishedOverlap Ξ (p n) d.cutoff d.stripRateLower d.stripRateUpper
      (z n,(m n,lam n))
    choose hz hcontacts using fun n=>hcontactAll n (theta n) (ht n)
    have hb (n:ℕ) : z n∈closedBall seed d.radius:=
      ball_subset_closedBall ((hP (p n) (hallowed n).2).2.1 (he n) (theta n) (ht n)).1
    have hzc (n:ℕ) : atomicLocation (z n) (Fin.last r)<d.cutoff:=d.ball_below_cutoff _ (hb n)
    have hroot (n:ℕ) := (hP (p n) (hallowed n).2).2.2.1 (he n)
      (z n,(m n,lam n)) (hb n) (ht n).2 (ht n).1
    have hQ (n:ℕ) : (Q n:ℝ)∈endpointStrip d.stripRateLower d.stripRateUpper (p n) := by
      have hraw:=Ioo_subset_Icc_self (hroot n).2.1
      have hu:=endpointStrip_mem_unit d.strip_rates.1 (p n) hraw
      change (distinguishedOverlap Ξ (p n) d.cutoff d.stripRateLower d.stripRateUpper
        (z n,(m n,lam n)):ℝ)∈_
      rw [distinguishedOverlap_coe Ξ _ _ _ _ _ ⟨hu.1,hu.2.le⟩]
      exact hraw
    have hqcQ (n:ℕ) : d.cutoff≤(Q n:ℝ):=
      ((hP (p n) (hallowed n).2).2.2.2 (Q n) (hQ n)).le
    let m0:d.MassInterval:=⟨theta0.2,ht0.2⟩
    have hzt : Tendsto z atTop (𝓝 (d.branch m0)):=
      d.stationaryBranch_sequence_converges p he hpt theta ht theta0 ht0 htt
    have hmt : Tendsto m atTop (𝓝 (m0:ℝ)):=
      (continuous_snd.tendsto theta0).comp htt
    have hpositive (n:ℕ) (i:Fin r) : (z n).1 i∈Ioo (0:ℝ) d.cutoff:=by
      refine ⟨?_,?_⟩
      · simpa only [atomicLocation_zero,atomicLocation_succ] using
          (hz n).1 (show (0:Fin (r+1)) < i.succ from Fin.succ_pos i)
      · exact ((hz n).1.monotone (Fin.le_last i.succ)).trans_lt (hzc n)
    have hsp (n:ℕ) (i:Fin r) : atomicOverlap (z n) (hz n) i.succ∈
        (atomicMeasure (z n) (hz n):Measure Overlap).support:=by
      rw [support_atomicMeasure]
      exact ⟨i.succ,rfl⟩
    have hc (n:ℕ) (i:Fin r) :
        firstVariation (Ξ.addHighDegree (p n) (hp n) (he n) (hn n) (lam n)
          (d.couplingLower_pos.trans_le (ht n).1.1))
          (twoLevelMeasure (z n) (hz n) (m n) (Q n)) ((z n).1 i)=0:=
      (hcontacts n).1 _ (hsp n i)
    have hcritical (n:ℕ) (i:Fin r) :
        deriv (firstVariation (Ξ.addHighDegree (p n) (hp n) (he n) (hn n) (lam n)
          (d.couplingLower_pos.trans_le (ht n).1.1))
          (twoLevelMeasure (z n) (hz n) (m n) (Q n))) ((z n).1 i)=0:=by
      have hne : atomicOverlap (z n) (hz n) i.succ≠⟨0,by norm_num⟩:=by
        intro hh
        have hv:=congrArg Subtype.val hh
        exact (ne_of_gt (hpositive n i).1) hv
      have hh:=(hcontacts n).2.1 _ (hsp n i) hne
      rw [(hasDerivAt_firstVariation _ _
        ⟨(hpositive n i).1,(hpositive n i).2.trans d.cutoff_mem.2⟩).deriv]
      exact hh
    have H:=d.lower_geometry_sequence hg hmargin p hp he hn hpt m lam
      (fun n=>(ht n).2) (fun n=>(ht n).1) Q hQ hqcQ z hz hzc m0 hzt hmt hc hcritical
    filter_upwards [H] with n Hn
    intro ht' hp' he' hn' hz'
    refine ⟨Hn.1,Hn.2.1,?_,Hn.2.2.2⟩
    intro i
    have hi:=Hn.2.2.1 i
    rw [closedJet_two_of_mem_Ioo _ (hpositive n i)] at hi
    exact hi
  filter_upwards [HG,eventually_ge_atTop P] with p hp hlarge he theta ht
  exact hp ⟨he,hlarge⟩ theta ht

end LimitingStandingData
end DepthPaper
