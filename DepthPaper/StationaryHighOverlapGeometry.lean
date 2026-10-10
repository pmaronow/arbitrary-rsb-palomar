module

public import DepthPaper.LowerGeometryLemma
public import DepthPaper.HighOverlapGeometry

@[expose] public section


/-! Proposition 4.10 for the actual stationary selectors. Lower geometry,
endpoint contacts, logarithmic smoothing, and all parameter windows are
discharged. The two endpoint-sign cases remain the literal conditional
conclusions in the manuscript. -/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 64

def HighOverlapContactGeometry {r : ℕ} (X : AdmissibleCovariance) (mu : ParisiMeasure)
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (qc a Q gamma : ℝ) : Prop :=
  qc<a ∧ a<Q ∧ Q<1 ∧
  (∀q∈Icc qc a,firstVariation X mu q≤ -gamma) ∧
  (∀q∈Icc a 1,GammaPrime X mu q≤1/2) ∧
  StrictMonoOn (firstVariation X mu) (Icc a Q) ∧
  StrictAntiOn (firstVariation X mu) (Icc Q 1) ∧
  deriv (deriv (firstVariation X mu)) Q<0 ∧
  (firstVariation X mu Q<0 →
    (∀q∈Icc (0:ℝ) 1,firstVariation X mu q≤0) ∧
    {q∈Icc (0:ℝ) 1|firstVariation X mu q=0}=FRSB.parisiSupport (atomicMeasure z hz)) ∧
  (firstVariation X mu Q=0 →
    (∀q∈Icc (0:ℝ) 1,firstVariation X mu q≤0) ∧
    {q∈Icc (0:ℝ) 1|firstVariation X mu q=0}=FRSB.parisiSupport (atomicMeasure z hz)∪{Q})

namespace LimitingStandingData
variable {Ξ : AdmissibleCovariance} {r : ℕ} {seed : AtomicPoint r}

def StationaryHighOverlapGeometryAt (d : LimitingStandingData Ξ seed) (gamma L : ℝ)
    (p : ℕ) (theta : ℝ×ℝ) : Prop :=
  ∀ht:theta∈d.parameterWindow,∀hp:4≤p,∀he:Even p,∀hn:p∉Ξ.degrees,
    ∀hz:IsAtomicPoint (d.stationaryBranch p theta),
      let z:=d.stationaryBranch p theta
      let X:=Ξ.addHighDegree p hp he hn theta.1 (d.couplingLower_pos.trans_le ht.1.1)
      let Q:=distinguishedOverlap Ξ p d.cutoff d.stripRateLower d.stripRateUpper (z,(theta.2,theta.1))
      let a:=logarithmicOverlapThreshold p theta.1 L
      HighOverlapContactGeometry X (twoLevelMeasure z hz theta.2 Q) z hz d.cutoff a Q gamma

theorem high_overlap_geometry (d : LimitingStandingData Ξ seed) {gamma : ℝ}
    (hg : 0<gamma) (hmargin : ∀m:d.MassInterval,d.limitingVariation m d.cutoff≤ -4*gamma)
    (hcost : (1/2:ℝ)*(∫q in d.cutoff..1,(1-q)*Ξ.second q)≤gamma) :
    ∃L:ℝ,0<L ∧ 10≤d.massLower^2*L ∧
      ∀ᶠp:ℕ in atTop,∀he:Even p,∀theta∈d.parameterWindow,
        d.StationaryHighOverlapGeometryAt gamma L p theta := by
  let L:=10/d.massLower^2
  have hsq : 0<d.massLower^2 := pow_pos d.massLower_mem.1 _
  have hL : 0<L := div_pos (by norm_num) hsq
  have hcoef : 10≤d.massLower^2*L := by dsimp [L];rw [mul_div_cancel₀ _ hsq.ne']
  obtain ⟨_,_,_,_,_,Hs⟩:=d.stationaryBranch_eventually
  obtain ⟨_,_,_,_,Hr⟩:=distinguished_endpoint_contact_eventually Ξ
    (isCompact_closedBall seed d.radius) d.ball_valid d.massLower_mem d.couplingLower_pos
    d.couplingLower_le_upper d.cutoff_mem d.ball_below_cutoff d.strip_rates.1
    d.strip_rates.2.1 d.strip_rates.2.2
  have HG:=logarithmicOverlapThreshold_geometry_eventually (CQ:=d.stripRateUpper)
    d.cutoff_mem d.strip_rates.1 d.couplingLower_pos d.couplingLower_le_upper hL
  have HI:=high_overlap_intermediate_bound Ξ d.cutoff_mem d.couplingLower_pos
    d.couplingLower_le_upper hL hg hcost
  have HT:=high_overlap_slope_tail Ξ (CQ:=d.stripRateUpper) d.massLower_mem.1 d.cutoff_mem d.strip_rates.1
    d.couplingLower_pos d.couplingLower_le_upper hL hcoef
  refine ⟨L,hL,hcoef,?_⟩
  filter_upwards [d.lower_geometry hg hmargin,Hs,Hr,HG,HI,HT] with p hl hs hr hgeom hi ht
    he theta htheta
  intro ht' hp' he' hn' hz
  let z:=d.stationaryBranch p theta
  let X:=Ξ.addHighDegree p hp' he' hn' theta.1 (d.couplingLower_pos.trans_le htheta.1.1)
  let Q:=distinguishedOverlap Ξ p d.cutoff d.stripRateLower d.stripRateUpper (z,(theta.2,theta.1))
  let mu:=twoLevelMeasure z hz theta.2 Q
  let a:=logarithmicOverlapThreshold p theta.1 L
  have hball : z∈closedBall seed d.radius:=ball_subset_closedBall (hs he theta htheta).1
  have hzc : atomicLocation z (Fin.last r)<d.cutoff:=d.ball_below_cutoff z hball
  obtain ⟨hp,hn,Hr⟩:=hr.2 he
  have Hroot:=Hr (z,(theta.2,theta.1)) hball htheta.2 htheta.1
  have hstrip : (Q:ℝ)∈endpointStrip d.stripRateLower d.stripRateUpper p := Ioo_subset_Icc_self Hroot.2.1
  have hQ1 : (Q:ℝ)<1 := (endpointStrip_mem_unit d.strip_rates.1 p hstrip).2
  have hqa:=hgeom theta.1 htheta.1 Q hstrip
  have hlow : LowerContactGeometry X mu z d.cutoff gamma:=hl he theta htheta ht' hp' he' hn' hz
  have hinter : ∀q∈Icc d.cutoff a,firstVariation X mu q≤ -gamma :=
    hi hp' he' hn' theta.1 htheta.1 mu hlow.2.2.2
  have hslope : ∀q∈Icc a 1,GammaPrime X mu q≤1/2 :=
    ht hp' he' hn' theta.1 htheta.1 Q hstrip theta.2 htheta.2 r z hz hzc
  have ha : a∈Ioo (0:ℝ) 1:=⟨d.cutoff_mem.1.trans hqa.1,hqa.2.trans hQ1⟩
  have hcontact : Gamma X mu Q=(Q:ℝ):=Hroot.2.2.1
  obtain ⟨hmono,hanti,hdd⟩:=firstVariation_terminal_strict_geometry X mu ha ⟨hqa.2,hQ1⟩ hcontact hslope
  have hS : FRSB.parisiSupport (atomicMeasure z hz)⊆Icc (0:ℝ) d.cutoff := by
    rintro q ⟨v,hv,rfl⟩
    rw [support_atomicMeasure] at hv
    obtain ⟨i,rfl⟩:=hv
    refine ⟨(atomicOverlap z hz i).property.1,?_⟩
    exact (hz.1.monotone (Fin.le_last i)).trans hzc.le
  have hlow' : ∀q∈Icc (0:ℝ) d.cutoff,firstVariation X mu q≤0 ∧
      (firstVariation X mu q=0↔q∈FRSB.parisiSupport (atomicMeasure z hz)):=
    fun q hq=>⟨hlow.1 q hq,hlow.zero_iff_support hz hq⟩
  refine ⟨hqa.1,hqa.2,hQ1,hinter,hslope,hmono,hanti,hdd,?_,?_⟩
  · intro hneg
    change firstVariation X mu Q<0 at hneg
    have H:=firstVariation_global_geometry X mu ⟨d.cutoff_mem.1,hqa.1⟩ ha ⟨hqa.2,hQ1⟩ hg
      (FRSB.parisiSupport (atomicMeasure z hz)) hlow' hS hinter hcontact hslope hneg.le
    simpa only [if_neg hneg.ne] using H
  · intro hzero
    change firstVariation X mu Q=0 at hzero
    have H:=firstVariation_global_geometry X mu ⟨d.cutoff_mem.1,hqa.1⟩ ha ⟨hqa.2,hQ1⟩ hg
      (FRSB.parisiSupport (atomicMeasure z hz)) hlow' hS hinter hcontact hslope hzero.le
    simpa only [if_pos hzero] using H

end LimitingStandingData

def HighOverlapGeometryTarget (Ξ : AdmissibleCovariance) {r : ℕ} (seed : AtomicPoint r) : Prop :=
  ∃d:LimitingStandingData Ξ seed,∃gamma L:ℝ,0<gamma ∧ 0<L ∧ 10≤d.massLower^2*L ∧
    ∀ᶠp:ℕ in atTop,∀he:Even p,∀theta∈d.parameterWindow,
      d.StationaryHighOverlapGeometryAt gamma L p theta

theorem high_overlap_geometry (Ξ : AdmissibleCovariance) {r : ℕ} (seed : AtomicPoint r)
    (hz : IsAtomicPoint seed) (hnd : Nondegenerate Ξ seed hz) : HighOverlapGeometryTarget Ξ seed := by
  obtain ⟨d,gamma,hg,_,htail,hcost⟩:=exists_standing_cutoff_data Ξ seed hz hnd
  obtain ⟨L,hL,hcoef,H⟩:=d.high_overlap_geometry hg
    (fun m=>htail m d.cutoff ⟨le_rfl,d.cutoff_mem.2.le⟩) hcost
  exact ⟨d,gamma,L,hg,hL,hcoef,H⟩

end DepthPaper
