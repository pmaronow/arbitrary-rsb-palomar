module

public import DepthPaper.StationaryLowerGeometry

@[expose] public section


/-! Closed all-depth Lemma 4.9. Every standing choice and its strict
cutoff margin is constructed from the genuine nondegenerate seed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace DepthPaper

theorem LowerContactGeometry.zero_iff_support {r : ℕ} {X : AdmissibleCovariance}
    {mu : ParisiMeasure} {z : AtomicPoint r} {qc gamma : ℝ}
    (H : LowerContactGeometry X mu z qc gamma) (hz : IsAtomicPoint z)
    {q : ℝ} (hq : q∈Icc (0:ℝ) qc) :
    firstVariation X mu q=0↔q∈FRSB.parisiSupport (atomicMeasure z hz) := by
  rw [H.2.1 q hq]
  constructor
  · rintro (rfl|⟨i,rfl⟩)
    · refine ⟨atomicOverlap z hz 0,?_,rfl⟩
      rw [support_atomicMeasure]
      exact ⟨0,rfl⟩
    · refine ⟨atomicOverlap z hz i.succ,?_,rfl⟩
      rw [support_atomicMeasure]
      exact ⟨i.succ,rfl⟩
  · rintro ⟨a,ha,rfl⟩
    rw [support_atomicMeasure] at ha
    obtain ⟨i,rfl⟩:=ha
    rcases Fin.eq_zero_or_eq_succ i with rfl|⟨j,rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨j,rfl⟩

def LowerGeometryTarget (Ξ : AdmissibleCovariance) {r : ℕ} (seed : AtomicPoint r) : Prop :=
  ∃d:LimitingStandingData Ξ seed,∃gamma:ℝ,0<gamma ∧
    (∀m:d.MassInterval,d.limitingVariation m 1≤ -5*gamma) ∧
    (∀m:d.MassInterval,∀q∈Icc d.cutoff 1,d.limitingVariation m q≤ -4*gamma) ∧
    (1/2:ℝ)*(∫q in d.cutoff..1,(1-q)*Ξ.second q)≤gamma ∧
    ∀ᶠp:ℕ in atTop,4≤p ∧ ∀he:Even p,∃hp:4≤p,∃hn:p∉Ξ.degrees,
      ∀theta:ℝ×ℝ,∀ht:theta∈d.parameterWindow,
        ∃hz:IsAtomicPoint (d.stationaryBranch p theta),
          let z:=d.stationaryBranch p theta
          let X:=Ξ.addHighDegree p hp he hn theta.1 (d.couplingLower_pos.trans_le ht.1.1)
          let Q:=distinguishedOverlap Ξ p d.cutoff d.stripRateLower d.stripRateUpper (z,(theta.2,theta.1))
          LowerContactGeometry X (twoLevelMeasure z hz theta.2 Q) z d.cutoff gamma

theorem lower_geometry (Ξ : AdmissibleCovariance) {r : ℕ} (seed : AtomicPoint r)
    (hz : IsAtomicPoint seed) (hnd : Nondegenerate Ξ seed hz) : LowerGeometryTarget Ξ seed := by
  obtain ⟨d,gamma,hg,hend,htail,hcost⟩:=exists_standing_cutoff_data Ξ seed hz hnd
  have H:=d.lower_geometry hg (fun m=>htail m d.cutoff ⟨le_rfl,d.cutoff_mem.2.le⟩)
  refine ⟨d,gamma,hg,hend,htail,hcost,?_⟩
  filter_upwards [H,d.stationary_candidate_contacts] with p hg hc
  refine ⟨hc.1,?_⟩
  intro he
  obtain ⟨hp,hn,Hc⟩:=hc.2 he
  refine ⟨hp,hn,?_⟩
  intro theta ht
  obtain ⟨hz,Hcontact⟩:=Hc theta ht
  exact ⟨hz,hg he theta ht ht hp he hn hz⟩

end DepthPaper
