module

public import DepthPaper.StationaryHighOverlapGeometry
public import DepthPaper.TwoLevelAtomicMeasureChart

@[expose] public section


/-! Genuine support, contact, and depth transfer for the minimizing
Gardner candidates. Zero upper mass is allowed at the transition. -/
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace DepthPaper
set_option maxHeartbeats 1600000

@[simp] theorem twoLevelMeasure_mass_one {r : ℕ} (z : AtomicPoint r)
    (hz : IsAtomicPoint z) (Q : Overlap) :
    twoLevelMeasure z hz 1 Q=atomicMeasure z hz := by
  apply ProbabilityMeasure.toMeasure_injective
  simp [twoLevelMeasure,partialAtomicMeasure,Paper.parisiMix]

theorem parisiSupport_atomicMeasure {r : ℕ} (z : AtomicPoint r)
    (hz : IsAtomicPoint z) :
    FRSB.parisiSupport (atomicMeasure z hz)=range (atomicLocation z) := by
  ext x
  constructor
  · rintro ⟨q,hq,rfl⟩
    rw [support_atomicMeasure] at hq
    obtain ⟨i,rfl⟩:=hq
    exact ⟨i,rfl⟩
  · rintro ⟨i,rfl⟩
    refine ⟨atomicOverlap z hz i,?_,rfl⟩
    rw [support_atomicMeasure]
    exact ⟨i,rfl⟩

theorem parisiSupport_twoLevelMeasure {r : ℕ} (z : AtomicPoint r)
    (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Ioo (0:ℝ) 1) (Q : Overlap)
    (hQ : atomicLocation z (Fin.last r)<(Q:ℝ)) (hQ1 : (Q:ℝ)<1) :
    FRSB.parisiSupport (twoLevelMeasure z hz m Q)=
      FRSB.parisiSupport (atomicMeasure z hz)∪{(Q:ℝ)} := by
  rw [←atomicMeasure_twoLevelCoordinates z hz m hm Q hQ hQ1]
  rw [parisiSupport_atomicMeasure,parisiSupport_atomicMeasure]
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    refine Fin.lastCases ?_ (fun i=>?_) i
    · exact Or.inr (by simp [atomicLocation_twoLevel_last])
    · exact Or.inl ⟨i,(atomicLocation_twoLevel_castSucc (z,m,(Q:ℝ)) i).symm⟩
  · rintro (⟨i,rfl⟩|hx)
    · exact ⟨i.castSucc,atomicLocation_twoLevel_castSucc (z,m,(Q:ℝ)) i⟩
    · exact ⟨Fin.last (r+1),by simpa only [atomicLocation_twoLevel_last,mem_singleton_iff] using hx.symm⟩

theorem twoLevelMeasure_isFiniteRSB {r : ℕ} (z : AtomicPoint r)
    (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Ioo (0:ℝ) 1) (Q : Overlap)
    (hQ : atomicLocation z (Fin.last r)<(Q:ℝ)) (hQ1 : (Q:ℝ)<1) :
    IsFiniteRSB (r+1) (twoLevelMeasure z hz m Q) := by
  rw [←atomicMeasure_twoLevelCoordinates z hz m hm Q hQ hQ1]
  exact atomicMeasure_isFiniteRSB _ _

theorem atomicMeasure_top_mass_zero {r : ℕ} (z : AtomicPoint r)
    (hz : IsAtomicPoint z) (Q : Overlap)
    (hQ : atomicLocation z (Fin.last r)<(Q:ℝ)) :
    (atomicMeasure z hz : Measure Overlap) {Q}=0 := by
  rw [atomicMeasure_measure,Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  have hne : atomicOverlap z hz i≠Q := by
    intro he
    have hx : atomicLocation z i=(Q:ℝ):=congrArg Subtype.val he
    have hh:atomicLocation z i≤atomicLocation z (Fin.last r):=hz.1.monotone (Fin.le_last i)
    linarith
  simp [Measure.smul_apply,Measure.dirac_apply',hne]

theorem minimizer_of_contact_zero_set (X : AdmissibleCovariance) (mu : ParisiMeasure)
    (hle : ∀q∈Icc (0:ℝ) 1,firstVariation X mu q≤0)
    (hS : FRSB.parisiSupport mu⊆{q∈Icc (0:ℝ) 1|firstVariation X mu q=0}) :
    mu=parisiMinimizer X := by
  apply parisiMinimizer_unique
  apply isParisiMinimizer_of_nonpos_zero_support X mu hle
  intro q hq
  exact (hS ⟨q,hq,rfl⟩).2

theorem nondegenerate_of_geometry {r : ℕ} (X : AdmissibleCovariance)
    (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (hmin : atomicMeasure z hz=parisiMinimizer X)
    (hle : ∀q∈Icc (0:ℝ) 1,firstVariation X (atomicMeasure z hz) q≤0)
    (hzero : {q∈Icc (0:ℝ) 1|firstVariation X (atomicMeasure z hz) q=0}=
      FRSB.parisiSupport (atomicMeasure z hz))
    (hcurv : ∀i : Fin r,deriv (deriv (firstVariation X (atomicMeasure z hz))) (z.1 i)<0)
    (hH : positiveAtomicHessian X z) : Nondegenerate X z hz := by
  refine ⟨hmin ▸ isParisiMinimizer_selected X,?_,?_,hH⟩
  · intro q hq
    refine ⟨hle q hq,?_⟩
    have hh : firstVariation X (atomicMeasure z hz) q=0↔
        q∈FRSB.parisiSupport (atomicMeasure z hz) := by
      rw [←hzero]
      exact ⟨fun h=>⟨hq,h⟩,fun h=>h.2⟩
    rw [hh,parisiSupport_atomicMeasure]
    exact ⟨fun ⟨i,hi⟩=>⟨i,hi.symm⟩,fun ⟨i,hi⟩=>⟨i,hi.symm⟩⟩
  · intro i
    have hp : z.1 i∈Ioo (0:ℝ) 1 := by
      have hpos:=hz.1 (show (0:Fin (r+1)) < i.succ by simp)
      have hlast:=hz.1.monotone (Fin.le_last i.succ)
      change 0<z.1 i at hpos
      change z.1 i≤atomicLocation z (Fin.last r) at hlast
      exact ⟨hpos,hlast.trans_lt hz.2.1⟩
    rw [closedJet_two_of_mem_Ioo _ hp]
    exact hcurv i

end DepthPaper
