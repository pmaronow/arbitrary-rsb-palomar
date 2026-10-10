module

public import GeneralDepthPaper.TwoLevelAtomicCoordinates

@[expose] public section


/-! The actual atomic chart represents exactly the two-level probability
measure, with positive lower and upper masses on its literal open domain. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace GeneralDepthPaper
set_option maxHeartbeats 1400000

theorem atomicLocation_twoLevel_castSucc {r : ℕ} (v : TwoLevelAtomicPoint r)
    (i : Fin (r+1)) : atomicLocation (twoLevelAtomicCoordinates v) i.castSucc=
      atomicLocation v.1 i := by
  refine Fin.cases ?_ (fun j=>?_) i
  · rfl
  · simp [atomicLocation,twoLevelAtomicCoordinates,Fin.castSucc_succ]

theorem atomicLocation_twoLevel_last {r : ℕ} (v : TwoLevelAtomicPoint r) :
    atomicLocation (twoLevelAtomicCoordinates v) (Fin.last (r+1))=v.2.2 := by
  rw [←Fin.succ_last,atomicLocation_succ,twoLevelAtomicCoordinates_location_last]

theorem atomicWeight_twoLevel_castSucc {r : ℕ} (v : TwoLevelAtomicPoint r)
    (i : Fin (r+1)) : atomicWeight (twoLevelAtomicCoordinates v) i.castSucc=
      v.2.1*atomicWeight v.1 i := by
  rw [atomicWeight_castSucc,twoLevelAtomicCoordinates_mass]

theorem atomicWeight_twoLevel_last {r : ℕ} (v : TwoLevelAtomicPoint r) :
    atomicWeight (twoLevelAtomicCoordinates v) (Fin.last (r+1))=1-v.2.1 := by
  rw [atomicWeight_last,twoLevelAtomicCoordinates_mass_sum]

theorem isAtomicPoint_twoLevelCoordinates {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (m Q : ℝ) (hm : m∈Ioo (0 : ℝ) 1) (hQ : atomicLocation z (Fin.last r)<Q)
    (hQ1 : Q<1) : IsAtomicPoint (twoLevelAtomicCoordinates (z,m,Q)) := by
  constructor
  · intro i
    refine Fin.lastCases ?_ (fun i=>?_) i
    · intro j hij
      exact False.elim ((not_lt_of_ge (Fin.le_last j)) hij)
    · intro j
      refine Fin.lastCases ?_ (fun j=>?_) j
      · intro _
        rw [atomicLocation_twoLevel_castSucc,atomicLocation_twoLevel_last]
        exact (hz.1.monotone (Fin.le_last i)).trans_lt hQ
      · intro hij
        rw [atomicLocation_twoLevel_castSucc,atomicLocation_twoLevel_castSucc]
        exact hz.1 (Fin.castSucc_lt_castSucc_iff.mp hij)
  · constructor
    · rw [atomicLocation_twoLevel_last]
      exact hQ1
    · intro i
      refine Fin.lastCases ?_ (fun j=>?_) i
      · rw [atomicWeight_twoLevel_last]
        exact sub_pos.mpr hm.2
      · rw [atomicWeight_twoLevel_castSucc]
        exact mul_pos hm.1 (hz.2.2 j)

theorem atomicMeasure_twoLevelCoordinates {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (m : ℝ) (hm : m∈Ioo (0 : ℝ) 1) (Q : Overlap)
    (hQ : atomicLocation z (Fin.last r)<(Q : ℝ)) (hQ1 : (Q : ℝ)<1) :
    atomicMeasure (twoLevelAtomicCoordinates (z,m,(Q : ℝ)))
        (isAtomicPoint_twoLevelCoordinates z hz m Q hm hQ hQ1)=twoLevelMeasure z hz m Q := by
  let v : TwoLevelAtomicPoint r:=(z,m,(Q : ℝ))
  let hv:=isAtomicPoint_twoLevelCoordinates z hz m Q hm hQ hQ1
  have hlow (i : Fin (r+1)) : atomicOverlap (twoLevelAtomicCoordinates v) hv i.castSucc=
      atomicOverlap z hz i := by
    apply Subtype.ext
    exact atomicLocation_twoLevel_castSucc v i
  have htop : atomicOverlap (twoLevelAtomicCoordinates v) hv (Fin.last (r+1))=Q := by
    apply Subtype.ext
    exact atomicLocation_twoLevel_last v
  change atomicMeasure (twoLevelAtomicCoordinates v) hv=twoLevelMeasure z hz m Q
  apply ProbabilityMeasure.toMeasure_injective
  rw [atomicMeasure_measure,Fin.sum_univ_castSucc]
  simp_rw [atomicWeight_twoLevel_castSucc,hlow]
  rw [atomicWeight_twoLevel_last,htop]
  change (∑i : Fin (r+1),ENNReal.ofReal (m*atomicWeight z i) • Measure.dirac (atomicOverlap z hz i))+
    ENNReal.ofReal (1-m) • Measure.dirac Q=
      (partialAtomicMeasure z hz m Q : Measure Overlap)
  rw [partialAtomicMeasure,Paper.parisiMix_measure _ _ m ⟨hm.1.le,hm.2.le⟩,atomicMeasure_measure]
  simp only [Measure.toProbabilityMeasure,ProbabilityMeasure.toMeasure]
  rw [Finset.smul_sum]
  simp_rw [smul_smul,ENNReal.ofReal_mul hm.1.le]
  exact add_comm _ _

end GeneralDepthPaper
