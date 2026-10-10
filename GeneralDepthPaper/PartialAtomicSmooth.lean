module

public import GeneralDepthPaper.PartialAtomicMeasure

@[expose] public section


/-! Actual smoothness in the old atomic coordinates, also at full mass.
For `m<1` the family is a larger positive atomic chart. At `m=1` it is the
already verified original chart; the zero-weight top atom causes no gap. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

def partialAtomicLift {r : ℕ} (m : ℝ) (Q : ℝ) (z : AtomicPoint r) : AtomicPoint (r+1) :=
  (Fin.lastCases Q z.1,fun i=>m*atomicWeight z i)

@[simp] theorem atomicLocation_partialLift_castSucc {r : ℕ} (m Q : ℝ)
    (z : AtomicPoint r) (i : Fin (r+1)) :
    atomicLocation (partialAtomicLift m Q z) i.castSucc=atomicLocation z i := by
  cases i using Fin.cases with
  | zero => rfl
  | succ j =>
    rw [←Fin.succ_castSucc,atomicLocation_succ,atomicLocation_succ]
    change Fin.lastCases (motive:=fun _:Fin (r+1)=>ℝ) Q z.1 j.castSucc=z.1 j
    exact Fin.lastCases_castSucc j

@[simp] theorem atomicLocation_partialLift_last {r : ℕ} (m Q : ℝ) (z : AtomicPoint r) :
    atomicLocation (partialAtomicLift m Q z) (Fin.last (r+1))=Q := by
  rw [show Fin.last (r+1)=(Fin.last r).succ from rfl,atomicLocation_succ]
  change Fin.lastCases (motive:=fun _:Fin (r+1)=>ℝ) Q z.1 (Fin.last r)=Q
  exact Fin.lastCases_last

@[simp] theorem atomicWeight_partialLift_castSucc {r : ℕ} (m Q : ℝ)
    (z : AtomicPoint r) (i : Fin (r+1)) :
    atomicWeight (partialAtomicLift m Q z) i.castSucc=m*atomicWeight z i := by
  rw [atomicWeight_castSucc]
  rfl

@[simp] theorem atomicWeight_partialLift_last {r : ℕ} (m Q : ℝ) (z : AtomicPoint r) :
    atomicWeight (partialAtomicLift m Q z) (Fin.last (r+1))=1-m := by
  rw [atomicWeight_last]
  change 1-(∑i:Fin (r+1),m*atomicWeight z i)=1-m
  rw [←Finset.mul_sum,sum_atomicWeight,mul_one]

theorem isAtomicPoint_partialLift {r : ℕ} (m Q : ℝ) (z : AtomicPoint r)
    (hz : IsAtomicPoint z) (hm : m∈Ioo (0:ℝ) 1)
    (hQ : atomicLocation z (Fin.last r)<Q ∧ Q<1) :
    IsAtomicPoint (partialAtomicLift m Q z) := by
  refine ⟨?_,by simpa using hQ.2,?_⟩
  · rw [Fin.strictMono_iff_lt_succ]
    intro i
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simpa using hQ.1
    · simpa only [Fin.succ_castSucc,atomicLocation_partialLift_castSucc] using hz.1 j.castSucc_lt_succ
  · intro i
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simpa only [atomicWeight_partialLift_last] using sub_pos.mpr hm.2
    · simpa only [atomicWeight_partialLift_castSucc] using mul_pos hm.1 (hz.2.2 j)

theorem atomicMeasure_partialLift {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (m : ℝ) (hm : m∈Ioo (0:ℝ) 1) (Q : Overlap)
    (hQ : atomicLocation z (Fin.last r)<(Q:ℝ) ∧ (Q:ℝ)<1) :
    atomicMeasure (partialAtomicLift m Q z) (isAtomicPoint_partialLift m Q z hz hm hQ)=
      partialAtomicMeasure z hz m Q := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [partialAtomicMeasure,Paper.parisiMix_measure _ _ m ⟨hm.1.le,hm.2.le⟩,
    atomicMeasure_measure,atomicMeasure_measure,Fin.sum_univ_castSucc]
  simp only [atomicWeight_partialLift_castSucc,atomicWeight_partialLift_last,
    Measure.toProbabilityMeasure,ProbabilityMeasure.toMeasure]
  have he (i : Fin (r+1)) :
      atomicOverlap (partialAtomicLift m Q z) (isAtomicPoint_partialLift m Q z hz hm hQ) i.castSucc=
        atomicOverlap z hz i := by
    apply Subtype.ext
    exact atomicLocation_partialLift_castSucc m Q z i
  have hl :
      atomicOverlap (partialAtomicLift m Q z) (isAtomicPoint_partialLift m Q z hz hm hQ)
        (Fin.last (r+1))=Q := by
    apply Subtype.ext
    exact atomicLocation_partialLift_last m Q z
  simp_rw [he,hl]
  rw [Finset.smul_sum,add_comm (ENNReal.ofReal (1-m) • Measure.dirac Q)]
  apply congrArg (fun x : Measure Overlap=>x+ENNReal.ofReal (1-m) • Measure.dirac Q)
  · symm
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul,ENNReal.ofReal_mul hm.1.le]

theorem contDiff_partialAtomicLift {r : ℕ} (m Q : ℝ) :
    ContDiff ℝ ∞ (partialAtomicLift (r:=r) m Q) := by
  apply ContDiff.prodMk
  · rw [contDiff_pi]
    intro i
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simp only [partialAtomicLift,Fin.lastCases_last]
      exact contDiff_const
    · simp only [partialAtomicLift,Fin.lastCases_castSucc]
      exact (contDiff_apply ℝ ℝ j).comp contDiff_fst
  · rw [contDiff_pi]
    intro i
    exact contDiff_const.mul (contDiff_atomicWeight i)

theorem contDiffAt_partialAtomicFunctionalExtension {r : ℕ} (Ξ : AdmissibleCovariance)
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Ioc (0:ℝ) 1)
    (Q : Overlap) (hQ : atomicLocation z (Fin.last r)<(Q:ℝ) ∧ (Q:ℝ)<1) :
    ContDiffAt ℝ ∞ (partialAtomicFunctionalExtension Ξ r m Q) z := by
  rcases hm.2.eq_or_lt with he|hm1
  · subst m
    apply (contDiffAt_atomicFunctionalExtension Ξ z hz).congr_of_eventuallyEq
    filter_upwards [(isOpen_atomic_domain r).mem_nhds hz] with y hy
    simp only [partialAtomicFunctionalExtension,partialAtomicMeasureExtension,
      Paper.parisiMix_one,atomicMeasureExtension_eq _ hy,atomicFunctionalExtension_eq Ξ _ hy]
  · have hml : m∈Ioo (0:ℝ) 1 := ⟨hm.1,hm1⟩
    have hbig:=isAtomicPoint_partialLift m Q z hz hml hQ
    have hc := (contDiffAt_atomicFunctionalExtension Ξ (partialAtomicLift m Q z) hbig).comp z
      (contDiff_partialAtomicLift m (Q:ℝ)).contDiffAt
    apply hc.congr_of_eventuallyEq
    have hnear : ∀ᶠy in 𝓝 z,atomicLocation y (Fin.last r)<(Q:ℝ) :=
      (isOpen_lt (continuous_atomicLocation (Fin.last r)) continuous_const).mem_nhds hQ.1
    filter_upwards [(isOpen_atomic_domain r).mem_nhds hz,hnear] with y hy hyl
    have hyv:=isAtomicPoint_partialLift m Q y hy hml ⟨hyl,hQ.2⟩
    simp only [Function.comp_def,partialAtomicFunctionalExtension,
      partialAtomicMeasureExtension_eq _ hy,atomicFunctionalExtension_eq Ξ _ hyv,
      atomicMeasure_partialLift y hy m hml Q ⟨hyl,hQ.2⟩]

end GeneralDepthPaper
