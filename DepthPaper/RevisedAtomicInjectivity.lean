module

public import DepthPaper.AtomicCoordinates

@[expose] public section

/-! Detection of a change in mass coordinates while the support is fixed.
The statement concerns the actual finite atomic probability measures. -/

noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace DepthPaper

theorem atomicMeasure_singleton {r : ℕ} (z : AtomicPoint r)
    (hz : IsAtomicPoint z) (i : Fin (r + 1)) :
    (atomicMeasure z hz : Measure Overlap) {atomicOverlap z hz i} =
      ENNReal.ofReal (atomicWeight z i) := by
  rw [atomicMeasure_measure, Measure.finsetSum_apply]
  simp only [Measure.smul_apply,
    Measure.dirac_apply' _ (measurableSet_singleton _), smul_eq_mul]
  simp [Set.indicator, (atomicOverlap_injective z hz).eq_iff]

theorem atomicMeasure_injective_fixed_locations {r : ℕ}
    (z w : AtomicPoint r) (hz : IsAtomicPoint z) (hw : IsAtomicPoint w)
    (hloc : z.1 = w.1) (he : atomicMeasure z hz = atomicMeasure w hw) : z = w := by
  have hOverlap (i : Fin (r + 1)) : atomicOverlap z hz i = atomicOverlap w hw i := by
    apply Subtype.ext
    change atomicLocation z i = atomicLocation w i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => simpa only [atomicLocation_succ] using congrFun hloc j
  have hweight (i : Fin (r + 1)) : atomicWeight z i = atomicWeight w i := by
    have hmeasure := congrArg (fun μ : ParisiMeasure =>
      (μ : Measure Overlap) {atomicOverlap z hz i}) he
    rw [atomicMeasure_singleton z hz i, hOverlap i,
      atomicMeasure_singleton w hw i] at hmeasure
    have hh := congrArg ENNReal.toReal hmeasure
    simpa only [ENNReal.toReal_ofReal (hz.2.2 i).le,
      ENNReal.toReal_ofReal (hw.2.2 i).le] using hh
  apply Prod.ext hloc
  funext i
  simpa only [atomicWeight_castSucc] using hweight i.castSucc

end DepthPaper
