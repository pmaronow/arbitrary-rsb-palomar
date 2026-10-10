module

public import DepthPaper.RevisedAtomicRegularity
public import DepthPaper.RevisedVariationRegularity

@[expose] public section

/-! Genuine chart stationarity and first-variation contacts of an actual
finite atomic global minimizer, for every finite positive even covariance. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace DepthPaper.RevisedCovariance

theorem fderiv_atomicFunctional_eq_zero_of_minimizer (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (hmin : IsParisiMinimizer Ξ (atomicMeasure z hz)) :
    fderiv ℝ (atomicFunctionalExtension Ξ r) z=0 := by
  apply IsLocalMin.fderiv_eq_zero
  filter_upwards [(isOpen_atomic_domain r).mem_nhds hz] with y hy
  rw [atomicFunctionalExtension_eq Ξ z hz,atomicFunctionalExtension_eq Ξ y hy]
  exact hmin (atomicMeasure y hy)

theorem atomic_minimizer_contacts (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (hmin : IsParisiMinimizer Ξ (atomicMeasure z hz)) :
    (∀q∈Icc (0:ℝ) 1,firstVariation Ξ (atomicMeasure z hz) q≤0) ∧
    (∀i : Fin (r+1),firstVariation Ξ (atomicMeasure z hz) (atomicLocation z i)=0) ∧
    (∀i : Fin r,deriv (firstVariation Ξ (atomicMeasure z hz)) (z.1 i)=0) := by
  let μ := atomicMeasure z hz
  have hmax := (isParisiMinimizer_iff_support_firstVariation_max Ξ μ).mp hmin
  have hsupport (i : Fin (r+1)) : atomicOverlap z hz i∈(μ : Measure Overlap).support := by
    rw [support_atomicMeasure]
    exact ⟨i,rfl⟩
  have hnonpos : ∀q∈Icc (0:ℝ) 1,firstVariation Ξ μ q≤0 := by
    intro q hq
    have H := hmax (atomicOverlap z hz 0) (hsupport 0) ⟨q,hq⟩
    change firstVariation Ξ μ q≤firstVariation Ξ μ 0 at H
    simpa only [firstVariation_zero] using H
  have hzero (i : Fin (r+1)) : firstVariation Ξ μ (atomicLocation z i)=0 := by
    have H := hmax (atomicOverlap z hz i) (hsupport i) ⟨0,by norm_num⟩
    change firstVariation Ξ μ 0≤firstVariation Ξ μ (atomicLocation z i) at H
    rw [firstVariation_zero] at H
    exact le_antisymm (hnonpos _ (atomicLocation_mem_unit hz i)) H
  refine ⟨hnonpos,hzero,?_⟩
  intro i
  have hq : z.1 i∈Ioo (0:ℝ) 1 :=
    ⟨by simpa only [atomicLocation_zero,atomicLocation_succ] using hz.1 (Fin.succ_pos i),
      (hz.1.monotone (Fin.le_last i.succ)).trans_lt hz.2.1⟩
  have hloc : IsLocalMax (firstVariation Ξ μ) (z.1 i) := by
    filter_upwards [isOpen_Ioo.mem_nhds hq] with y hy
    have hzi : firstVariation Ξ μ (z.1 i)=0 := hzero i.succ
    rw [hzi]
    exact hnonpos y (Ioo_subset_Icc_self hy)
  exact hloc.deriv_eq_zero

theorem integral_firstVariation_atomic_minimizer (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (hmin : IsParisiMinimizer Ξ (atomicMeasure z hz)) :
    (∫q:Overlap,firstVariation Ξ (atomicMeasure z hz) q
      ∂(atomicMeasure z hz : Measure Overlap))=0 := by
  have hzero := (atomic_minimizer_contacts Ξ z hz hmin).2.1
  apply integral_eq_zero_of_ae
  filter_upwards [show ∀ᵐq ∂(atomicMeasure z hz : Measure Overlap),
      q∈(atomicMeasure z hz : Measure Overlap).support from Measure.support_mem_ae] with q hq
  rw [support_atomicMeasure] at hq
  obtain ⟨i,rfl⟩ := hq
  exact hzero i

end DepthPaper.RevisedCovariance
