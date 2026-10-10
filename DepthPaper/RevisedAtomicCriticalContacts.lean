module

public import GeneralDepthPaper.RevisedCovarianceInverse
public import GeneralDepthPaper.RevisedBridge
public import GeneralDepthPaper.AtomicStationary

@[expose] public section

/-! Genuine first-variation contact equations at a critical point of the
actual finite-atomic Parisi functional. This is an exact interface transfer
from the degree-at-least-two coordinate calculus; global minimality and
subcriticality are not required. -/
noncomputable section
open MeasureTheory
namespace DepthPaper.RevisedCovariance

theorem atomic_stationary_contacts (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (hs : fderiv ℝ (atomicFunctionalExtension Ξ r) z=0) :
    (∀i : Fin (r+1),firstVariation Ξ (atomicMeasure z hz) (atomicLocation z i)=0) ∧
    (∀i : Fin r,deriv (firstVariation Ξ (atomicMeasure z hz)) (z.1 i)=0) := by
  have hF : GeneralDepthPaper.atomicFunctionalExtension Ξ.toGeneralCovariance r=
      atomicFunctionalExtension Ξ r := by
    rw [←GeneralDepthPaper.revised_atomicFunctionalExtension,
      toGeneralCovariance_toRevisedCovariance]
  have hsG : fderiv ℝ
      (GeneralDepthPaper.atomicFunctionalExtension Ξ.toGeneralCovariance r) z=0 := by
    rw [hF]
    exact hs
  have hcontact := GeneralDepthPaper.atomic_stationary_contacts Ξ.toGeneralCovariance z hz hsG
  have hf : GeneralDepthPaper.firstVariation Ξ.toGeneralCovariance
      (GeneralDepthPaper.atomicMeasure z hz)=firstVariation Ξ (atomicMeasure z hz) := by
    rw [←GeneralDepthPaper.revised_firstVariation,toGeneralCovariance_toRevisedCovariance]
    rfl
  simpa only [hf,←GeneralDepthPaper.revised_atomicLocation] using hcontact

theorem integral_firstVariation_atomic_stationary (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (hs : fderiv ℝ (atomicFunctionalExtension Ξ r) z=0) :
    (∫q:Overlap,firstVariation Ξ (atomicMeasure z hz) q
      ∂(atomicMeasure z hz : Measure Overlap))=0 := by
  have hzero := (atomic_stationary_contacts Ξ z hz hs).1
  apply integral_eq_zero_of_ae
  filter_upwards [show ∀ᵐq ∂(atomicMeasure z hz : Measure Overlap),
      q∈(atomicMeasure z hz : Measure Overlap).support from Measure.support_mem_ae] with q hq
  rw [support_atomicMeasure] at hq
  obtain ⟨i,rfl⟩ := hq
  exact hzero i

end DepthPaper.RevisedCovariance
