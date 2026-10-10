module

public import GeneralDepthPaper.RevisedBridge
public import DepthPaper.RevisedNondegeneracy

@[expose] public section

/-! The revised paper's nondegeneracy condition, without a Hessian premise.
The actual positive atomic Hessian is derived from these conditions. The
subcritical origin condition is stated separately, as in admissibility. -/
noncomputable section
open Set
open scoped Topology
namespace GeneralDepthPaper

/-- Nondegeneracy from the revised paper: the actual atomic probability
measure globally minimizes the actual Parisi functional; its first
variation is nonpositive with exactly the prescribed contact set, and
has strictly negative second derivative at every positive support atom. -/
def PaperNondegenerate (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) : Prop :=
  IsParisiMinimizer Ξ (atomicMeasure z hz) ∧
    (∀q∈Icc (0:ℝ) 1,firstVariation Ξ (atomicMeasure z hz) q≤0 ∧
      (firstVariation Ξ (atomicMeasure z hz) q=0 ↔ ∃i,q=atomicLocation z i)) ∧
    (∀i : Fin r,closedJet 1 2 (firstVariation Ξ (atomicMeasure z hz)) (z.1 i)<0)

@[simp] theorem paperNondegenerate_iff_revised (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) :
    DepthPaper.RevisedCovariance.Nondegenerate Ξ.toRevisedCovariance z
      ((revised_isAtomicPoint z).mpr hz) ↔ PaperNondegenerate Ξ z hz := by
  unfold DepthPaper.RevisedCovariance.Nondegenerate PaperNondegenerate
  rw [revised_atomicMeasure z hz]
  simp only [revised_isParisiMinimizer,revised_firstVariation,
    revised_atomicLocation,revised_closedJet]

/-- The Hessian conclusion is proved for the actual atomic functional,
using the actual model's control comparison and supporting plane. -/
theorem positiveAtomicHessian_of_paperNondegenerate (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (hND : PaperNondegenerate Ξ z hz) :
    positiveAtomicHessian Ξ z := by
  have hR := (paperNondegenerate_iff_revised Ξ z hz).mpr hND
  have hH := DepthPaper.RevisedCovariance.positiveAtomicHessian_of_nondegenerate
    Ξ.toRevisedCovariance z ((revised_isAtomicPoint z).mpr hz) hR
  apply positiveAtomicHessian_of_revised Ξ z
  simpa only [DepthPaper.RevisedCovariance.positiveAtomicHessian] using hH

/-- The internal predicate's Hessian field follows from paper
nondegeneracy; its remaining origin field is precisely admissibility. -/
theorem nondegenerate_of_paperNondegenerate (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (hND : PaperNondegenerate Ξ z hz)
    (hsub : Ξ.IsSubcritical) : Nondegenerate Ξ z hz := by
  exact ⟨hND.1,hND.2.1,hND.2.2,
    positiveAtomicHessian_of_paperNondegenerate Ξ z hz hND,hsub⟩

theorem nondegenerate_iff_paperNondegenerate_and_subcritical
    (Ξ : AdmissibleCovariance) {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z) :
    Nondegenerate Ξ z hz ↔ PaperNondegenerate Ξ z hz ∧ Ξ.IsSubcritical := by
  constructor
  · intro hND
    exact ⟨⟨hND.1,hND.2.1,hND.2.2.1⟩,hND.2.2.2.2⟩
  · rintro ⟨hND,hsub⟩
    exact nondegenerate_of_paperNondegenerate Ξ z hz hND hsub

end GeneralDepthPaper
