module

public import DepthPaper.RevisedNondegeneracy
public import DepthPaper.RevisedAtomicCriticalContacts

@[expose] public section

/-! The revised manuscript's atomic Hessian lemma, with chart criticality
as its hypothesis. Global minimality is not needed. -/
noncomputable section
namespace DepthPaper.RevisedCovariance
open scoped ContDiff

/-- Revised Lemma `lem:atomic-hessian`: a critical atomic chart point with
strict negative first-variation contact curvature has positive definite
actual Parisi Hessian. This holds for every finite positive even covariance,
including a quadratic interaction. -/
theorem atomic_hessian (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (hs : fderiv ℝ (atomicFunctionalExtension Ξ r) z=0)
    (hcurv : ∀i : Fin r,closedJet 1 2 (firstVariation Ξ (atomicMeasure z hz)) (z.1 i)<0) :
    positiveAtomicHessian Ξ z := by
  have hc := atomic_stationary_contacts Ξ z hz hs
  exact positiveAtomicHessian_of_contacts_curvature Ξ z hz hc.1 hc.2 hcurv

end DepthPaper.RevisedCovariance
