module

public import GeneralDepthPaper.RevisedCovarianceBridge
public import GeneralDepthPaper.Nondegeneracy
public import DepthPaper.RevisedAtomicStationary

@[expose] public section

/-! Exact correspondence between the general finite-coefficient proof
development and the revised finite-support interface. The probability
measure, physical functional, first variation, and actual chart Hessian
are all retained. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace GeneralDepthPaper

@[simp] theorem revised_isAtomicPoint {r : ℕ} (z : AtomicPoint r) :
    DepthPaper.IsAtomicPoint z ↔ IsAtomicPoint z := Iff.rfl

@[simp] theorem revised_atomicLocation {r : ℕ} (z : AtomicPoint r) (i : Fin (r+1)) :
    DepthPaper.atomicLocation z i=atomicLocation z i := rfl

@[simp] theorem revised_atomicWeight {r : ℕ} (z : AtomicPoint r) (i : Fin (r+1)) :
    DepthPaper.atomicWeight z i=atomicWeight z i := rfl

@[simp] theorem revised_atomicMeasure {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z) :
    DepthPaper.atomicMeasure z ((revised_isAtomicPoint z).mpr hz)=atomicMeasure z hz := rfl

@[simp] theorem revised_atomicFunctional (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) :
    DepthPaper.RevisedCovariance.atomicFunctional Ξ.toRevisedCovariance z
      ((revised_isAtomicPoint z).mpr hz)=atomicFunctional Ξ z hz := rfl

@[simp] theorem revised_atomicFunctionalExtension (Ξ : AdmissibleCovariance) (r : ℕ) :
    DepthPaper.RevisedCovariance.atomicFunctionalExtension Ξ.toRevisedCovariance r=
      atomicFunctionalExtension Ξ r := rfl

@[simp] theorem revised_closedJet (bar : ℝ) (j : ℕ) (f : ℝ→ℝ) :
    DepthPaper.closedJet bar j f=closedJet bar j f := rfl

theorem positiveAtomicHessian_of_revised (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r)
    (h : ∀v:DepthPaper.AtomicPoint r,v≠0→
      0<(fderiv ℝ (fun y=>fderiv ℝ
        (DepthPaper.RevisedCovariance.atomicFunctionalExtension Ξ.toRevisedCovariance r) y) z v) v) :
    positiveAtomicHessian Ξ z := by
  simpa only [positiveAtomicHessian,revised_atomicFunctionalExtension] using h

/-- Transfer of actual revised data to the internal general-development
predicate. The Hessian premise is precisely the actual chart Hessian and
is intended to be discharged by the separately proved paper Hessian result. -/
theorem nondegenerate_of_revised_data (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (hmin : DepthPaper.RevisedCovariance.IsParisiMinimizer Ξ.toRevisedCovariance
      (DepthPaper.atomicMeasure z ((revised_isAtomicPoint z).mpr hz)))
    (hcontacts : ∀q∈Icc (0:ℝ) 1,
      DepthPaper.RevisedCovariance.firstVariation Ξ.toRevisedCovariance
        (DepthPaper.atomicMeasure z ((revised_isAtomicPoint z).mpr hz)) q≤0 ∧
      (DepthPaper.RevisedCovariance.firstVariation Ξ.toRevisedCovariance
        (DepthPaper.atomicMeasure z ((revised_isAtomicPoint z).mpr hz)) q=0 ↔
          ∃i,q=DepthPaper.atomicLocation z i))
    (hcurv : ∀i:Fin r,DepthPaper.closedJet 1 2
      (DepthPaper.RevisedCovariance.firstVariation Ξ.toRevisedCovariance
        (DepthPaper.atomicMeasure z ((revised_isAtomicPoint z).mpr hz))) (z.1 i)<0)
    (hhess : ∀v:DepthPaper.AtomicPoint r,v≠0→
      0<(fderiv ℝ (fun y=>fderiv ℝ
        (DepthPaper.RevisedCovariance.atomicFunctionalExtension Ξ.toRevisedCovariance r) y) z v) v)
    (hsub : Ξ.IsSubcritical) : Nondegenerate Ξ z hz := by
  have hμ := revised_atomicMeasure z hz
  rw [hμ] at hmin hcontacts hcurv
  refine ⟨?_,?_,?_,positiveAtomicHessian_of_revised Ξ z hhess,hsub⟩
  · simpa only [revised_isParisiMinimizer] using hmin
  · simpa only [revised_firstVariation,revised_atomicLocation] using hcontacts
  · simpa only [revised_firstVariation,revised_closedJet] using hcurv

end GeneralDepthPaper
