module

public import DepthPaper.FiniteCoefficientFamily

set_option backward.privateInPublic true

@[expose] public section


/-! Coefficients outside the active finite support do not change the
genuine mixed model. This transfers actual nondegeneracy to its literal
finite positive coefficient coordinates. -/
noncomputable section
open Set
open scoped BigOperators
namespace DepthPaper

private theorem mixture_eq_coefficients (X Y : FourPapersCommon.AdmissibleEvenMixture)
    (H : X.coefficient=Y.coefficient) : X=Y := by
  cases X
  cases Y
  cases H
  rfl

theorem AdmissibleCovariance.toEvenMixture_eq_of_active_coefficients
    {X Y : AdmissibleCovariance} (hdeg : X.degrees=Y.degrees)
    (hcoef : ∀p∈X.degrees,X.coefficient p=Y.coefficient p) :
    X.toEvenMixture=Y.toEvenMixture := by
  have H : X.toEvenMixture.coefficient=Y.toEvenMixture.coefficient := by
    funext p
    simp only [AdmissibleCovariance.toEvenMixture_coefficient,←hdeg]
    by_cases hp:p∈X.degrees
    · rw [if_pos hp,if_pos hp,hcoef p hp]
    · rw [if_neg hp,if_neg hp]
  exact mixture_eq_coefficients _ _ H

theorem nondegenerate_congr_effective_covariance {X Y : AdmissibleCovariance}
    (H : X.toEvenMixture=Y.toEvenMixture) {r : ℕ} (z : AtomicPoint r)
    (hz : IsAtomicPoint z) : Nondegenerate X z hz↔Nondegenerate Y z hz := by
  have hfun : atomicFunctionalExtension X r=atomicFunctionalExtension Y r := by
    funext u
    unfold atomicFunctionalExtension
    split_ifs with hu
    · simp only [atomicFunctional,parisiFunctional,H]
    · rfl
  simp only [Nondegenerate,IsParisiMinimizer,firstVariation,H,positiveAtomicHessian,hfun]

theorem indexedCovariance_effective_eq {k : ℕ} (X : AdmissibleCovariance)
    (p : Fin (k+1)→ℕ) (hp : ∀i,4≤p i) (he : ∀i,Even (p i))
    (hinj : Function.Injective p) (hdeg : X.degrees=Finset.univ.image p) :
    (indexedCovariance p hp he (fun i=>X.coefficient (p i))
      (fun i=>X.coefficient_pos (p i) (hdeg ▸ Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))).toEvenMixture=
      X.toEvenMixture := by
  apply AdmissibleCovariance.toEvenMixture_eq_of_active_coefficients hdeg.symm
  intro j hj
  obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hj
  exact indexedCovariance_coefficient p hp he hinj _ _ i

theorem nondegenerate_coefficient_locus_nonempty {k r : ℕ}
    (X : AdmissibleCovariance) (p : Fin (k+1)→ℕ)
    (hp : ∀i,4≤p i) (he : ∀i,Even (p i)) (hinj : Function.Injective p)
    (hdeg : X.degrees=Finset.univ.image p) (z : AtomicPoint r)
    (hz : IsAtomicPoint z) (hnd : Nondegenerate X z hz) :
    (nondegenerateCoefficientLocus p hp he r).Nonempty := by
  let c : Fin (k+1)→ℝ:=fun i=>X.coefficient (p i)
  have hc : c∈positiveCoefficientDomain k:=fun i=>X.coefficient_pos (p i)
    (hdeg ▸ Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  refine ⟨c,hc,z,hz,?_⟩
  exact (nondegenerate_congr_effective_covariance
    (indexedCovariance_effective_eq X p hp he hinj hdeg) z hz).mpr hnd

end DepthPaper
