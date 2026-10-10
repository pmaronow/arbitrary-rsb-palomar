module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section


/-! An actual positive definite Hessian identifies any finite-dimensional
real normed space with its continuous dual. No Euclidean norm is required,
so this applies to finite atomic charts with their product/sup norm. -/
noncomputable section
namespace FourPapersCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem positive_hessian_injective (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v : E,v≠0 → 0 < B v v) : Function.Injective B := by
  intro u v huv
  apply sub_eq_zero.mp
  by_contra hne
  have hz : B (u-v) = 0 := by rw [map_sub,huv,sub_self]
  have he : B (u-v) (u-v) = 0 := by rw [hz];rfl
  have hp := hB (u-v) hne
  linarith

theorem positive_hessian_bijective (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v : E,v≠0 → 0 < B v v) : Function.Bijective B := by
  have hd : Module.finrank ℝ (E →L[ℝ] ℝ) = Module.finrank ℝ E := by
    calc
      _ = Module.finrank ℝ (E →ₗ[ℝ] ℝ) :=
        (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).symm.finrank_eq
      _ = _ := Subspace.dual_finrank_eq
  have hi := positive_hessian_injective B hB
  exact ⟨hi,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd.symm).mp hi⟩

def positiveHessianEquivalence (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v : E,v≠0 → 0 < B v v) : E ≃L[ℝ] (E →L[ℝ] ℝ) :=
  ContinuousLinearEquiv.ofBijective B
    (LinearMap.ker_eq_bot.mpr (positive_hessian_bijective B hB).1)
    (LinearMap.range_eq_top.mpr (positive_hessian_bijective B hB).2)

@[simp] theorem positiveHessianEquivalence_apply (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v : E,v≠0 → 0 < B v v) (v : E) :
    positiveHessianEquivalence B hB v = B v := rfl

end FourPapersCommon
