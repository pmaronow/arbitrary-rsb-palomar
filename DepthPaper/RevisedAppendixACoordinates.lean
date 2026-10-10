module

public import DepthPaper.RevisedAppendixAFiniteCalculus
public import Mathlib.LinearAlgebra.Multilinear.Basis

@[expose] public section

/-! Quantitative conversion from all coordinate mixed derivatives to the
actual multilinear derivative norm, with constants depending only on the
finite parameter dimension and order. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
namespace DepthPaper
set_option maxHeartbeats 1000000
universe u

def revisedParameterAxis (d : ℕ) (i : Fin d) : Fin d → ℝ := Pi.single i 1

theorem revised_norm_coordinate_multilinear_le {F : Type u}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (d j : ℕ)
    (M : (Fin d → ℝ) [×j]→L[ℝ] F) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ w : Fin j → Fin d, ‖M (fun i => revisedParameterAxis d (w i))‖ ≤ C) :
    ‖M‖ ≤ (d:ℝ)^j*C := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  have he (i : Fin j) : v i = ∑ k : Fin d, v i k • revisedParameterAxis d k := by
    ext k
    simp [revisedParameterAxis,Pi.single_apply]
  have hex : M v = ∑ w : Fin j → Fin d,
      (∏ i, v i (w i)) • M (fun i => revisedParameterAxis d (w i)) := by
    calc
      M v = M (fun i => ∑ k : Fin d, v i k • revisedParameterAxis d k) :=
        congrArg M (funext he)
      _ = _ := by
        change M.toMultilinearMap (fun i => ∑ k : Fin d, v i k • revisedParameterAxis d k) = _
        rw [M.toMultilinearMap.map_sum]
        simp_rw [M.toMultilinearMap.map_smul_univ]
        rfl
  rw [hex]
  calc
    _ ≤ ∑ w : Fin j → Fin d,
        ‖(∏ i, v i (w i)) • M (fun i => revisedParameterAxis d (w i))‖ := norm_sum_le _ _
    _ ≤ ∑ _w : Fin j → Fin d, C*∏ i, ‖v i‖ := by
      apply Finset.sum_le_sum
      intro w _
      rw [norm_smul, norm_prod]
      have hp : (∏ i, ‖v i (w i)‖) ≤ ∏ i, ‖v i‖ :=
        Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => norm_le_pi_norm (v i) _)
      exact (mul_le_mul hp (hb w) (norm_nonneg _) (by positivity)).trans_eq (mul_comm _ _)
    _ = (d:ℝ)^j*C*∏ i, ‖v i‖ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,
        nsmul_eq_mul,Nat.cast_pow]
      ring

end DepthPaper
