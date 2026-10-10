module

public import Mathlib.Analysis.Analytic.IteratedFDeriv
public import Mathlib.Data.Fintype.Perm

@[expose] public section


/-! A quantitative multilinear derivative estimate from a genuine convergent
Fréchet power series. This is used to retain uniform estimates when terminal
parameters range over noncompact Banach balls. -/
noncomputable section
open Set Filter
open scoped Topology NNReal ENNReal
namespace GeneralDepthPaper
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

theorem norm_iteratedFDeriv_le_factorial_coefficient
    {f : E → G} {P : FormalMultilinearSeries ℝ E G} {x : E} {R : ℝ≥0∞}
    (h : HasFPowerSeriesOnBall f P x R) (n : ℕ) :
    ‖iteratedFDeriv ℝ n f x‖ ≤ (n.factorial:ℝ)*‖P n‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
  intro v
  rw [h.iteratedFDeriv_eq_sum_of_completeSpace v]
  calc
    ‖∑σ : Equiv.Perm (Fin n),P n (fun i => v (σ i))‖ ≤
        ∑σ : Equiv.Perm (Fin n),‖P n (fun i => v (σ i))‖ := norm_sum_le _ _
    _ ≤ ∑σ : Equiv.Perm (Fin n),‖P n‖*(∏i,‖v (σ i)‖) :=
      Finset.sum_le_sum (fun σ _ => (P n).le_opNorm _)
    _ = ∑σ : Equiv.Perm (Fin n),‖P n‖*(∏i,‖v i‖) := by
      apply Finset.sum_congr rfl
      intro σ _
      exact congrArg (fun z : ℝ => ‖P n‖*z) (Equiv.prod_comp (σ : Fin n ≃ Fin n) (fun i => ‖v i‖))
    _ = ((n.factorial:ℝ)*‖P n‖)*(∏i,‖v i‖) := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul]
      ring

theorem norm_iteratedFDeriv_le_of_geometric_coefficients
    {f : E → G} {P : FormalMultilinearSeries ℝ E G} {x : E} {R : ℝ≥0∞}
    (h : HasFPowerSeriesOnBall f P x R) (r C : ℝ) (hr : 0 < r)
    (hc : ∀n,‖P n‖*r^n ≤ C) (n : ℕ) :
    ‖iteratedFDeriv ℝ n f x‖ ≤ (n.factorial:ℝ)*C/r^n := by
  have hp := (le_div_iff₀ (pow_pos hr n)).mpr (hc n)
  exact (norm_iteratedFDeriv_le_factorial_coefficient h n).trans
    ((mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)).trans_eq (by ring))

end GeneralDepthPaper
