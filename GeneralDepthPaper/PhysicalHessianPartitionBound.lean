module

public import GeneralDepthPaper.PhysicalVolatility

@[expose] public section

/-! A deterministic norm estimate for transported Hessian stochastic sums.
Monotone volatility increments telescope, so this estimate needs neither
random-coefficient independence nor cross-term orthogonality. -/
noncomputable section
open Set
open scoped BigOperators NNReal
namespace GeneralDepthPaper

variable {E : Type*} [NormedAddCommGroup E]

/-- The triangle inequality and telescoping volatility increments give a
mesh bound for the sum of the genuine individual error terms. -/
theorem physicalHessianPartition_norm_le (Ξ : AdmissibleCovariance)
    (q : ℕ → ℝ≥0) (N : ℕ) (d : ℝ) (z : ℕ → E)
    (hz : ∀ i < N, ‖z i‖ ≤
      (physicalVolatility Ξ (q (i+1))-physicalVolatility Ξ (q i))*Real.sqrt d) :
    ‖∑ i ∈ Finset.range N, z i‖ ≤
      (physicalVolatility Ξ (q N)-physicalVolatility Ξ (q 0))*Real.sqrt d := by
  calc
    _ ≤ ∑ i ∈ Finset.range N, ‖z i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range N,
        (physicalVolatility Ξ (q (i+1))-physicalVolatility Ξ (q i))*Real.sqrt d := by
      apply Finset.sum_le_sum
      intro i hi
      exact hz i (Finset.mem_range.mp hi)
    _ = (physicalVolatility Ξ (q N)-physicalVolatility Ξ (q 0))*Real.sqrt d := by
      rw [←Finset.sum_mul,
        Finset.sum_range_sub (fun i => physicalVolatility Ξ (q i)) N]

/-- On the closed physical unit interval the same error is bounded by
the literal terminal volatility times the square root of the mesh. -/
theorem physicalHessianPartition_norm_le_endpoint (Ξ : AdmissibleCovariance)
    (q : ℕ → ℝ≥0) (N : ℕ) (d : ℝ) (z : ℕ → E)
    (hq : q N ≤ 1)
    (hz : ∀ i < N, ‖z i‖ ≤
      (physicalVolatility Ξ (q (i+1))-physicalVolatility Ξ (q i))*Real.sqrt d) :
    ‖∑ i ∈ Finset.range N, z i‖ ≤ Real.sqrt (Ξ.second 1)*Real.sqrt d := by
  apply (physicalHessianPartition_norm_le Ξ q N d z hz).trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg d)
  exact (sub_le_self _ (physicalVolatility_nonneg Ξ (q 0))).trans
    (physicalVolatility_le_one Ξ hq)

end GeneralDepthPaper
