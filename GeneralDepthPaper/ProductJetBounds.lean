module

public import GeneralDepthPaper.PointwiseDerivativeBounds
public import Mathlib.Analysis.Normed.Operator.Mul

@[expose] public section


/-! Local product estimates using genuine pointwise parameter jets. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64

theorem norm_iteratedFDeriv_mul_bound_at {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : E→ℝ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (n : ℕ)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hfb : ∀j:ℕ,j ≤ n→‖iteratedFDeriv ℝ j f x‖ ≤ C)
    (hgb : ∀j:ℕ,j ≤ n→‖iteratedFDeriv ℝ j g x‖ ≤ D) :
    ‖iteratedFDeriv ℝ n (fun y=> f y*g y) x‖ ≤ (2:ℝ)^n*C*D := by
  have H := norm_iteratedFDeriv_bilinear_le_at (ContinuousLinearMap.mul ℝ ℝ) hf hg n
  have hs0 : 0 ≤ ∑i∈Finset.range (n+1),(n.choose i:ℝ)*
      ‖iteratedFDeriv ℝ i f x‖*‖iteratedFDeriv ℝ (n-i) g x‖ := by positivity
  have H' := H.trans ((mul_le_mul_of_nonneg_right
    (ContinuousLinearMap.opNorm_mul_le ℝ ℝ) hs0).trans_eq (one_mul _))
  apply H'.trans
  have he : (∑i∈Finset.range (n+1),(n.choose i:ℝ)*C*D)=(2:ℝ)^n*C*D := by
    rw [←Finset.sum_mul,←Finset.sum_mul,←Nat.cast_sum,Nat.sum_range_choose,Nat.cast_pow,Nat.cast_ofNat]
  rw [←he]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (hfb i hi') (Nat.cast_nonneg _))
    (hgb (n-i) (Nat.sub_le _ _)) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hC)

end GeneralDepthPaper
