module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic

@[expose] public section


/-! Strict finite probability laws and the genuine logarithmic relative
entropy inequality. Normalization and positivity are mathematical data. -/
noncomputable section
open scoped BigOperators
namespace FourPapersCommon

structure StrictFiniteProbability (α : Type*) [Fintype α] where
  weight : α → ℝ
  positive : ∀ x,0 < weight x
  total : ∑ x,weight x = 1

namespace StrictFiniteProbability
variable {α : Type*} [Fintype α]

def entropy (p : StrictFiniteProbability α) : ℝ := -∑ x,p.weight x*Real.log (p.weight x)

theorem weight_le_one (p : StrictFiniteProbability α) (x : α) : p.weight x ≤ 1 := by
  rw [← p.total]
  exact Finset.single_le_sum (fun y _ => (p.positive y).le) (Finset.mem_univ x)

theorem entropy_nonneg (p : StrictFiniteProbability α) : 0 ≤ p.entropy := by
  unfold entropy
  apply neg_nonneg.mpr
  apply Finset.sum_nonpos
  intro x _
  exact mul_nonpos_of_nonneg_of_nonpos (p.positive x).le
    (Real.log_nonpos (p.positive x).le (p.weight_le_one x))

theorem weighted_log_ratio_nonpos (p : StrictFiniteProbability α) (r : α → ℝ)
    (hr : ∀ x,0 < r x) (ht : ∑ x,p.weight x*r x = 1) :
    (∑ x,p.weight x*Real.log (r x)) ≤ 0 := by
  calc
    _ ≤ ∑ x,p.weight x*(r x-1) := Finset.sum_le_sum (fun x _ =>
      mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (hr x)) (p.positive x).le)
    _ = 0 := by simp only [mul_sub,mul_one,Finset.sum_sub_distrib,ht,p.total,sub_self]

theorem relative_entropy_nonneg (p q : StrictFiniteProbability α) :
    0 ≤ ∑ x,p.weight x*Real.log (p.weight x/q.weight x) := by
  have ht : ∑ x,p.weight x*(q.weight x/p.weight x) = 1 := by
    have he : (fun x => p.weight x*(q.weight x/p.weight x)) = q.weight := by
      funext x
      field_simp [(p.positive x).ne']
    rw [he,q.total]
  have hh := p.weighted_log_ratio_nonpos (fun x => q.weight x/p.weight x)
    (fun x => div_pos (q.positive x) (p.positive x)) ht
  have he : (∑ x,p.weight x*Real.log (q.weight x/p.weight x)) =
      -(∑ x,p.weight x*Real.log (p.weight x/q.weight x)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [Real.log_div (q.positive x).ne' (p.positive x).ne',
      Real.log_div (p.positive x).ne' (q.positive x).ne']
    ring
  rw [he] at hh
  linarith

end StrictFiniteProbability
end FourPapersCommon
