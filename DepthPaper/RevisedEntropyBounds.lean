module

public import DepthPaper.RevisedEntropyTerminal
public import FourPapersCommon.FiniteEntropy

@[expose] public section

/-! The literal diffusion entropy integrand is the Shannon entropy of the
two positive spin weights. In particular it is strictly positive and bounded
by `log 2`, giving the integrability needed by the diffusion identity. -/

noncomputable section
open scoped BigOperators

namespace DepthPaper
open FourPapersCommon
set_option maxHeartbeats 800000

def revisedSpinWeight (x : ℝ) (b : Bool) : ℝ :=
  Real.exp (if b then x else -x) / (2 * Real.cosh x)

theorem revisedSpinWeight_pos (x : ℝ) (b : Bool) :
    0 < revisedSpinWeight x b := by
  unfold revisedSpinWeight
  positivity

theorem revisedSpinWeight_total (x : ℝ) :
    (∑ b : Bool, revisedSpinWeight x b) = 1 := by
  simp only [Fintype.sum_bool, revisedSpinWeight, Bool.false_eq_true,
    ite_false, ite_true]
  rw [← add_div, Real.cosh_eq]
  field_simp

def revisedSpinProbability (x : ℝ) : StrictFiniteProbability Bool where
  weight := revisedSpinWeight x
  positive := revisedSpinWeight_pos x
  total := revisedSpinWeight_total x

theorem revisedSpinWeight_lt_one (x : ℝ) (b : Bool) :
    revisedSpinWeight x b < 1 := by
  have ht := revisedSpinWeight_total x
  simp only [Fintype.sum_bool] at ht
  cases b <;> have hp := revisedSpinWeight_pos x true <;>
    have hn := revisedSpinWeight_pos x false <;> linarith

theorem revisedSpinProbability_entropy (x : ℝ) :
    (revisedSpinProbability x).entropy = revisedSpinEntropy x := by
  unfold StrictFiniteProbability.entropy revisedSpinProbability
  simp only [Fintype.sum_bool, revisedSpinWeight, Bool.false_eq_true,
    ite_false, ite_true]
  rw [Real.log_div (Real.exp_ne_zero _) (by positivity : 2 * Real.cosh x ≠ 0),
    Real.log_div (Real.exp_ne_zero _) (by positivity : 2 * Real.cosh x ≠ 0),
    Real.log_exp, Real.log_exp,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.cosh_pos x).ne']
  unfold revisedSpinEntropy
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  field_simp
  ring

theorem revisedSpinEntropy_pos (x : ℝ) : 0 < revisedSpinEntropy x := by
  rw [← revisedSpinProbability_entropy]
  unfold StrictFiniteProbability.entropy
  simp only [Fintype.sum_bool, revisedSpinProbability]
  have hp := mul_neg_of_pos_of_neg (revisedSpinWeight_pos x true)
    (Real.log_neg (revisedSpinWeight_pos x true) (revisedSpinWeight_lt_one x true))
  have hn := mul_neg_of_pos_of_neg (revisedSpinWeight_pos x false)
    (Real.log_neg (revisedSpinWeight_pos x false) (revisedSpinWeight_lt_one x false))
  linarith

def revisedUniformSpinProbability : StrictFiniteProbability Bool where
  weight := fun _ => 1 / 2
  positive := fun _ => by norm_num
  total := by simp

theorem revisedSpinEntropy_le_log_two (x : ℝ) :
    revisedSpinEntropy x ≤ Real.log 2 := by
  let p := revisedSpinProbability x
  have h := p.relative_entropy_nonneg revisedUniformSpinProbability
  have he : (∑ b : Bool, p.weight b *
      Real.log (p.weight b / revisedUniformSpinProbability.weight b)) =
      Real.log 2 - p.entropy := by
    change (∑ b : Bool, p.weight b * Real.log (p.weight b / (1 / 2 : ℝ))) = _
    simp_rw [Real.log_div (p.positive _).ne' (by norm_num : (1 / 2 : ℝ) ≠ 0)]
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_one]
    simp only [sub_neg_eq_add, zero_sub, mul_add, Finset.sum_add_distrib,
      ← Finset.sum_mul, p.total, one_mul, StrictFiniteProbability.entropy]
    ring
  rw [he] at h
  rw [← revisedSpinProbability_entropy]
  change p.entropy ≤ Real.log 2
  linarith

theorem norm_revisedEntropyTerminalDirection_le_log_two (x : ℝ) :
    ‖terminalValue revisedEntropyTerminalDirection x‖ ≤ Real.log 2 := by
  have hp := revisedSpinEntropy_pos x
  have hu := revisedSpinEntropy_le_log_two x
  rw [revisedSpinEntropy_eq_terminalDirection] at hp hu
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  linarith

end DepthPaper
