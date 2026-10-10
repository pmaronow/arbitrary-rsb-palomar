module

public import FRSB.ForwardExponentialBounds
public import FRSB.ForwardLogBounds

@[expose] public section


/-! Continuity of concrete exponential, product and logarithmic jet
polynomials under pointwise convergence of every genuine spatial jet. -/
noncomputable section
open Filter
open scoped ContDiff Topology
namespace FRSB

lemma iteratedDeriv_exp_formula (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : ℝ) :
    iteratedDeriv (n + 1) (fun y => Real.exp (f y)) x =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        iteratedDeriv (i + 1) f x * iteratedDeriv (n - i) (fun y => Real.exp (f y)) x := by
  have h := exp_neg_mul_iteratedDeriv_formula f (-1) hf n x
  simpa only [neg_neg, one_mul] using h

theorem tendsto_iteratedDeriv_exp_of_jets {A : Type*} {l : Filter A}
    (f : A → ℝ → ℝ) (g : ℝ → ℝ) (hf : ∀ a, ContDiff ℝ ∞ (f a)) (hg : ContDiff ℝ ∞ g)
    (x : ℝ) (hlim : ∀ j, Tendsto (fun a => iteratedDeriv j (f a) x) l (𝓝 (iteratedDeriv j g x)))
    (j : ℕ) :
    Tendsto (fun a => iteratedDeriv j (fun y => Real.exp (f a y)) x) l
      (𝓝 (iteratedDeriv j (fun y => Real.exp (g y)) x)) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero => exact Real.continuous_exp.continuousAt.tendsto.comp (hlim 0)
    | succ n =>
      simp_rw [iteratedDeriv_exp_formula _ (hf _), iteratedDeriv_exp_formula g hg]
      apply tendsto_finset_sum
      intro i hi
      exact ((hlim (i + 1)).const_mul (n.choose i : ℝ)).mul (ih (n - i) (by omega))

theorem tendsto_iteratedDeriv_mul_of_jets {A : Type*} {l : Filter A}
    (f g : A → ℝ → ℝ) (F G : ℝ → ℝ)
    (hf : ∀ a, ContDiff ℝ ∞ (f a)) (hg : ∀ a, ContDiff ℝ ∞ (g a))
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (x : ℝ)
    (hlimf : ∀ j, Tendsto (fun a => iteratedDeriv j (f a) x) l (𝓝 (iteratedDeriv j F x)))
    (hlimg : ∀ j, Tendsto (fun a => iteratedDeriv j (g a) x) l (𝓝 (iteratedDeriv j G x))) (j : ℕ) :
    Tendsto (fun a => iteratedDeriv j (fun y => f a y * g a y) x) l
      (𝓝 (iteratedDeriv j (fun y => F y * G y) x)) := by
  have he (a : A) : iteratedDeriv j (fun y => f a y * g a y) x =
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * iteratedDeriv i (f a) x * iteratedDeriv (j - i) (g a) x :=
    iteratedDeriv_mul ((hf a).of_le (by simp)).contDiffAt ((hg a).of_le (by simp)).contDiffAt
  have he' : iteratedDeriv j (fun y => F y * G y) x =
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * iteratedDeriv i F x * iteratedDeriv (j - i) G x :=
    iteratedDeriv_mul (hF.of_le (by simp)).contDiffAt (hG.of_le (by simp)).contDiffAt
  simp_rw [he, he']
  apply tendsto_finset_sum
  intro i hi
  exact ((hlimf i).const_mul (j.choose i : ℝ)).mul (hlimg (j - i))

lemma iteratedDeriv_negativeLog_formula (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hp : ∀ y, 0 < f y) (n : ℕ) (x : ℝ) :
    iteratedDeriv (n + 1) (fun y => -Real.log (f y)) x =
      (-iteratedDeriv (n + 1) f x - ∑ i ∈ Finset.range n, (n.choose i : ℝ) *
        iteratedDeriv (i + 1) (fun y => -Real.log (f y)) x * iteratedDeriv (n - i) f x) / f x := by
  apply (eq_div_iff (hp x).ne').mpr
  exact negativeLog_iteratedDeriv_recursion f hf hp n x

theorem tendsto_iteratedDeriv_negativeLog_of_jets {A : Type*} {l : Filter A}
    (f : A → ℝ → ℝ) (g : ℝ → ℝ) (hf : ∀ a, ContDiff ℝ ∞ (f a)) (hg : ContDiff ℝ ∞ g)
    (hfp : ∀ a y, 0 < f a y) (hgp : ∀ y, 0 < g y) (x : ℝ)
    (hlim : ∀ j, Tendsto (fun a => iteratedDeriv j (f a) x) l (𝓝 (iteratedDeriv j g x))) (j : ℕ) :
    Tendsto (fun a => iteratedDeriv j (fun y => -Real.log (f a y)) x) l
      (𝓝 (iteratedDeriv j (fun y => -Real.log (g y)) x)) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero =>
      exact ((Real.continuousAt_log (hgp x).ne').tendsto.comp (hlim 0)).neg
    | succ n =>
      have he (a : A) := iteratedDeriv_negativeLog_formula (f a) (hf a) (hfp a) n x
      have he' := iteratedDeriv_negativeLog_formula g hg hgp n x
      simp_rw [he, he']
      apply Tendsto.div _ (hlim 0) (hgp x).ne'
      apply Tendsto.sub (hlim (n + 1)).neg
      apply tendsto_finset_sum
      intro i hi
      exact ((ih (i + 1) (by have hi' := Finset.mem_range.mp hi; omega)).const_mul
        (n.choose i : ℝ)).mul (hlim (n - i))

end FRSB
