module

public import Mathlib

@[expose] public section


/-! The closed-interval regularity argument of Lemma 6.3. The index set is
arbitrary: in the application it consists of all polynomials in the spatial
jets. Closure under both generator polynomials is what makes the induction
work. This file supplies the analytic bootstrap, not the stochastic moment
identities that are its explicit inputs. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace FRSB

/-- An integral identity with a continuous integrand yields genuine within
 derivatives at both physical endpoints as well as at interior times. -/
theorem hasDerivWithinAt_of_interval_identity (e d : ℝ → ℝ) (q : ℝ)
    (hd : ContinuousOn d (Icc 0 q))
    (he : ∀ t ∈ Icc (0 : ℝ) q, e t = e 0 + ∫ s in 0..t, d s)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) q) :
    HasDerivWithinAt e (d t) (Icc 0 q) t := by
  have : Fact (t ∈ Icc (0 : ℝ) q) := ⟨ht⟩
  have hz : (0 : ℝ) ∈ Icc 0 q := ⟨le_rfl, ht.1.trans ht.2⟩
  have hi : HasDerivWithinAt (fun u => ∫ s in 0..u, d s) (d t) (Icc 0 q) t :=
    intervalIntegral.integral_hasDerivWithinAt_right
      ((hd.mono (uIcc_subset_Icc hz ht)).intervalIntegrable)
      (hd.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hd t ht)
  exact (hi.const_add (e 0)).congr he (he t ht)

/-- All closed-interval derivatives are bootstrapped simultaneously. The
 derivative of each moment is a linear combination of two other moments,
 with coefficient given by a positive-denominator quotient of moments. -/
theorem moments_contDiffOn_closed_interval
    {ι : Type*} (e : ι → ℝ → ℝ) (f₀ f₁ : ι → ι) (iA iB : ι)
    (β q : ℝ) (hq : 0 < q)
    (he : ∀ i, ContinuousOn (e i) (Icc 0 q))
    (hB : ∀ t ∈ Icc (0 : ℝ) q, 0 < e iB t)
    (hderiv : ∀ i t, t ∈ Icc (0 : ℝ) q →
      HasDerivWithinAt (e i)
        (β ^ 2 * (e (f₀ i) t + (e iA t / (2 * e iB t)) * e (f₁ i) t))
        (Icc 0 q) t) :
    (∀ i, ContDiffOn ℝ ∞ (e i) (Icc 0 q)) ∧
      ContDiffOn ℝ ∞ (fun t => e iA t / (2 * e iB t)) (Icc 0 q) := by
  have hu : UniqueDiffOn ℝ (Icc (0 : ℝ) q) := uniqueDiffOn_Icc hq
  have hn : ∀ n : ℕ, ∀ i, ContDiffOn ℝ n (e i) (Icc 0 q) := by
    intro n
    induction n with
    | zero => intro i; exact contDiffOn_zero.mpr (he i)
    | succ n ih =>
      intro i
      rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_derivWithin hu]
      refine ⟨fun t ht => (hderiv i t ht).differentiableWithinAt, by simp, ?_⟩
      have ha : ContDiffOn ℝ (n : ℕ∞ω)
          (fun t => e iA t / (2 * e iB t)) (Icc 0 q) :=
        (ih iA).div (contDiffOn_const.mul (ih iB)) (fun t ht => by have := hB t ht; positivity)
      have hc : ContDiffOn ℝ (n : ℕ∞ω)
          (fun t => β ^ 2 * (e (f₀ i) t + (e iA t / (2 * e iB t)) * e (f₁ i) t))
          (Icc 0 q) := contDiffOn_const.mul ((ih (f₀ i)).add (ha.mul (ih (f₁ i))))
      exact hc.congr (fun t ht => (hderiv i t ht).derivWithin (hu t ht))
  have hsmooth : ∀ i, ContDiffOn ℝ ∞ (e i) (Icc 0 q) := by
    intro i
    exact contDiffOn_infty.mpr (fun n => hn n i)
  refine ⟨hsmooth, (hsmooth iA).div (contDiffOn_const.mul (hsmooth iB)) ?_⟩
  intro t ht
  have := hB t ht
  positivity

/-- Integral-equation version of the moment bootstrap; differentiability is
 derived here by the closed-interval FTC and is not an additional premise. -/
theorem moments_contDiffOn_of_interval_identity
    {ι : Type*} (e : ι → ℝ → ℝ) (f₀ f₁ : ι → ι) (iA iB : ι)
    (β q : ℝ) (hq : 0 < q)
    (he : ∀ i, ContinuousOn (e i) (Icc 0 q))
    (hB : ∀ t ∈ Icc (0 : ℝ) q, 0 < e iB t)
    (hi : ∀ i t, t ∈ Icc (0 : ℝ) q →
      e i t = e i 0 + ∫ s in 0..t,
        β ^ 2 * (e (f₀ i) s + (e iA s / (2 * e iB s)) * e (f₁ i) s)) :
    (∀ i, ContDiffOn ℝ ∞ (e i) (Icc 0 q)) ∧
      ContDiffOn ℝ ∞ (fun t => e iA t / (2 * e iB t)) (Icc 0 q) := by
  apply moments_contDiffOn_closed_interval e f₀ f₁ iA iB β q hq he hB
  intro i t ht
  have ha : ContinuousOn (fun s => e iA s / (2 * e iB s)) (Icc 0 q) :=
    (he iA).div (continuousOn_const.mul (he iB))
      (fun s hs => by have := hB s hs; positivity)
  apply hasDerivWithinAt_of_interval_identity _ _ q _ (hi i) t ht
  exact continuousOn_const.mul ((he (f₀ i)).add (ha.mul (he (f₁ i))))

end FRSB
