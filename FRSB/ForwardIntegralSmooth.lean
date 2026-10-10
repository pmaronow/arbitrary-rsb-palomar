module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

@[expose] public section


/-! Uniformly bounded positive-order derivatives permit all-order
differentiation through an actual finite-measure integral. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace FRSB

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]

theorem hasDerivAt_integral_uniform (F D : ℝ → Ω → ℝ) (x K : ℝ)
    (hmeas : ∀ y, AEStronglyMeasurable (F y) P)
    (hi : Integrable (F x) P) (hDmeas : AEStronglyMeasurable (D x) P)
    (hbound : ∀ y sample, ‖D y sample‖ ≤ K)
    (hder : ∀ y sample, HasDerivAt (fun z => F z sample) (D y sample) y) :
    HasDerivAt (fun y => ∫ sample, F y sample ∂P) (∫ sample, D x sample ∂P) x := by
  have hout := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := P) (F := F) (F' := D) (bound := fun _ => K) (s := univ)
    (x₀ := x) (Filter.univ_mem : univ ∈ 𝓝 x)
    (Filter.Eventually.of_forall hmeas) hi hDmeas
    (Filter.Eventually.of_forall fun sample y _ => hbound y sample)
    (integrable_const K) (Filter.Eventually.of_forall fun sample y _ => hder y sample)
  exact hout.2

theorem iteratedDeriv_integral_uniform (F : ℝ → Ω → ℝ)
    (hF : ∀ sample, ContDiff ℝ ∞ (fun x => F x sample))
    (hi : ∀ x, Integrable (F x) P)
    (hm : ∀ j x, AEStronglyMeasurable (fun sample =>
      iteratedDeriv j (fun y => F y sample) x) P)
    (K : ℕ → ℝ) (hb : ∀ j x sample,
      ‖iteratedDeriv (j + 1) (fun y => F y sample) x‖ ≤ K j)
    (j : ℕ) (x : ℝ) :
    iteratedDeriv j (fun y => ∫ sample, F y sample ∂P) x =
      ∫ sample, iteratedDeriv j (fun y => F y sample) x ∂P := by
  induction j generalizing x with
  | zero => simp only [iteratedDeriv_zero]
  | succ j ih =>
    have he : iteratedDeriv j (fun y => ∫ sample, F y sample ∂P) =
        fun y => ∫ sample, iteratedDeriv j (fun z => F z sample) y ∂P := funext ih
    have hi' : Integrable (fun sample => iteratedDeriv j (fun z => F z sample) x) P := by
      cases j with
      | zero => simpa only [iteratedDeriv_zero] using hi x
      | succ j =>
        exact (integrable_const (K j)).mono' (hm (j + 1) x)
          (Filter.Eventually.of_forall (hb j x))
    have hd := hasDerivAt_integral_uniform P
      (fun y sample => iteratedDeriv j (fun z => F z sample) y)
      (fun y sample => iteratedDeriv (j + 1) (fun z => F z sample) y) x (K j)
      (hm j) hi' (hm (j + 1) x) (hb j)
      (fun y sample => by
        rw [iteratedDeriv_succ]
        exact ((hF sample).differentiable_iteratedDeriv j
          (by exact_mod_cast WithTop.coe_lt_top j) y).hasDerivAt)
    rw [iteratedDeriv_succ, he]
    exact hd.deriv

theorem contDiff_integral_uniform (F : ℝ → Ω → ℝ)
    (hF : ∀ sample, ContDiff ℝ ∞ (fun x => F x sample))
    (hi : ∀ x, Integrable (F x) P)
    (hm : ∀ j x, AEStronglyMeasurable (fun sample =>
      iteratedDeriv j (fun y => F y sample) x) P)
    (K : ℕ → ℝ) (hb : ∀ j x sample,
      ‖iteratedDeriv (j + 1) (fun y => F y sample) x‖ ≤ K j) :
    ContDiff ℝ ∞ (fun x => ∫ sample, F x sample ∂P) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro j hj x
  have he : iteratedDeriv j (fun y => ∫ sample, F y sample ∂P) =
      fun y => ∫ sample, iteratedDeriv j (fun z => F z sample) y ∂P :=
    funext (iteratedDeriv_integral_uniform P F hF hi hm K hb j)
  rw [he]
  have hi' : Integrable (fun sample => iteratedDeriv j (fun z => F z sample) x) P := by
    cases j with
    | zero => simpa only [iteratedDeriv_zero] using hi x
    | succ j =>
      exact (integrable_const (K j)).mono' (hm (j + 1) x)
        (Filter.Eventually.of_forall (hb j x))
  exact (hasDerivAt_integral_uniform P
    (fun y sample => iteratedDeriv j (fun z => F z sample) y)
    (fun y sample => iteratedDeriv (j + 1) (fun z => F z sample) y) x (K j)
    (hm j) hi' (hm (j + 1) x) (hb j)
    (fun y sample => by
      rw [iteratedDeriv_succ]
      exact ((hF sample).differentiable_iteratedDeriv j
        (by exact_mod_cast WithTop.coe_lt_top j) y).hasDerivAt)).differentiableAt

end FRSB
