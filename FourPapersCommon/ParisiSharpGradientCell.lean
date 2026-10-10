module

public import FourPapersCommon.BoundedBurgersComparison
public import Paper.ParisiFiniteGradientTime

set_option backward.privateInPublic true

@[expose] public section


/-!
# Sharp comparison for actual finite Parisi gradient slabs

The comparison is applied to the actual Cole--Hopf gradients after the forward
time change `u = β² (b - r)`.  Their spatial derivatives remain in `[0, 1]`,
including mass zero.  The actual slab time equation supplies the Burgers PDE;
no comparison equation or final estimate is assumed.
-/

open Set
open SpinGlass SpinGlass.Targets

namespace FourPapersCommon

private noncomputable def sharpForwardSlab {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) (m b : ℝ) (p : ℝ × ℝ) : ℝ :=
  Paper.parisiSlabGradient s β j m b (b - p.1 / β ^ 2) p.2

private noncomputable def sharpForwardSlabTime {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) (m b : ℝ) (p : ℝ × ℝ) : ℝ :=
  (1 / 2 : ℝ) * Paper.parisiSlabThird s β j m b (b - p.1 / β ^ 2) p.2 +
    m * Paper.parisiSlabGradient s β j m b (b - p.1 / β ^ 2) p.2 *
      Paper.parisiSlabHessian s β j m b (b - p.1 / β ^ 2) p.2

private theorem sharpForwardSlab_continuous {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (b : ℝ) :
    Continuous (sharpForwardSlab s β j m b) := by
  exact (Paper.continuous_parisiSlab s β j hm.1 b).2.1.comp
    (show Continuous (fun p : ℝ × ℝ => (b - p.1 / β ^ 2, p.2)) by fun_prop)

private theorem sharpForwardSlab_hasDerivAt_time {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) (j : ℕ) {m : ℝ}
    (hm : m ∈ Icc (0 : ℝ) 1) (b u x : ℝ) (hu : 0 < u) :
    HasDerivAt (fun v => sharpForwardSlab s β j m b (v, x))
      (sharpForwardSlabTime s β j m b (u, x)) u := by
  have hsq : 0 < β ^ 2 := sq_pos_of_ne_zero hβ
  have ht : b - u / β ^ 2 < b := sub_lt_self _ (div_pos hu hsq)
  have hi : HasDerivAt (fun v : ℝ => b - v / β ^ 2) (-(1 / β ^ 2)) u := by
    have hz := (hasDerivAt_const u b).sub ((hasDerivAt_id u).div_const (β ^ 2))
    have hh : HasDerivAt (fun v : ℝ => b - v / β ^ 2) (0 - 1 / β ^ 2) u :=
      hz.congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => rfl)
    simpa only [zero_sub] using hh
  have hd := (Paper.hasDerivAt_parisiSlabGradient_time s β hβ j hm b x ht).comp u hi
  have heq : -(β ^ 2 / 2) *
      (Paper.parisiSlabThird s β j m b (b - u / β ^ 2) x +
        2 * m * Paper.parisiSlabGradient s β j m b (b - u / β ^ 2) x *
          Paper.parisiSlabHessian s β j m b (b - u / β ^ 2) x) *
        -(1 / β ^ 2) = sharpForwardSlabTime s β j m b (u, x) := by
    dsimp only [sharpForwardSlabTime]
    field_simp [ne_of_gt hsq]
  exact (hd.congr_deriv heq).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun v => rfl)

private theorem sharpForwardSlab_hasDerivAt_space {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) (m b u x : ℝ) :
    HasDerivAt (fun y => sharpForwardSlab s β j m b (u, y))
      (Paper.parisiSlabHessian s β j m b (b - u / β ^ 2) x) x := by
  exact (Paper.hasDerivAt_parisiSlabGradient_spatial s β j m b (b - u / β ^ 2) x).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => rfl)

private theorem sharpForwardSlab_deriv_space {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) (m b u : ℝ) :
    deriv (fun y => sharpForwardSlab s β j m b (u, y)) =
      Paper.parisiSlabHessian s β j m b (b - u / β ^ 2) := by
  funext x
  exact (sharpForwardSlab_hasDerivAt_space s β j m b u x).deriv

private theorem sharpForwardSlab_second_differentiable {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) (m b u x : ℝ) :
    DifferentiableAt ℝ (deriv (fun y => sharpForwardSlab s β j m b (u, y))) x := by
  rw [sharpForwardSlab_deriv_space]
  exact (Paper.hasDerivAt_parisiSlabHessian_spatial s β j m b _ x).differentiableAt

private theorem sharpForwardSlab_pde {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) (m b u x : ℝ) :
    sharpForwardSlabTime s β j m b (u, x) =
      (1 / 2 : ℝ) * deriv (deriv (fun y => sharpForwardSlab s β j m b (u, y))) x +
        m * sharpForwardSlab s β j m b (u, x) *
          deriv (fun y => sharpForwardSlab s β j m b (u, y)) x := by
  simp only [sharpForwardSlab_deriv_space]
  rw [(Paper.hasDerivAt_parisiSlabHessian_spatial s β j m b (b - u / β ^ 2) x).deriv]
  rfl

private theorem sharpForwardSlab_abs_le_one {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (b u x : ℝ) :
    |sharpForwardSlab s β j m b (u, x)| ≤ 1 :=
  Paper.abs_parisiSlabGradient_le_one s β j hm b _ x

private theorem sharpForwardSlab_deriv_mem {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (b u x : ℝ) :
    deriv (fun y => sharpForwardSlab s β j m b (u, y)) x ∈ Icc (0 : ℝ) 1 := by
  rw [sharpForwardSlab_deriv_space]
  refine ⟨Paper.parisiSlabHessian_nonneg s β j hm b _ x, ?_⟩
  have hh := Paper.parisiSlabHessian_add_sq_le_one s β j hm b (b - u / β ^ 2) x
  nlinarith [sq_nonneg (Paper.parisiSlabGradient s β j m b (b - u / β ^ 2) x)]

/-- The sharp actual Cole--Hopf cell comparison, with arbitrary terminal
recursion schemes and masses, including mass zero and repeated endpoints. -/
theorem parisiSlabGradient_sharp_comparison {k l : ℕ}
    (s : RSBScheme k) (t : RSBScheme l) (β : ℝ) (hβ : β ≠ 0) (j i : ℕ)
    {m n : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (hn : n ∈ Icc (0 : ℝ) 1)
    (a b D : ℝ) (hab : a ≤ b) (hD : 0 ≤ D)
    (hterminal : ∀ x : ℝ,
      |Paper.parisiSlabGradient t β i n b b x -
        Paper.parisiSlabGradient s β j m b b x| ≤ D)
    (r : ℝ) (hr : r ∈ Icc a b) (x : ℝ) :
    |Paper.parisiSlabGradient t β i n b r x -
      Paper.parisiSlabGradient s β j m b r x| ≤
      Real.exp (β ^ 2 * (b - r)) * (D + β ^ 2 * (b - r) * |m - n|) := by
  let T : ℝ := β ^ 2 * (b - a)
  have hT : 0 ≤ T := mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hab)
  have hinit : ∀ x : ℝ,
      |sharpForwardSlab t β i n b (0, x) -
        sharpForwardSlab s β j m b (0, x)| ≤ D := by
    simpa only [sharpForwardSlab, zero_div, sub_zero] using hterminal
  have hcomparison := bounded_burgers_comparison T hT m n hm hn
    (sharpForwardSlab s β j m b) (sharpForwardSlab t β i n b)
    (sharpForwardSlabTime s β j m b) (sharpForwardSlabTime t β i n b)
    (sharpForwardSlab_continuous s β j hm b).continuousOn
    (sharpForwardSlab_continuous t β i hn b).continuousOn
    (fun u hu x =>
      (sharpForwardSlab_hasDerivAt_time s β hβ j hm b u x hu.1).hasDerivWithinAt)
    (fun u hu x =>
      (sharpForwardSlab_hasDerivAt_time t β hβ i hn b u x hu.1).hasDerivWithinAt)
    (fun u _ x => (sharpForwardSlab_hasDerivAt_space s β j m b u x).differentiableAt)
    (fun u _ x => (sharpForwardSlab_hasDerivAt_space t β i n b u x).differentiableAt)
    (fun u _ x => sharpForwardSlab_second_differentiable s β j m b u x)
    (fun u _ x => sharpForwardSlab_second_differentiable t β i n b u x)
    (fun u _ x => sharpForwardSlab_pde s β j m b u x)
    (fun u _ x => sharpForwardSlab_pde t β i n b u x)
    (fun u _ x => sharpForwardSlab_abs_le_one s β j hm b u x)
    (fun u _ x => sharpForwardSlab_abs_le_one t β i hn b u x)
    (fun u _ x => sharpForwardSlab_deriv_mem s β j hm b u x)
    (fun u _ x => sharpForwardSlab_deriv_mem t β i hn b u x)
    D hD hinit
  have hur : β ^ 2 * (b - r) ∈ Icc (0 : ℝ) T := by
    refine ⟨mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hr.2), ?_⟩
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left hr.1 b) (sq_nonneg β)
  have htime : b - (β ^ 2 * (b - r)) / β ^ 2 = r := by
    field_simp [pow_ne_zero 2 hβ] <;> ring
  simpa only [sharpForwardSlab, htime] using hcomparison (β ^ 2 * (b - r)) hur x

end FourPapersCommon
