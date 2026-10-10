module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pow

set_option backward.privateInPublic true

@[expose] public section


/-! Hessian coercivity in an arbitrary real Banach norm.  The estimates use
the continuous dual, so in particular apply to finite atomic charts with
their product norm. No inner-product identification is assumed. -/
noncomputable section
open Set
open scoped ContDiff
namespace GeneralDepthPaper
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 600000

private theorem coercive_line_convex (f : E → ℝ) {s : Set E} (hs : Convex ℝ s)
    (hf : ∀ z ∈ s, ContDiffAt ℝ ∞ f z) (κ : ℝ)
    (hH : ∀ z ∈ s, ∀ v : E,
      κ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) z v v)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    ConvexOn ℝ (Icc (0 : ℝ) 1)
      (fun t => f (x + t • (y-x)) - κ / 2 * ‖y-x‖ ^ 2 * t^2) := by
  let δ := y-x
  let L := fun t : ℝ => x+t • δ
  have hmem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : L t ∈ s :=
    hs.add_smul_sub_mem hx hy ht
  have hL (t : ℝ) : HasDerivAt L δ t := by
    simpa only [L, one_smul, id_eq] using ((hasDerivAt_id t).smul_const δ).const_add x
  have h1 {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun u => f (L u)) (fderiv ℝ f (L t) δ) t :=
    ((hf _ (hmem ht)).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hL t)
  have h2 {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun u => fderiv ℝ f (L u) δ)
        (fderiv ℝ (fderiv ℝ f) (L t) δ δ) t := by
    have hd := (((hf _ (hmem ht)).fderiv_right (m:=∞) (by simp)).differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hL t)
    simpa [Function.comp_def] using
      hd.clm_apply (hasDerivAt_const t δ)
  have hd1 {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun u => f (L u) - κ / 2 * ‖δ‖ ^ 2 * u^2)
        (fderiv ℝ f (L t) δ - κ * ‖δ‖ ^ 2 * t) t := by
    convert (h1 ht).sub (((hasDerivAt_id t).pow 2).const_mul (κ/2 * ‖δ‖^2)) using 1 <;>
      simp [Function.comp_def, id_eq, Pi.sub_def] <;> ring
  have hd2 {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun u => fderiv ℝ f (L u) δ - κ * ‖δ‖ ^ 2 * u)
        (fderiv ℝ (fderiv ℝ f) (L t) δ δ - κ * ‖δ‖ ^ 2) t := by
    simpa only [mul_one, id_eq, Pi.sub_def] using
      (h2 ht).sub ((hasDerivAt_id t).const_mul (κ * ‖δ‖ ^ 2))
  exact convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1)
    (fun t ht => (hd1 ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd1 (interior_subset ht)).hasDerivWithinAt)
    (fun t ht => (hd2 (interior_subset ht)).hasDerivWithinAt)
    (fun t ht => sub_nonneg.mpr (hH _ (hmem (interior_subset ht)) δ))

/-- The actual quadratic lower tangent estimate, derived from the Hessian. -/
theorem coercive_taylor_lower (f : E → ℝ) {s : Set E} (hs : Convex ℝ s)
    (hf : ∀ z ∈ s, ContDiffAt ℝ ∞ f z) (κ : ℝ)
    (hH : ∀ z ∈ s, ∀ v : E,
      κ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) z v v)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    f x + fderiv ℝ f x (y-x) + κ/2 * ‖y-x‖^2 ≤ f y := by
  have hc := coercive_line_convex f hs hf κ hH hx hy
  have hD : HasDerivAt
      (fun t : ℝ => f (x+t • (y-x)) - κ/2 * ‖y-x‖^2 * t^2)
      (fderiv ℝ f x (y-x)) 0 := by
    have hL : HasDerivAt (fun t : ℝ => x+t • (y-x)) (y-x) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const (y-x)).const_add x
    have hf0 : HasFDerivAt f (fderiv ℝ f x) (x+(0:ℝ) • (y-x)) := by
      simpa using ((hf x hx).differentiableAt (by norm_num)).hasFDerivAt
    have h1 := hf0.comp_hasDerivAt 0 hL
    simpa [Function.comp_def, Pi.sub_def] using h1.sub (((hasDerivAt_id (0:ℝ)).pow 2).const_mul (κ/2*‖y-x‖^2))
  have h := hc.le_slope_of_hasDerivAt (x:=0) (y:=1) (by simp) (by simp) (by norm_num) hD
  simp only [slope_def_field, one_smul, zero_smul, add_zero, add_sub_cancel,
    one_pow, mul_one, zero_pow (by norm_num : 2≠0), mul_zero, sub_zero,
    div_one] at h
  linarith

/-- Strong monotonicity of the genuine derivative in the continuous dual. -/
theorem coercive_gradient_pairing (f : E → ℝ) {s : Set E} (hs : Convex ℝ s)
    (hf : ∀ z ∈ s, ContDiffAt ℝ ∞ f z) (κ : ℝ)
    (hH : ∀ z ∈ s, ∀ v : E,
      κ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) z v v)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    κ * ‖y-x‖^2 ≤ (fderiv ℝ f y - fderiv ℝ f x) (y-x) := by
  have hxy := coercive_taylor_lower f hs hf κ hH hx hy
  have hyx := coercive_taylor_lower f hs hf κ hH hy hx
  have he : x-y = -(y-x) := by abel
  rw [he, map_neg, norm_neg] at hyx
  simp only [ContinuousLinearMap.sub_apply]
  linarith

/-- A stationary point in a coercive convex region is unique. -/
theorem coercive_stationary_unique (f : E → ℝ) {s : Set E} (hs : Convex ℝ s)
    (hf : ∀ z ∈ s, ContDiffAt ℝ ∞ f z) {κ : ℝ} (hκ : 0<κ)
    (hH : ∀ z ∈ s, ∀ v : E,
      κ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) z v v)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s)
    (hgx : fderiv ℝ f x=0) (hgy : fderiv ℝ f y=0) : x=y := by
  have h := coercive_gradient_pairing f hs hf κ hH hx hy
  rw [hgx,hgy] at h
  simp only [sub_self,ContinuousLinearMap.zero_apply] at h
  have hn : ‖y-x‖=0 := by
    by_contra hn
    exact (not_lt_of_ge h) (mul_pos hκ (sq_pos_of_ne_zero hn))
  exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm

/-- Distance to a stationary point is controlled by the true dual gradient. -/
theorem coercive_stationary_displacement (f : E → ℝ) {s : Set E} (hs : Convex ℝ s)
    (hf : ∀ z ∈ s, ContDiffAt ℝ ∞ f z) {κ : ℝ} (hκ : 0<κ)
    (hH : ∀ z ∈ s, ∀ v : E,
      κ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) z v v)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) (hgy : fderiv ℝ f y=0) :
    ‖y-x‖ ≤ ‖fderiv ℝ f x‖/κ := by
  have h := coercive_gradient_pairing f hs hf κ hH hx hy
  rw [hgy] at h
  simp only [zero_sub,ContinuousLinearMap.neg_apply] at h
  have hb := (fderiv ℝ f x).le_opNorm (y-x)
  have hba : -(fderiv ℝ f x) (y-x) ≤ ‖fderiv ℝ f x‖*‖y-x‖ := by
    exact (neg_le_abs _).trans (by simpa only [Real.norm_eq_abs] using hb)
  apply (le_div_iff₀ hκ).mpr
  by_cases hn : ‖y-x‖=0
  · simp only [hn,zero_mul];exact norm_nonneg _
  · have hp : 0<‖y-x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    nlinarith

end GeneralDepthPaper
