module

public import FRSB.ComparisonBounded

set_option backward.privateInPublic true

@[expose] public section


/-! A bounded comparison estimate for two genuine viscous Burgers solutions.
The scalar barrier uses the difference of their mass parameters and their
actual spatial gradients; no comparison or stability conclusion is assumed. -/
noncomputable section
open Set Filter
open scoped Topology
namespace FourPapersCommon
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

private theorem bounded_burgers_gap_upper
    (T : ℝ) (hT : 0 ≤ T) (m n : ℝ) (hm : m ∈ Icc (0 : ℝ) 1)
    (hn : n ∈ Icc (0 : ℝ) 1) (f g ft gt : ℝ × ℝ → ℝ)
    (hf : ContinuousOn f (Icc 0 T ×ˢ (univ : Set ℝ)))
    (hg : ContinuousOn g (Icc 0 T ×ˢ (univ : Set ℝ)))
    (hft : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x,
      HasDerivWithinAt (fun s => f (s,x)) (ft (t,x)) (Icc 0 T) t)
    (hgt : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x,
      HasDerivWithinAt (fun s => g (s,x)) (gt (t,x)) (Icc 0 T) t)
    (hfx : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x, DifferentiableAt ℝ (fun y => f (t,y)) x)
    (hgx : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x, DifferentiableAt ℝ (fun y => g (t,y)) x)
    (hfxx : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x,
      DifferentiableAt ℝ (deriv (fun y => f (t,y))) x)
    (hgxx : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x,
      DifferentiableAt ℝ (deriv (fun y => g (t,y))) x)
    (hPDEf : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x,
      ft (t,x) = (1/2 : ℝ) * deriv (deriv (fun y => f (t,y))) x +
        m * f (t,x) * deriv (fun y => f (t,y)) x)
    (hPDEg : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x,
      gt (t,x) = (1/2 : ℝ) * deriv (deriv (fun y => g (t,y))) x +
        n * g (t,x) * deriv (fun y => g (t,y)) x)
    (hfbound : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |f (t,x)| ≤ 1)
    (hgbound : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |g (t,x)| ≤ 1)
    (hggrad : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x,
      deriv (fun y => g (t,y)) x ∈ Icc (0 : ℝ) 1)
    (D : ℝ) (hD : 0 ≤ D) (hinitial : ∀ x, g (0,x) - f (0,x) ≤ D) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      g (t,x) - f (t,x) ≤ Real.exp t * (D + t * |m-n|) := by
  let δ : ℝ := |m-n|
  let B : ℝ → ℝ := fun t => Real.exp t * (D + t * δ)
  let Bt : ℝ → ℝ := fun t => B t + Real.exp t * δ
  let v : ℝ × ℝ → ℝ := fun z => B z.1 - (g z - f z)
  let vt : ℝ × ℝ → ℝ := fun z => Bt z.1 - (gt z - ft z)
  let b : ℝ × ℝ → ℝ := fun z => m * f z
  let κ : ℝ × ℝ → ℝ := fun z => n * deriv (fun y => g (z.1,y)) z.2
  have hδ : 0 ≤ δ := abs_nonneg _
  have hBnonneg t (ht : t ∈ Icc (0 : ℝ) T) : 0 ≤ B t := by
    exact mul_nonneg (Real.exp_pos _).le (add_nonneg hD (mul_nonneg ht.1 hδ))
  have hBle t (ht : t ∈ Icc (0 : ℝ) T) : B t ≤ B T := by
    exact mul_le_mul (Real.exp_le_exp.mpr ht.2)
      (by linarith [mul_le_mul_of_nonneg_right ht.2 hδ])
      (add_nonneg hD (mul_nonneg ht.1 hδ)) (Real.exp_pos _).le
  have hBder t : HasDerivAt B (Bt t) t := by
    have hi : HasDerivAt (fun s : ℝ => D + s * δ) δ t := by
      convert (hasDerivAt_const t D).add ((hasDerivAt_id t).mul_const δ) using 1
      · funext s
        rfl
      · ring
    exact (Real.hasDerivAt_exp t).mul hi
  have hvc : ContinuousOn v (Icc 0 T ×ˢ (univ : Set ℝ)) := by
    exact (by dsimp [B]; fun_prop : Continuous (fun z : ℝ × ℝ => B z.1)).continuousOn.sub
      (hg.sub hf)
  have hvtime : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x,
      HasDerivWithinAt (fun s => v (s,x)) (vt (t,x)) (Icc 0 T) t := by
    intro t ht x
    exact (hBder t).hasDerivWithinAt.sub ((hgt t ht x).sub (hft t ht x))
  have hvspace t (ht : t ∈ Ioc (0 : ℝ) T) x :
      HasDerivAt (fun y => v (t,y))
        (deriv (fun y => f (t,y)) x - deriv (fun y => g (t,y)) x) x := by
    convert (hasDerivAt_const x (B t)).sub
      ((hgx t ht x).hasDerivAt.sub (hfx t ht x).hasDerivAt) using 1 <;>
      ring
  have hvderiv t (ht : t ∈ Ioc (0 : ℝ) T) :
      deriv (fun y => v (t,y)) =
        fun y => deriv (fun q => f (t,q)) y - deriv (fun q => g (t,q)) y := by
    funext x
    exact (hvspace t ht x).deriv
  have hvsecond t (ht : t ∈ Ioc (0 : ℝ) T) x :
      deriv (deriv (fun y => v (t,y))) x =
        deriv (deriv (fun y => f (t,y))) x - deriv (deriv (fun y => g (t,y))) x := by
    rw [hvderiv t ht]
    exact ((hfxx t ht x).hasDerivAt.sub (hgxx t ht x).hasDerivAt).deriv
  have hvxx t (ht : t ∈ Ioc (0 : ℝ) T) x :
      DifferentiableAt ℝ (deriv (fun y => v (t,y))) x := by
    rw [hvderiv t ht]
    exact (hfxx t ht x).sub (hgxx t ht x)
  have hvbound : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |v (t,x)| ≤ B T + 2 := by
    intro t ht x
    have hgap : |g (t,x) - f (t,x)| ≤ 2 := by
      have ha : |g (t,x) - f (t,x)| ≤ |g (t,x)| + |f (t,x)| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le (g (t,x)) (f (t,x))
      exact ha.trans (by linarith [hgbound t ht x,hfbound t ht x])
    calc
      |v (t,x)| ≤ |B t| + |g (t,x) - f (t,x)| := by
        simpa only [v,Real.norm_eq_abs] using norm_sub_le (B t) (g (t,x) - f (t,x))
      _ = B t + |g (t,x) - f (t,x)| := by rw [abs_of_nonneg (hBnonneg t ht)]
      _ ≤ B T + 2 := add_le_add (hBle t ht) hgap
  have hbquad : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x,
      2 * b (t,x) * x ≤ (1 : ℝ) * (1 + x^2) := by
    intro t ht x
    have hbabs : |b (t,x)| ≤ 1 := by
      dsimp [b]
      rw [abs_mul,abs_of_nonneg hm.1]
      exact (mul_le_mul_of_nonneg_left (hfbound t ⟨ht.1.le,ht.2⟩ x) hm.1).trans
        (by simpa using hm.2)
    have hbsq := mul_nonneg (sub_nonneg.mpr hbabs)
      (add_nonneg (show (0 : ℝ) ≤ 1 by norm_num) (abs_nonneg (b (t,x))))
    nlinarith [sq_abs (b (t,x)),sq_nonneg (x - b (t,x))]
  have hκbound t (ht : t ∈ Ioc (0 : ℝ) T) x : κ (t,x) ≤ 1 := by
    exact (mul_le_mul hn.2 (hggrad t ht x).2 (hggrad t ht x).1 zero_le_one).trans
      (by norm_num)
  have hsource t (ht : t ∈ Ioc (0 : ℝ) T) x :
      (n-m) * f (t,x) * deriv (fun y => g (t,y)) x ≤ δ := by
    have ha : |(n-m) * f (t,x) * deriv (fun y => g (t,y)) x| ≤ |n-m| := by
      rw [abs_mul,abs_mul,abs_of_nonneg (hggrad t ht x).1]
      calc
        |n-m| * |f (t,x)| * deriv (fun y => g (t,y)) x ≤ |n-m| * 1 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hfbound t ⟨ht.1.le,ht.2⟩ x) (abs_nonneg _))
            (hggrad t ht x).2 (hggrad t ht x).1 (by positivity)
        _ = |n-m| := by ring
    exact (le_abs_self _).trans (by simpa [δ,abs_sub_comm] using ha)
  have hbar t (ht : t ∈ Ioc (0 : ℝ) T) x : δ ≤ Bt t - κ (t,x) * B t := by
    have hreact := mul_le_mul_of_nonneg_right (hκbound t ht x)
      (hBnonneg t ⟨ht.1.le,ht.2⟩)
    have hexp := mul_le_mul_of_nonneg_right
      (Real.one_le_exp_iff.mpr ht.1.le) hδ
    dsimp [Bt]
    linarith
  have hvPDE : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x,
      0 ≤ vt (t,x) - (1/2 : ℝ) * deriv (deriv (fun y => v (t,y))) x -
        b (t,x) * deriv (fun y => v (t,y)) x - κ (t,x) * v (t,x) := by
    intro t ht x
    rw [hvsecond t ht x,(hvspace t ht x).deriv]
    have heq : vt (t,x) - (1/2 : ℝ) *
        (deriv (deriv (fun y => f (t,y))) x - deriv (deriv (fun y => g (t,y))) x) -
        b (t,x) * (deriv (fun y => f (t,y)) x - deriv (fun y => g (t,y)) x) -
        κ (t,x) * v (t,x) =
        (Bt t - κ (t,x) * B t) - (n-m) * f (t,x) * deriv (fun y => g (t,y)) x := by
      dsimp [vt,b,v,κ]
      rw [hPDEg t ht x,hPDEf t ht x]
      ring
    rw [heq]
    linarith [hbar t ht x,hsource t ht x]
  have hv0 : ∀ x, 0 ≤ v (0,x) := by
    intro x
    have hi := hinitial x
    simpa [v,B] using sub_nonneg.mpr hi
  have hvnonneg := FRSB.bounded_supersolution_nonneg_quadratic false T 1 (B T + 2)
    hT (by norm_num) (by linarith [hBnonneg T ⟨hT,le_rfl⟩]) v vt b κ
    (by simpa [FRSB.comparisonSpace] using hvc)
    (fun t ht x _ => hvtime t ht x)
    (fun t ht x _ => (hvspace t ht x).differentiableAt)
    (fun t ht x _ => hvxx t ht x)
    (fun t ht x _ => hvbound t ht x)
    (fun t ht x _ => hbquad t ht x)
    (fun t ht x _ => hκbound t ht x)
    (fun t ht x _ => hvPDE t ht x)
    (fun x _ => hv0 x) (by intro h; cases h)
  intro t ht x
  have hvpos := hvnonneg (t,x) ⟨ht,by simp [FRSB.comparisonSpace]⟩
  change 0 ≤ B t - (g (t,x) - f (t,x)) at hvpos
  exact sub_nonneg.mp hvpos

/-- A bounded pair of actual Burgers solutions has a sharp one-cell mass
comparison bound. Initial gaps and all spatial fields are unrestricted. -/
theorem bounded_burgers_comparison
    (T : ℝ) (hT : 0 ≤ T) (m n : ℝ) (hm : m ∈ Icc (0 : ℝ) 1)
    (hn : n ∈ Icc (0 : ℝ) 1) (f g ft gt : ℝ × ℝ → ℝ)
    (hf : ContinuousOn f (Icc 0 T ×ˢ (univ : Set ℝ)))
    (hg : ContinuousOn g (Icc 0 T ×ˢ (univ : Set ℝ)))
    (hft : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x,
      HasDerivWithinAt (fun s => f (s,x)) (ft (t,x)) (Icc 0 T) t)
    (hgt : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x,
      HasDerivWithinAt (fun s => g (s,x)) (gt (t,x)) (Icc 0 T) t)
    (hfx : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x, DifferentiableAt ℝ (fun y => f (t,y)) x)
    (hgx : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x, DifferentiableAt ℝ (fun y => g (t,y)) x)
    (hfxx : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x,
      DifferentiableAt ℝ (deriv (fun y => f (t,y))) x)
    (hgxx : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x,
      DifferentiableAt ℝ (deriv (fun y => g (t,y))) x)
    (hPDEf : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x,
      ft (t,x) = (1/2 : ℝ) * deriv (deriv (fun y => f (t,y))) x +
        m * f (t,x) * deriv (fun y => f (t,y)) x)
    (hPDEg : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x,
      gt (t,x) = (1/2 : ℝ) * deriv (deriv (fun y => g (t,y))) x +
        n * g (t,x) * deriv (fun y => g (t,y)) x)
    (hfbound : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |f (t,x)| ≤ 1)
    (hgbound : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |g (t,x)| ≤ 1)
    (hfgrad : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x,
      deriv (fun y => f (t,y)) x ∈ Icc (0 : ℝ) 1)
    (hggrad : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x,
      deriv (fun y => g (t,y)) x ∈ Icc (0 : ℝ) 1)
    (D : ℝ) (hD : 0 ≤ D) (hinitial : ∀ x, |g (0,x) - f (0,x)| ≤ D) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      |g (t,x) - f (t,x)| ≤ Real.exp t * (D + t * |m-n|) := by
  have hu := bounded_burgers_gap_upper T hT m n hm hn f g ft gt hf hg hft hgt hfx hgx
    hfxx hgxx hPDEf hPDEg hfbound hgbound hggrad D hD
    (fun x => (le_abs_self _).trans (hinitial x))
  have hl := bounded_burgers_gap_upper T hT n m hn hm g f gt ft hg hf hgt hft hgx hfx
    hgxx hfxx hPDEg hPDEf hgbound hfbound hfgrad D hD (fun x => by
      have hi := (abs_le.mp (hinitial x)).1
      linarith)
  intro t ht x
  apply abs_le.mpr
  refine ⟨?_,hu t ht x⟩
  have hh := hl t ht x
  rw [abs_sub_comm n m] at hh
  linarith

end FourPapersCommon
