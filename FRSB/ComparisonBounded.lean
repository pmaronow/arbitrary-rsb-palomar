module

public import FRSB.Comparison
public import Mathlib.Basic.Sign.Basic

@[expose] public section


noncomputable section
open Set Filter SignType
open scoped Topology
namespace FRSB

def comparisonSpace (halfLine : Bool) : Set ℝ := if halfLine then Ici 0 else univ
def comparisonSpaceInterior (halfLine : Bool) : Set ℝ := if halfLine then Ioi 0 else univ

lemma outward_drift_quadratic {b K x : ℝ} (hK : 0 ≤ K)
    (hb : b * sign x ≤ K) : 2 * b * x ≤ K * (1 + x ^ 2) := by
  have hh := mul_le_mul_of_nonneg_right hb (abs_nonneg x)
  simp only [mul_assoc, sign_mul_abs] at hh
  have hs : 0 ≤ (|x| - 1) ^ 2 := sq_nonneg _
  have hk := mul_nonneg hK hs
  nlinarith [sq_abs x]

/-- Bounded comparison on the full line or nonnegative half-line. The drift
may be unbounded in the inward direction: only its quadratic outward action
is bounded. -/
theorem bounded_supersolution_nonneg_quadratic (halfLine : Bool)
    (T K M : ℝ) (hT : 0 ≤ T) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (v vt b κ : ℝ × ℝ → ℝ)
    (hv : ContinuousOn v (Icc 0 T ×ˢ comparisonSpace halfLine))
    (ht : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ comparisonSpaceInterior halfLine,
      HasDerivWithinAt (fun s => v (s, x)) (vt (t, x)) (Icc 0 T) t)
    (hx : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ comparisonSpaceInterior halfLine,
      DifferentiableAt ℝ (fun y => v (t, y)) x)
    (hxx : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ comparisonSpaceInterior halfLine,
      DifferentiableAt ℝ (deriv (fun y => v (t, y))) x)
    (hbound : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ comparisonSpace halfLine, |v (t, x)| ≤ M)
    (hb : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ comparisonSpaceInterior halfLine,
      2 * b (t, x) * x ≤ K * (1 + x ^ 2))
    (hκ : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ comparisonSpaceInterior halfLine, κ (t, x) ≤ K)
    (hPDE : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ comparisonSpaceInterior halfLine,
      0 ≤ vt (t, x) - (1 / 2 : ℝ) * deriv (deriv (fun y => v (t, y))) x -
        b (t, x) * deriv (fun y => v (t, y)) x - κ (t, x) * v (t, x))
    (hinitial : ∀ x ∈ comparisonSpace halfLine, 0 ≤ v (0, x))
    (hboundary : halfLine = true → ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ v (t, 0)) :
    ∀ p ∈ Icc 0 T ×ˢ comparisonSpace halfLine, 0 ≤ v p := by
  intro p hp
  by_contra hn
  have hpneg : v p < 0 := lt_of_not_ge hn
  let e : ℝ → ℝ := fun t => Real.exp (-(K + 1) * t)
  let d : ℝ → ℝ := fun t => Real.exp ((K + 2) * t)
  let F : ℝ := e p.1 * v p
  let A : ℝ := d p.1 * (1 + p.2 ^ 2)
  have hF : F < 0 := mul_neg_of_pos_of_neg (Real.exp_pos _) hpneg
  have hA : 0 < A := mul_pos (Real.exp_pos _) (by nlinarith [sq_nonneg p.2])
  let ε : ℝ := -F / (2 * A)
  have hε : 0 < ε := div_pos (neg_pos.mpr hF) (by positivity)
  have hεA : ε * A = -F / 2 := by dsimp [ε]; field_simp
  let R : ℝ := max |p.2| 1 + (M + 1) / ε + 1
  have hdiv : 0 < (M + 1) / ε := div_pos (by linarith) hε
  have hR1 : 1 ≤ R := by dsimp [R]; linarith [le_max_right |p.2| 1]
  have hpR : |p.2| < R := by dsimp [R]; linarith [le_max_left |p.2| 1]
  have hR : 0 < R := by linarith
  have hεR : M + 1 < ε * R := by
    have heq : ε * ((M + 1) / ε) = M + 1 := by field_simp
    dsimp [R]
    rw [mul_add, mul_add, heq, mul_one]
    have hm := mul_nonneg hε.le (le_max_right |p.2| 1 |>.trans' (by norm_num))
    linarith
  have hfar : M < ε * (1 + R ^ 2) := by
    have hh := mul_lt_mul_of_pos_right hεR hR
    have hm := mul_le_mul_of_nonneg_left hR1 hM
    nlinarith [hε, hh, hm]
  let l : ℝ := if halfLine then 0 else -R
  have hlr : l < R := by cases halfLine <;> simp [l] <;> linarith
  have hbox : Icc l R ⊆ comparisonSpace halfLine := by
    cases halfLine
    · simp [l, comparisonSpace]
    · intro x hx0
      exact hx0.1
  have hinterior : Ioo l R ⊆ comparisonSpaceInterior halfLine := by
    cases halfLine
    · simp [l, comparisonSpaceInterior]
    · intro x hx0
      exact hx0.1
  have hopen : IsOpen (comparisonSpaceInterior halfLine) := by
    cases halfLine
    · exact isOpen_univ
    · exact isOpen_Ioi
  let w : ℝ × ℝ → ℝ := fun z => e z.1 * v z + ε * d z.1 * (1 + z.2 ^ 2)
  let wt : ℝ × ℝ → ℝ := fun z =>
    -(K + 1) * e z.1 * v z + e z.1 * vt z + ε * ((K + 2) * d z.1) * (1 + z.2 ^ 2)
  let κ' : ℝ × ℝ → ℝ := fun z => κ z - (K + 1)
  have heder (t : ℝ) : HasDerivAt e (-(K + 1) * e t) t := by
    convert ((hasDerivAt_id t).const_mul (-(K + 1))).exp using 1 <;> dsimp [e] <;> ring
  have hdder (t : ℝ) : HasDerivAt d ((K + 2) * d t) t := by
    convert ((hasDerivAt_id t).const_mul (K + 2)).exp using 1 <;> dsimp [d] <;> ring
  have hwc : ContinuousOn w (Icc 0 T ×ˢ Icc l R) := by
    have hh := hv.mono (prod_mono Subset.rfl hbox)
    exact ((by fun_prop : Continuous (fun z : ℝ × ℝ => e z.1)).continuousOn.mul hh).add
      (by dsimp [d]; fun_prop)
  have hwtime : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ Ioo l R,
      HasDerivWithinAt (fun s => w (s, x)) (wt (t, x)) (Icc 0 T) t := by
    intro t ht0 x hx0
    convert ((heder t).hasDerivWithinAt.mul (ht t ht0 x (hinterior hx0))).add
      (((hdder t).hasDerivWithinAt.const_mul ε).mul_const (1 + x ^ 2)) using 1 <;>
      dsimp [w, wt] <;> ring
  have hwspace (t : ℝ) (ht0 : t ∈ Ioc (0 : ℝ) T) (x : ℝ)
      (hx0 : x ∈ comparisonSpaceInterior halfLine) :
      HasDerivAt (fun y => w (t, y))
        (e t * deriv (fun y => v (t, y)) x + 2 * ε * d t * x) x := by
    have hh := ((hx t ht0 x hx0).hasDerivAt.const_mul (e t)).add
      (((hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_id x).pow 2)).const_mul (ε * d t))
    convert hh using 1
    · funext y
      dsimp [w]
    · simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, zero_add, mul_one]
      ring
  have hwsecond (t : ℝ) (ht0 : t ∈ Ioc (0 : ℝ) T) (x : ℝ)
      (hx0 : x ∈ comparisonSpaceInterior halfLine) :
      deriv (deriv (fun y => w (t, y))) x =
        e t * deriv (deriv (fun y => v (t, y))) x + 2 * ε * d t := by
    have heq : deriv (fun y => w (t, y)) =ᶠ[𝓝 x]
        (fun y => e t * deriv (fun q => v (t, q)) y + 2 * ε * d t * y) := by
      filter_upwards [hopen.mem_nhds hx0] with y hy
      exact (hwspace t ht0 y hy).deriv
    rw [heq.deriv_eq]
    have hh := (((hxx t ht0 x hx0).hasDerivAt.const_mul (e t)).add
      ((hasDerivAt_id x).const_mul (2 * ε * d t))).deriv
    convert hh using 1
    · congr 1
    · simp only [id_eq, mul_one]
  have hwκ : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ Ioo l R, κ' (t, x) < 0 := by
    intro t ht0 x hx0
    dsimp [κ']
    linarith [hκ t ht0 x (hinterior hx0)]
  have hwPDE : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ Ioo l R,
      0 ≤ wt (t, x) - (1 / 2 : ℝ) * deriv (deriv (fun y => w (t, y))) x -
        b (t, x) * deriv (fun y => w (t, y)) x - κ' (t, x) * w (t, x) := by
    intro t ht0 x hx0
    have hxi := hinterior hx0
    rw [hwsecond t ht0 x hxi, (hwspace t ht0 x hxi).deriv]
    have hreact : κ' (t, x) ≤ -1 := by dsimp [κ']; linarith [hκ t ht0 x hxi]
    have hmul := mul_le_mul_of_nonneg_right hreact (by positivity : 0 ≤ 1 + x ^ 2)
    have hbar : 0 ≤ (K + 2) * (1 + x ^ 2) - 1 - 2 * b (t, x) * x - κ' (t, x) * (1 + x ^ 2) := by
      nlinarith [hb t ht0 x hxi, sq_nonneg x]
    have hvnonneg := mul_nonneg (Real.exp_pos (-(K + 1) * t)).le (hPDE t ht0 x hxi)
    have hbnonneg := mul_nonneg (mul_nonneg hε.le (Real.exp_pos ((K + 2) * t)).le) hbar
    have heq : wt (t, x) - (1 / 2 : ℝ) * (e t * deriv (deriv (fun y => v (t, y))) x + 2 * ε * d t) -
        b (t, x) * (e t * deriv (fun y => v (t, y)) x + 2 * ε * d t * x) - κ' (t, x) * w (t, x) =
      e t * (vt (t, x) - (1 / 2 : ℝ) * deriv (deriv (fun y => v (t, y))) x -
        b (t, x) * deriv (fun y => v (t, y)) x - κ (t, x) * v (t, x)) +
      ε * d t * ((K + 2) * (1 + x ^ 2) - 1 - 2 * b (t, x) * x - κ' (t, x) * (1 + x ^ 2)) := by
      dsimp [wt, w, κ']; ring
    rw [heq]
    exact add_nonneg hvnonneg hbnonneg
  have hinitialW : ∀ x ∈ Icc l R, 0 ≤ w (0, x) := by
    intro x hx0
    dsimp [w, e, d]
    simp only [mul_zero, Real.exp_zero, one_mul, mul_one]
    exact add_nonneg (hinitial x (hbox hx0)) (mul_nonneg hε.le (by positivity))
  have hside : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ comparisonSpace halfLine,
      |x| = R → 0 ≤ w (t, x) := by
    intro t ht0 x hx0 hxR
    have hepos : 0 < e t := Real.exp_pos _
    have hele : e t ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [ht0.1])
    have hdge : 1 ≤ d t := Real.one_le_exp_iff.mpr (by nlinarith [ht0.1])
    have hvlow := (abs_le.mp (hbound t ht0 x hx0)).1
    have hlow : -M ≤ e t * v (t, x) := by
      have hm := mul_le_mul_of_nonneg_left hvlow hepos.le
      nlinarith
    have hx2 : x ^ 2 = R ^ 2 := by nlinarith [sq_abs x]
    have hbar : ε * (1 + R ^ 2) ≤ ε * d t * (1 + x ^ 2) := by
      rw [hx2]
      exact mul_le_mul_of_nonneg_right (by nlinarith : ε ≤ ε * d t) (by positivity)
    dsimp [w]
    linarith
  have hleftW : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ w (t, l) := by
    intro t ht0
    cases hhalf : halfLine
    · have hl : l = -R := by simp [l, hhalf]
      rw [hl]
      exact hside t ht0 (-R) (by simp [comparisonSpace, hhalf]) (by simp [abs_of_pos hR])
    · have hl : l = 0 := by simp [l, hhalf]
      rw [hl]
      dsimp [w]
      exact add_nonneg (mul_nonneg (Real.exp_pos _).le (hboundary hhalf t ht0)) (by positivity)
  have hrightW : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ w (t, R) := by
    intro t ht0
    exact hside t ht0 R (by cases halfLine <;> simp [comparisonSpace, hR.le]) (abs_of_pos hR)
  have hpbox : p ∈ Icc 0 T ×ˢ Icc l R := by
    refine ⟨hp.1, ?_⟩
    have hh := abs_lt.mp hpR
    cases hhalf : halfLine
    · simpa [l, hhalf] using And.intro hh.1.le hh.2.le
    · have hp0 : 0 ≤ p.2 := by simpa [comparisonSpace, hhalf] using hp.2
      simpa [l, hhalf] using And.intro hp0 hh.2.le
  have hwpos := compact_supersolution_nonneg T l R hT hlr w wt b κ' hwc hwtime
    (fun t ht0 x hx0 => (hwspace t ht0 x (hinterior hx0)).differentiableAt)
    hwκ hwPDE hinitialW hleftW hrightW p hpbox
  have heq : w p = F + ε * A := by dsimp [w, F, A]; ring
  rw [heq, hεA] at hwpos
  linarith

/-- The paper's full-line/half-line comparison principle with exactly the
one-sided outward drift bound. -/
theorem bounded_supersolution_nonneg (halfLine : Bool)
    (T K M : ℝ) (hT : 0 ≤ T) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (v vt b κ : ℝ × ℝ → ℝ)
    (hv : ContinuousOn v (Icc 0 T ×ˢ comparisonSpace halfLine))
    (ht : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ comparisonSpaceInterior halfLine,
      HasDerivWithinAt (fun s => v (s, x)) (vt (t, x)) (Icc 0 T) t)
    (hx : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ comparisonSpaceInterior halfLine,
      DifferentiableAt ℝ (fun y => v (t, y)) x)
    (hxx : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ comparisonSpaceInterior halfLine,
      DifferentiableAt ℝ (deriv (fun y => v (t, y))) x)
    (hbound : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ comparisonSpace halfLine, |v (t, x)| ≤ M)
    (hb : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ comparisonSpaceInterior halfLine,
      b (t, x) * sign x ≤ K)
    (hκ : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ comparisonSpaceInterior halfLine, κ (t, x) ≤ K)
    (hPDE : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ comparisonSpaceInterior halfLine,
      0 ≤ vt (t, x) - (1 / 2 : ℝ) * deriv (deriv (fun y => v (t, y))) x -
        b (t, x) * deriv (fun y => v (t, y)) x - κ (t, x) * v (t, x))
    (hinitial : ∀ x ∈ comparisonSpace halfLine, 0 ≤ v (0, x))
    (hboundary : halfLine = true → ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ v (t, 0)) :
    ∀ p ∈ Icc 0 T ×ˢ comparisonSpace halfLine, 0 ≤ v p :=
  bounded_supersolution_nonneg_quadratic halfLine T K M hT hK hM v vt b κ hv ht hx hxx
    hbound (fun t ht0 x hx0 => outward_drift_quadratic hK (hb t ht0 x hx0)) hκ hPDE hinitial hboundary

end FRSB
