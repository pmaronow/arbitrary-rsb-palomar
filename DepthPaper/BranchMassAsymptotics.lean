module

public import DepthPaper.LimitingPressureCalculus
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section


/-! Quantitative inversion of a genuinely C² decreasing branch at its
endpoint. This analytic foundation will be instantiated with the actual
stationary branch in Corollary 5.2; it is not itself that numbered result. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 1000000

theorem branch_derivative_increment_bound (ell : ℝ→ℝ) {a B : ℝ}
    (ha : a<1) (hB : 0≤B)
    (hreg : ∀x∈Icc a 1,ContDiffAt ℝ 2 ell x)
    (hcurv : ∀x∈Icc a 1,|deriv (deriv ell) x|≤B)
    {m x : ℝ} (hm : m∈Icc a 1) (hx : x∈Icc m 1) :
    |deriv ell x-deriv ell 1|≤B*(1-m) := by
  rcases hx.2.eq_or_lt with hxe|hx1
  · rw [hxe,sub_self,abs_zero]
    exact mul_nonneg hB (sub_nonneg.mpr hm.2)
  have hcont : ContinuousOn (deriv ell) (Icc x 1) := by
    intro y hy
    exact ((hreg y ⟨hm.1.trans (hx.1.trans hy.1),hy.2⟩).derivWithin (m:=1) (by norm_num)).continuousAt.continuousWithinAt
  have hd : ∀y∈Ioo x 1,HasDerivAt (deriv ell) (deriv (deriv ell) y) y := by
    intro y hy
    exact (((hreg y ⟨hm.1.trans (hx.1.trans hy.1.le),hy.2.le⟩).derivWithin (m:=1) (by norm_num)).differentiableAt
      (by norm_num)).hasDerivAt
  obtain ⟨y,hy,he⟩:=exists_hasDerivAt_eq_slope (deriv ell) (deriv (deriv ell)) hx1 hcont hd
  have he' : deriv ell 1-deriv ell x=deriv (deriv ell) y*(1-x) := by
    exact ((eq_div_iff (sub_pos.mpr hx1).ne').mp he).symm
  have hyB:=hcurv y ⟨hm.1.trans (hx.1.trans hy.1.le),hy.2.le⟩
  calc
    _=|deriv ell 1-deriv ell x|:=abs_sub_comm _ _
    _=|deriv (deriv ell) y| * (1-x):=by rw [he',abs_mul,abs_of_nonneg (sub_nonneg.mpr hx.2)]
    _≤B*(1-x):=mul_le_mul_of_nonneg_right hyB (sub_nonneg.mpr hx.2)
    _≤B*(1-m):=mul_le_mul_of_nonneg_left (by linarith [hx.1]) hB

theorem branch_endpoint_remainder_bound (ell : ℝ→ℝ) {a B : ℝ}
    (ha : a<1) (hB : 0≤B)
    (hreg : ∀x∈Icc a 1,ContDiffAt ℝ 2 ell x)
    (hcurv : ∀x∈Icc a 1,|deriv (deriv ell) x|≤B)
    {m : ℝ} (hm : m∈Icc a 1) :
    |ell m-ell 1+deriv ell 1*(1-m)|≤B*(1-m)^2 := by
  rcases hm.2.eq_or_lt with hme|hm1
  · rw [hme];simp
  let f : ℝ→ℝ:=fun x=>ell x-ell 1-deriv ell 1*(x-1)
  let df : ℝ→ℝ:=fun x=>deriv ell x-deriv ell 1
  have hd : ∀x∈Icc m 1,HasDerivAt f (df x) x := by
    intro x hx
    have hdx:=((hreg x ⟨hm.1.trans hx.1,hx.2⟩).differentiableAt (by norm_num)).hasDerivAt
    convert (hdx.sub_const (ell 1)).sub (((hasDerivAt_id x).sub_const 1).const_mul (deriv ell 1)) using 1
    · rfl
    · dsimp only [df];ring
  have hcont : ContinuousOn f (Icc m 1):=fun x hx=>(hd x hx).continuousAt.continuousWithinAt
  obtain ⟨x,hx,he⟩:=exists_hasDerivAt_eq_slope f df hm1 hcont (fun x hx=>hd x ⟨hx.1.le,hx.2.le⟩)
  have he' : f 1-f m=df x*(1-m) := ((eq_div_iff (sub_pos.mpr hm1).ne').mp he).symm
  have hb:=branch_derivative_increment_bound ell ha hB hreg hcurv hm ⟨hx.1.le,hx.2.le⟩
  have hf1 : f 1=0:=by dsimp only [f];ring
  have heq : |ell m-ell 1+deriv ell 1*(1-m)|=|f 1-f m| := by
    have heq0 : f 1-f m=-(ell m-ell 1+deriv ell 1*(1-m)) := by dsimp only [f];ring
    rw [heq0,abs_neg]
  rw [heq,he',abs_mul,abs_of_nonneg (sub_nonneg.mpr hm.2)]
  change |deriv ell x-deriv ell 1| * (1-m)≤B*(1-m)^2
  have hh:=mul_le_mul_of_nonneg_right hb (sub_nonneg.mpr hm.2)
  convert hh using 1 <;> ring

theorem branch_mass_le_parameter_increment (ell : ℝ→ℝ) {a c : ℝ}
    (ha : a<1) (hc : 0 < c)
    (hreg : ∀x∈Icc a 1,ContDiffAt ℝ 2 ell x)
    (hslope : ∀x∈Icc a 1,deriv ell x≤-c)
    {m : ℝ} (hm : m∈Icc a 1) :
    c*(1-m)≤ell m-ell 1 := by
  rcases hm.2.eq_or_lt with hme|hm1
  · rw [hme];simp
  have hcont : ContinuousOn ell (Icc m 1):=fun x hx=>
    (hreg x ⟨hm.1.trans hx.1,hx.2⟩).continuousAt.continuousWithinAt
  have hd : ∀x∈Ioo m 1,HasDerivAt ell (deriv ell x) x:=fun x hx=>
    ((hreg x ⟨hm.1.trans hx.1.le,hx.2.le⟩).differentiableAt (by norm_num)).hasDerivAt
  obtain ⟨x,hx,he⟩:=exists_hasDerivAt_eq_slope ell (deriv ell) hm1 hcont hd
  have he' : ell 1-ell m=deriv ell x*(1-m):=((eq_div_iff (sub_pos.mpr hm1).ne').mp he).symm
  have hh:=mul_le_mul_of_nonneg_right (hslope x ⟨hm.1.trans hx.1.le,hx.2.le⟩)
    (sub_nonneg.mpr hm.2)
  linarith

theorem branch_inverse_quadratic_mass_law (ell : ℝ→ℝ) {a c B : ℝ}
    (ha : a<1) (hc : 0 < c) (hB : 0≤B)
    (hreg : ∀x∈Icc a 1,ContDiffAt ℝ 2 ell x)
    (hslope : ∀x∈Icc a 1,deriv ell x≤-c)
    (hcurv : ∀x∈Icc a 1,|deriv (deriv ell) x|≤B)
    {m : ℝ} (hm : m∈Icc a 1) :
    0 < -(1/2:ℝ)*deriv ell 1 ∧
      |1-m-(ell m-ell 1)/(2*(-(1/2:ℝ)*deriv ell 1))|≤
        (B/c^3)*(ell m-ell 1)^2 := by
  let A:ℝ:=-deriv ell 1
  let d:ℝ:=ell m-ell 1
  let e:ℝ:=1-m
  have hAc : c≤A := by have hh:=hslope 1 ⟨ha.le,le_rfl⟩;dsimp only [A];linarith
  have hA : 0 < A := hc.trans_le hAc
  have he : 0≤e:=sub_nonneg.mpr hm.2
  have hde : c*e≤d:=branch_mass_le_parameter_increment ell ha hc hreg hslope hm
  have hd : 0≤d := (mul_nonneg hc.le he).trans hde
  have hrem : |d-A*e|≤B*e^2 := by
    simpa only [A,d,e,sub_eq_add_neg,neg_mul,neg_neg] using branch_endpoint_remainder_bound ell ha hB hreg hcurv hm
  have heD : e≤d/c := (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hde)
  have he2 : e^2≤(d/c)^2:=pow_le_pow_left₀ he heD 2
  have hrd : |e-d/A|=|d-A*e|/A := by
    have heq : e-d/A=-(d-A*e)/A := by field_simp;ring
    rw [heq,abs_div,abs_neg,abs_of_pos hA]
  have habs : 0≤|d-A*e|:=abs_nonneg _
  have h1:=div_le_div_of_nonneg_right hrem hA.le
  have h2:=div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he2 hB) hA.le
  have h3:=div_le_div_of_nonneg_left (mul_nonneg hB (sq_nonneg (d/c))) hc hAc
  have hfinal : |e-d/A|≤(B/c^3)*d^2 := by
    rw [hrd]
    apply (h1.trans h2).trans
    apply h3.trans_eq
    field_simp
    <;> ring
  constructor
  · dsimp only [A] at hA
    linarith
  · convert hfinal using 1 <;> dsimp only [A,d,e] <;> congr 1 <;> ring

end DepthPaper
