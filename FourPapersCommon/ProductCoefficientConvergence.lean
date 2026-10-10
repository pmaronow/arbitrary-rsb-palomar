module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Algebra.Order.Field

@[expose] public section


/-! Multiplying moving step coefficients by uniformly converging bounded
rates preserves actual integrated squared convergence. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace FourPapersCommon

theorem productCoefficient_square_integral_le (a b c v : ℝ → ℝ) {T C δ : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hi : IntervalIntegrable (fun s => (c s*a s-v s*b s)^2) volume 0 T)
    (hj : IntervalIntegrable (fun s => (a s-b s)^2) volume 0 T)
    (ha : ∀ s ∈ Icc (0 : ℝ) T,|a s| ≤ 1)
    (hv : ∀ s ∈ Icc (0 : ℝ) T,|v s| ≤ C)
    (hd : ∀ s ∈ Icc (0 : ℝ) T,|c s-v s| ≤ δ) :
    (∫ s in 0..T,(c s*a s-v s*b s)^2) ≤
      2*δ^2*T+2*C^2*(∫ s in 0..T,(a s-b s)^2) := by
  have hp (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      (c s*a s-v s*b s)^2 ≤ 2*δ^2+2*C^2*(a s-b s)^2 := by
    have he : c s*a s-v s*b s = (c s-v s)*a s+v s*(a s-b s) := by ring
    have h1 : |(c s-v s)*a s| ≤ δ := by
      rw [abs_mul]
      simpa only [mul_one] using mul_le_mul (hd s hs) (ha s hs) (abs_nonneg _) hδ
    have h2 : |v s*(a s-b s)| ≤ C*|a s-b s| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hv s hs) (abs_nonneg _)
    have h1sq := (sq_le_sq₀ (abs_nonneg _) hδ).mpr h1
    have h2sq := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hC (abs_nonneg _))).mpr h2
    rw [sq_abs] at h1sq h2sq
    simp only [mul_pow,sq_abs] at h2sq
    rw [he]
    nlinarith only [h1sq,h2sq,sq_nonneg ((c s-v s)*a s-v s*(a s-b s))]
  have hh := intervalIntegral.integral_mono_on hT hi
    ((intervalIntegrable_const (c := 2*δ^2)).add (hj.const_mul (2*C^2))) hp
  rw [intervalIntegral.integral_add (intervalIntegrable_const (c := 2*δ^2))
    (hj.const_mul (2*C^2)),intervalIntegral.integral_const,intervalIntegral.integral_const_mul] at hh
  simpa only [sub_zero,smul_eq_mul,mul_comm,mul_left_comm,mul_assoc] using hh

theorem tendsto_productCoefficient_square_integral {ι : Type*} {F : Filter ι}
    (a c : ι → ℝ → ℝ) (b v : ℝ → ℝ) {T C : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hi : ∀ n,IntervalIntegrable (fun s => (c n s*a n s-v s*b s)^2) volume 0 T)
    (hj : ∀ n,IntervalIntegrable (fun s => (a n s-b s)^2) volume 0 T)
    (ha : ∀ n,∀ s ∈ Icc (0 : ℝ) T,|a n s| ≤ 1)
    (hv : ∀ s ∈ Icc (0 : ℝ) T,|v s| ≤ C)
    (δ : ι → ℝ) (hδ : ∀ n,0 ≤ δ n)
    (hd : ∀ n,∀ s ∈ Icc (0 : ℝ) T,|c n s-v s| ≤ δ n)
    (hδlim : Tendsto δ F (𝓝 0))
    (halim : Tendsto (fun n => ∫ s in 0..T,(a n s-b s)^2) F (𝓝 0)) :
    Tendsto (fun n => ∫ s in 0..T,(c n s*a n s-v s*b s)^2) F (𝓝 0) := by
  apply squeeze_zero (fun n => intervalIntegral.integral_nonneg_of_forall hT (fun s => sq_nonneg _))
    (fun n => productCoefficient_square_integral_le (a n) b (c n) v hT hC (hδ n)
      (hi n) (hj n) (ha n) hv (hd n))
  have h1 : Tendsto (fun n => 2*(δ n)^2*T) F (𝓝 0) := by
    simpa only [zero_pow (by norm_num : 2 ≠ 0),mul_zero,zero_mul] using
      ((hδlim.pow 2).const_mul 2).mul_const T
  have h2 : Tendsto (fun n => 2*C^2*(∫ s in 0..T,(a n s-b s)^2)) F (𝓝 0) := by
    simpa only [mul_zero] using halim.const_mul (2*C^2)
  simpa only [add_zero] using h1.add h2

end FourPapersCommon
