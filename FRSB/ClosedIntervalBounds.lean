module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section


/-! Closing a cropped interval increment estimate requires only continuous
endpoint observables and locally integrable source and error functions. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace FRSB

theorem closed_interval_increment_bound (F S E : ℝ → ℝ) (hF : Continuous F)
    (hS : ∀ a b, IntervalIntegrable S volume a b)
    (hE : ∀ a b, IntervalIntegrable E volume a b) {a b : ℝ} (hab : a < b)
    (hcrop : ∀ l r, a < l → l ≤ r → r < b →
      ‖F r-F l-∫s in l..r,S s‖ ≤ ∫s in l..r,E s)
    {l r : ℝ} (hl : a ≤ l) (hlr : l ≤ r) (hr : r ≤ b) :
    ‖F r-F l-∫s in l..r,S s‖ ≤ ∫s in l..r,E s := by
  let P : ℝ → ℝ := fun t => ∫ s in 0..t,S s
  let Q : ℝ → ℝ := fun t => ∫ s in 0..t,E s
  have hP : Continuous P := intervalIntegral.continuous_primitive hS 0
  have hQ : Continuous Q := intervalIntegral.continuous_primitive hE 0
  have hSint (x y : ℝ) : (∫s in x..y,S s) = P y-P x :=
    (intervalIntegral.integral_interval_sub_left (hS 0 y) (hS 0 x)).symm
  have hEint (x y : ℝ) : (∫s in x..y,E s) = Q y-Q x :=
    (intervalIntegral.integral_interval_sub_left (hE 0 y) (hE 0 x)).symm
  let c : ℝ := (a+b)/2
  let L : ℝ → ℝ := fun δ => (1-δ)*l+δ*c
  let R : ℝ → ℝ := fun δ => (1-δ)*r+δ*c
  have hc : a < c ∧ c < b := by dsimp [c]; constructor <;> linarith
  have hL : Tendsto L (𝓝[>] (0 : ℝ)) (𝓝 l) := by
    have hd : Tendsto (fun δ : ℝ => δ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa [L] using (((tendsto_const_nhds (x := (1 : ℝ))).sub hd).mul_const l).add (hd.mul_const c)
  have hR : Tendsto R (𝓝[>] (0 : ℝ)) (𝓝 r) := by
    have hd : Tendsto (fun δ : ℝ => δ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa [R] using (((tendsto_const_nhds (x := (1 : ℝ))).sub hd).mul_const r).add (hd.mul_const c)
  have hleft := (((hF.tendsto r).comp hR).sub ((hF.tendsto l).comp hL)).sub
    (((hP.tendsto r).comp hR).sub ((hP.tendsto l).comp hL)) |>.norm
  have hright := ((hQ.tendsto r).comp hR).sub ((hQ.tendsto l).comp hL)
  have hbnd : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ‖F (R δ)-F (L δ)-(P (R δ)-P (L δ))‖ ≤ Q (R δ)-Q (L δ) := by
    filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0),
      (show ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < 1 from
        (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds)] with δ hδ hδ1
    have hδ0 : 0 < δ := hδ
    have hLa : a < L δ := by
      dsimp [L]
      nlinarith [mul_nonneg (sub_nonneg.mpr hδ1.le) (sub_nonneg.mpr hl),
        mul_pos hδ0 (sub_pos.mpr hc.1)]
    have hRb : R δ < b := by
      dsimp [R]
      nlinarith [mul_nonneg (sub_nonneg.mpr hδ1.le) (sub_nonneg.mpr hr),
        mul_pos hδ0 (sub_pos.mpr hc.2)]
    have hLR : L δ ≤ R δ := by
      dsimp [L,R]
      nlinarith [mul_nonneg (sub_nonneg.mpr hδ1.le) (sub_nonneg.mpr hlr)]
    simpa only [hSint,hEint] using hcrop (L δ) (R δ) hLa hLR hRb
  simpa only [hSint,hEint] using le_of_tendsto_of_tendsto hleft hright hbnd

end FRSB
