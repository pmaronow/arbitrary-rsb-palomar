module

public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.Linarith

@[expose] public section


/-! Integral Grönwall for a continuous nonnegative comparison function.
Only the primitive is differentiated; the underlying drift may be merely measurable. -/
noncomputable section
open Set MeasureTheory
namespace FourPapersCommon

theorem le_exp_of_integral_le (f : ℝ→ℝ) (hf : Continuous f) (T δ K : ℝ)
    (hδ : 0≤δ) (hK : 0≤K)
    (hf0 : ∀r∈Icc (0 : ℝ) T,0≤f r)
    (hineq : ∀r∈Icc (0 : ℝ) T,f r≤δ+K*(∫s in 0..r,f s)) :
    ∀r∈Icc (0 : ℝ) T,f r≤δ*Real.exp (K*r) := by
  let u:ℝ→ℝ:=fun r=>δ+K*(∫s in 0..r,f s)
  have hu0 : ∀r∈Icc (0 : ℝ) T,0≤u r := by
    intro r hr
    exact add_nonneg hδ (mul_nonneg hK (intervalIntegral.integral_nonneg hr.1
      (fun s hs=>hf0 s ⟨hs.1,hs.2.trans hr.2⟩)))
  have hdu : ∀r,HasDerivAt u (K*f r) r := by
    intro r
    convert!
      (hasDerivAt_const r δ).add ((intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 r)
        hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt).const_mul K) using 1 <;>
        simp only [zero_add]
  have hu : Continuous u := continuous_iff_continuousAt.mpr fun r=>(hdu r).continuousAt
  have hb:=norm_le_gronwallBound_of_norm_deriv_right_le (f := u)
    (f' := fun r=>K*f r) (a := (0 : ℝ)) (b := T) hu.continuousOn
    (fun r _=>(hdu r).hasDerivWithinAt) (δ := δ) (K := K) (ε := 0)
    (by simp [u,Real.norm_of_nonneg hδ])
    (by
      intro r hr
      rw [Real.norm_of_nonneg (mul_nonneg hK (hf0 r ⟨hr.1,hr.2.le⟩)),
        Real.norm_of_nonneg (hu0 r ⟨hr.1,hr.2.le⟩),add_zero]
      exact mul_le_mul_of_nonneg_left (hineq r ⟨hr.1,hr.2.le⟩) hK)
  intro r hr
  exact (hineq r hr).trans (by
    simpa only [Real.norm_of_nonneg (hu0 r hr),gronwallBound_ε0,sub_zero] using hb r hr)

end FourPapersCommon
