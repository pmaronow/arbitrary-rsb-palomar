module

public import GeneralDepthPaper.HighOverlapIntermediate

@[expose] public section


/-! Literal polynomial primitive and logarithmic-squared bound in the
intermediate-region proof. The cutoff ordering is the genuine threshold
geometry, not a substitute probabilistic or PDE hypothesis. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace GeneralDepthPaper
set_option maxHeartbeats 800000

theorem logarithmicTailBudget_log_sq_bound {p : ℕ} (hp : 0 < p)
    (lamhi : ℝ) {L : ℝ} (hL : 0 ≤ L) (hlog : 1 ≤ Real.log (p : ℝ)) :
    logarithmicTailBudget lamhi L p ≤
      (L * (2 * |Real.log lamhi| + 3)) * (Real.log (p : ℝ)) ^ 2 / (p : ℝ) := by
  have hpn : 0 < (p : ℝ) := by exact_mod_cast hp
  have hlog0 : 0 ≤ Real.log (p : ℝ) := by linarith
  have hsq : Real.log (p : ℝ) ≤ (Real.log (p : ℝ)) ^ 2 := by nlinarith
  unfold logarithmicTailBudget
  apply (le_div_iff₀ hpn).mpr
  field_simp
  nlinarith [abs_nonneg (Real.log lamhi),
    mul_nonneg (abs_nonneg (Real.log lamhi)) (sub_nonneg.mpr hsq)]

theorem logarithmic_high_degree_integral_cost_bound {p : ℕ} (hp : 2 ≤ p)
    {qc lam lamhi L : ℝ} (hlam : 0 < lam) (hhi : lam ≤ lamhi) (hL : 0 < L)
    (hlog : 1 ≤ Real.log (p : ℝ)) (hLlog : 1 ≤ L * Real.log (p : ℝ))
    (hqc : qc ∈ Icc (0 : ℝ) (logarithmicOverlapThreshold p lam L))
    (hth : logarithmicOverlapThreshold p lam L ≤ 1) :
    lam * (∫ s in qc..logarithmicOverlapThreshold p lam L,
      (1-s) * (p : ℝ) * ((p-1 : ℕ) : ℝ) * s ^ (p-2)) ≤
        lam * (logarithmicOverlapThreshold p lam L) ^ (p-1) *
          ((p : ℝ) - ((p-1 : ℕ) : ℝ) * logarithmicOverlapThreshold p lam L) ∧
    lam * (logarithmicOverlapThreshold p lam L) ^ (p-1) *
          ((p : ℝ) - ((p-1 : ℕ) : ℝ) * logarithmicOverlapThreshold p lam L) =
        L * Real.log (p : ℝ) * (1-logarithmicOverlapThreshold p lam L +
          logarithmicOverlapThreshold p lam L / (p : ℝ)) ∧
    L * Real.log (p : ℝ) * (1-logarithmicOverlapThreshold p lam L +
          logarithmicOverlapThreshold p lam L / (p : ℝ)) ≤
        (L * (2 * |Real.log lamhi| + 3)) * (Real.log (p : ℝ)) ^ 2 / (p : ℝ) := by
  let q := logarithmicOverlapThreshold p lam L
  have hpn : 0 < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hid : (∫ s in qc..q, (1-s) * (p : ℝ) * ((p-1 : ℕ) : ℝ) * s ^ (p-2)) =
      highDegreeTailPrimitive p q - highDegreeTailPrimitive p qc := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro s _
      convert hasDerivAt_highDegreeTailPrimitive p hp s using 1 <;> ring
    · have hc : Continuous (fun s : ℝ => (1-s) * (p : ℝ) *
          ((p-1 : ℕ) : ℝ) * s ^ (p-2)) := by fun_prop
      exact hc.intervalIntegrable _ _
  have hprimitive : highDegreeTailPrimitive p q =
      q ^ (p-1) * ((p : ℝ) - ((p-1 : ℕ) : ℝ) * q) := by
    unfold highDegreeTailPrimitive
    have he : q ^ p = q ^ (p-1) * q := by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ p)] using pow_succ q (p-1)
    rw [he]
    ring
  have hnonneg := highDegreeTailPrimitive_nonneg (by omega : 1 ≤ p)
    (show qc ∈ Icc (0 : ℝ) 1 from ⟨hqc.1,hqc.2.trans hth⟩)
  have heq : lam * q ^ (p-1) * ((p : ℝ) - ((p-1 : ℕ) : ℝ) * q) =
      L * Real.log (p : ℝ) * (1-q+q/(p : ℝ)) := by
    have hh : lam * q ^ (p-1) = L * Real.log (p : ℝ) / (p : ℝ) := by
      apply (eq_div_iff hpn.ne').mpr
      convert logarithmicOverlapThreshold_power hp hlam hL using 1 <;>
        dsimp only [q] <;> ring
    rw [hh, Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
    field_simp
    <;> ring
  refine ⟨?_,heq,?_⟩
  · change lam * (∫ s in qc..q, (1-s) * (p : ℝ) * ((p-1 : ℕ) : ℝ) * s ^ (p-2)) ≤
      lam * q ^ (p-1) * ((p : ℝ) - ((p-1 : ℕ) : ℝ) * q)
    rw [hid]
    rw [hprimitive]
    nlinarith [mul_nonneg hlam.le hnonneg]
  · rw [←heq]
    exact (logarithmic_high_degree_cost_bound hp hlam hhi hL hLlog hth).trans
      (logarithmicTailBudget_log_sq_bound (by omega) lamhi hL.le hlog)

end GeneralDepthPaper
