module

public import DepthPaper.RevisedLargeVarianceDegrees

@[expose] public section

/-! The logarithmic differential algebra preserves its exact variance degree.
Products retain at least one exponentially small factor. -/
noncomputable section
open Set
namespace DepthPaper

def LogDeficitExpr.varianceDegree : LogDeficitExpr MassResidualNormalizerExpr → ℕ
  | .atom a => a.varianceDegree
  | .add a b => max a.varianceDegree b.varianceDegree
  | .mul a b => a.varianceDegree + b.varianceDegree
  | _ => 0

theorem LogDeficitExpr.varianceDegree_differentiate
    (e : LogDeficitExpr MassResidualNormalizerExpr)
    (da : MassResidualNormalizerExpr → MassResidualNormalizerExpr)
    (dz : MassResidualNormalizerExpr) (dm : ℝ) (n : ℕ)
    (ha : ∀ a, (da a).varianceDegree ≤ a.varianceDegree + n)
    (hz : dz.varianceDegree ≤ n) :
    (e.differentiate da dz dm).varianceDegree ≤ e.varianceDegree + n := by
  induction e <;> simp_all [differentiate, varianceDegree] <;> omega

theorem LogDeficitExpr.sharp_polynomial_bound
    (e : LogDeficitExpr MassResidualNormalizerExpr) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ m ∈ Icc ε 1, ∀ V ≥ 1, ∀ x,
      ‖e.physicalEval m V x‖ ≤ C * V ^ e.varianceDegree := by
  induction e with
  | const c =>
    refine ⟨‖c‖ + 1, by positivity, ?_⟩
    intro m hm V hV x
    simp only [physicalEval, eval, varianceDegree, pow_zero, mul_one]
    linarith
  | atom a =>
    obtain ⟨C, hC, ha⟩ := a.sharp_exponential_bound hε
    refine ⟨C, hC, ?_⟩
    intro m hm V hV x
    have hexp : Real.exp (-(ε ^ 2) * V / 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ε])
    exact (ha m hm V hV x).trans
      (mul_le_mul_of_nonneg_left hexp (by positivity) |>.trans_eq (mul_one _))
  | invden =>
    refine ⟨2, by norm_num, ?_⟩
    intro m hm V hV x
    have hb := normalizedDeficit_bounds (hε.trans_le hm.1) hm.2 V x (zero_le_one.trans hV)
    change ‖(1 - normalizedDeficit m V x)⁻¹‖ ≤ 2 * V ^ 0
    have hp : 0 < 1 - normalizedDeficit m V x := by linarith
    rw [Real.norm_of_nonneg (inv_nonneg.mpr hp.le), pow_zero, mul_one]
    have hh : 1 / 2 ≤ 1 - normalizedDeficit m V x := by linarith
    have hi := inv_le_inv₀ hp (by norm_num : (0 : ℝ) < 1 / 2) |>.mpr hh
    norm_num at hi ⊢
    exact hi
  | logden =>
    refine ⟨1, by norm_num, ?_⟩
    intro m hm V hV x
    have hb := normalizedDeficit_bounds (hε.trans_le hm.1) hm.2 V x (zero_le_one.trans hV)
    have hh := norm_log_one_sub_normalizedDeficit (hε.trans_le hm.1) hm.2 V x
      (zero_le_one.trans hV)
    rw [Real.norm_of_nonneg hb.1] at hh
    change ‖Real.log (1 - normalizedDeficit m V x)‖ ≤ 1 * V ^ 0
    simp only [pow_zero, mul_one]
    linarith
  | massInv =>
    refine ⟨ε⁻¹, inv_pos.mpr hε, ?_⟩
    intro m hm V hV x
    have hm0 := hε.trans_le hm.1
    change ‖m⁻¹‖ ≤ ε⁻¹ * V ^ 0
    rw [Real.norm_of_nonneg (inv_nonneg.mpr hm0.le), pow_zero, mul_one]
    exact (inv_le_inv₀ hm0 hε).mpr hm.1
  | add a b ha hb =>
    obtain ⟨A, hA, ha⟩ := ha
    obtain ⟨B, hB, hb⟩ := hb
    refine ⟨A + B, add_pos hA hB, ?_⟩
    intro m hm V hV x
    change ‖a.physicalEval m V x + b.physicalEval m V x‖ ≤ _
    calc
      _ ≤ ‖a.physicalEval m V x‖ + ‖b.physicalEval m V x‖ := norm_add_le _ _
      _ ≤ A * V ^ a.varianceDegree + B * V ^ b.varianceDegree :=
        add_le_add (ha m hm V hV x) (hb m hm V hV x)
      _ ≤ A * V ^ (max a.varianceDegree b.varianceDegree) +
          B * V ^ (max a.varianceDegree b.varianceDegree) :=
        add_le_add
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hV (le_max_left _ _)) hA.le)
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hV (le_max_right _ _)) hB.le)
      _ = (A + B) * V ^ (LogDeficitExpr.add a b).varianceDegree := by
        simp only [varianceDegree]; ring
  | mul a b ha hb =>
    obtain ⟨A, hA, ha⟩ := ha
    obtain ⟨B, hB, hb⟩ := hb
    refine ⟨A * B, mul_pos hA hB, ?_⟩
    intro m hm V hV x
    change ‖a.physicalEval m V x * b.physicalEval m V x‖ ≤ _
    rw [norm_mul]
    have hh := mul_le_mul (ha m hm V hV x) (hb m hm V hV x) (norm_nonneg _)
      (by positivity)
    exact hh.trans_eq (by simp only [varianceDegree, pow_add]; ring)

theorem normalizedDeficit_sharp_exponential_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ m ∈ Icc ε 1, ∀ V ≥ 1, ∀ x,
      ‖normalizedDeficit m V x‖ ≤ C * Real.exp (-(ε ^ 2) * V / 2) := by
  simpa [MassResidualNormalizerExpr.eval, NormalizerExpr.weightedEval, NormalizerExpr.eval,
    normalizedDeficit, MassResidualNormalizerExpr.varianceDegree, NormalizerExpr.varianceDegree]
    using (MassResidualNormalizerExpr.atom 0 0 (.const 1)).sharp_exponential_bound hε

theorem LogDeficitExpr.small_sharp_exponential_bound
    (e : LogDeficitExpr MassResidualNormalizerExpr) {ε : ℝ} (hε : 0 < ε) (he : e.Small) :
    ∃ C : ℝ, 0 < C ∧ ∀ m ∈ Icc ε 1, ∀ V ≥ 1, ∀ x,
      ‖e.physicalEval m V x‖ ≤ C * V ^ e.varianceDegree * Real.exp (-(ε ^ 2) * V / 2) := by
  revert he
  induction e with
  | const c =>
    intro he
    have hc : c = 0 := he
    refine ⟨1, by norm_num, ?_⟩
    intro m hm V hV x
    simp only [physicalEval, eval, hc, norm_zero, varianceDegree, pow_zero, one_mul]
    exact (Real.exp_pos _).le
  | atom a => intro _; exact a.sharp_exponential_bound hε
  | invden => intro he; exact False.elim he
  | logden =>
    intro _
    obtain ⟨C, hC, hδ⟩ := normalizedDeficit_sharp_exponential_bound hε
    refine ⟨2 * C, by positivity, ?_⟩
    intro m hm V hV x
    change ‖Real.log (1 - normalizedDeficit m V x)‖ ≤ _
    exact (norm_log_one_sub_normalizedDeficit (hε.trans_le hm.1) hm.2 V x
      (zero_le_one.trans hV)).trans
        (mul_le_mul_of_nonneg_left (hδ m hm V hV x) (by norm_num) |>.trans_eq
          (by simp only [varianceDegree, pow_zero]; ring))
  | massInv => intro he; exact False.elim he
  | add a b ha hb =>
    intro he
    obtain ⟨A, hA, ha⟩ := ha he.1
    obtain ⟨B, hB, hb⟩ := hb he.2
    refine ⟨A + B, add_pos hA hB, ?_⟩
    intro m hm V hV x
    change ‖a.physicalEval m V x + b.physicalEval m V x‖ ≤ _
    calc
      _ ≤ ‖a.physicalEval m V x‖ + ‖b.physicalEval m V x‖ := norm_add_le _ _
      _ ≤ A * V ^ a.varianceDegree * Real.exp (-(ε ^ 2) * V / 2) +
          B * V ^ b.varianceDegree * Real.exp (-(ε ^ 2) * V / 2) :=
        add_le_add (ha m hm V hV x) (hb m hm V hV x)
      _ ≤ A * V ^ (max a.varianceDegree b.varianceDegree) * Real.exp (-(ε ^ 2) * V / 2) +
          B * V ^ (max a.varianceDegree b.varianceDegree) * Real.exp (-(ε ^ 2) * V / 2) :=
        add_le_add
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hV (le_max_left _ _)) hA.le) (Real.exp_pos _).le)
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hV (le_max_right _ _)) hB.le) (Real.exp_pos _).le)
      _ = (A + B) * V ^ (LogDeficitExpr.add a b).varianceDegree *
          Real.exp (-(ε ^ 2) * V / 2) := by simp only [varianceDegree]; ring
  | mul a b ha hb =>
    intro he
    rcases he with he | he
    · obtain ⟨A, hA, ha⟩ := ha he
      obtain ⟨B, hB, hb⟩ := b.sharp_polynomial_bound hε
      refine ⟨A * B, mul_pos hA hB, ?_⟩
      intro m hm V hV x
      change ‖a.physicalEval m V x * b.physicalEval m V x‖ ≤ _
      rw [norm_mul]
      have hh := mul_le_mul (ha m hm V hV x) (hb m hm V hV x)
        (norm_nonneg _) (by positivity)
      exact hh.trans_eq (by simp only [varianceDegree, pow_add]; ring)
    · obtain ⟨A, hA, ha⟩ := a.sharp_polynomial_bound hε
      obtain ⟨B, hB, hb⟩ := hb he
      refine ⟨A * B, mul_pos hA hB, ?_⟩
      intro m hm V hV x
      change ‖a.physicalEval m V x * b.physicalEval m V x‖ ≤ _
      rw [norm_mul]
      have hh := mul_le_mul (ha m hm V hV x) (hb m hm V hV x)
        (norm_nonneg _) (by positivity)
      exact hh.trans_eq (by simp only [varianceDegree, pow_add]; ring)

theorem LogDeficitExpr.varianceDegree_massDx (e : LogDeficitExpr MassResidualNormalizerExpr) :
    e.massDx.varianceDegree ≤ e.varianceDegree := by
  simpa only [massDx, Nat.add_zero] using e.varianceDegree_differentiate
    MassResidualNormalizerExpr.dx deficitBaseExpr.lift.dx 0 0
    (fun a => by simpa using a.varianceDegree_dx)
    (by simp [deficitBaseExpr, ResidualNormalizerExpr.lift, MassResidualNormalizerExpr.dx,
      MassResidualNormalizerExpr.varianceDegree, NormalizerExpr.weightedDx,
      NormalizerExpr.dx, NormalizerExpr.varianceDegree, normalizerSpaceGenerator])

theorem LogDeficitExpr.varianceDegree_massDV (e : LogDeficitExpr MassResidualNormalizerExpr) :
    e.massDV.varianceDegree ≤ e.varianceDegree := by
  simpa only [massDV, Nat.add_zero] using e.varianceDegree_differentiate
    MassResidualNormalizerExpr.dV deficitBaseExpr.lift.dV 0 0
    (fun a => by simpa using a.varianceDegree_dV)
    (by simp [deficitBaseExpr, ResidualNormalizerExpr.lift, MassResidualNormalizerExpr.dV,
      MassResidualNormalizerExpr.varianceDegree, NormalizerExpr.weightedDV,
      NormalizerExpr.dV, NormalizerExpr.varianceDegree, normalizerVarianceGenerator])

theorem LogDeficitExpr.varianceDegree_dm (e : LogDeficitExpr MassResidualNormalizerExpr) :
    e.dm.varianceDegree ≤ e.varianceDegree + 1 := by
  exact e.varianceDegree_differentiate MassResidualNormalizerExpr.dm deficitBaseExpr.lift.dm 1 1
    (fun a => a.varianceDegree_dm)
    (by simp [deficitBaseExpr, ResidualNormalizerExpr.lift, MassResidualNormalizerExpr.dm,
      MassResidualNormalizerExpr.varianceDegree, NormalizerExpr.weightedDm,
      NormalizerExpr.dm, NormalizerExpr.varianceDegree, normalizerMassGenerator])

theorem varianceDegree_iterate_le {α : Type} (degree : α → ℕ) (f : α → α)
    (n : ℕ) (hf : ∀ a, degree (f a) ≤ degree a + n) (a : α) (r : ℕ) :
    degree (f^[r] a) ≤ degree a + r * n := by
  induction r with
  | zero => simp
  | succ r hr =>
    rw [Function.iterate_succ_apply']
    have h := hf (f^[r] a)
    rw [Nat.succ_mul]
    omega

theorem logarithmicError_source_expr_varianceDegree (i j k : ℕ) :
    (LogDeficitExpr.massDx^[i] (LogDeficitExpr.dm^[j]
      (LogDeficitExpr.massDV^[k] errorMassBaseExpr))).varianceDegree ≤ j := by
  have hk := varianceDegree_iterate_le LogDeficitExpr.varianceDegree LogDeficitExpr.massDV 0
    (fun a => by simpa using a.varianceDegree_massDV) errorMassBaseExpr k
  have hj := varianceDegree_iterate_le LogDeficitExpr.varianceDegree LogDeficitExpr.dm 1
    (fun a => a.varianceDegree_dm) (LogDeficitExpr.massDV^[k] errorMassBaseExpr) j
  have hi := varianceDegree_iterate_le LogDeficitExpr.varianceDegree LogDeficitExpr.massDx 0
    (fun a => by simpa using a.varianceDegree_massDx)
    (LogDeficitExpr.dm^[j] (LogDeficitExpr.massDV^[k] errorMassBaseExpr)) i
  have hb : errorMassBaseExpr.varianceDegree = 0 := rfl
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, hb] at hk hj hi
  omega

end DepthPaper
