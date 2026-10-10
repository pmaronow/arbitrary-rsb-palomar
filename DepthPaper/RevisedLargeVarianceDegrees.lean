module

public import DepthPaper.SourceLogarithmicErrorBounds

@[expose] public section

/-! Separate variance and spatial degrees in the finite differential algebra.
This retains the exact exponential rate in Appendix C.1. -/
noncomputable section
open Set
namespace DepthPaper

def NormalizerExpr.varianceDegree : NormalizerExpr → ℕ
  | .variance => 1
  | .add a b => max a.varianceDegree b.varianceDegree
  | .mul a b => a.varianceDegree + b.varianceDegree
  | _ => 0

def NormalizerExpr.spaceDegree : NormalizerExpr → ℕ
  | .space => 1
  | .add a b => max a.spaceDegree b.spaceDegree
  | .mul a b => a.spaceDegree + b.spaceDegree
  | _ => 0

theorem NormalizerExpr.separate_polynomial_bound (e : NormalizerExpr) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ m ∈ Icc (0 : ℝ) 1, ∀ V ≥ 1, ∀ x,
      ‖e.eval m V x‖ ≤ C * V ^ e.varianceDegree * (1 + |x|) ^ e.spaceDegree := by
  induction e with
  | const c =>
    refine ⟨max ‖c‖ 1, le_max_right _ _, ?_⟩
    intro m hm V hV x
    simpa [eval, varianceDegree, spaceDegree] using le_max_left ‖c‖ 1
  | mass =>
    refine ⟨1, le_rfl, ?_⟩
    intro m hm V hV x
    simpa [eval, varianceDegree, spaceDegree, Real.norm_of_nonneg hm.1] using hm.2
  | variance =>
    refine ⟨1, le_rfl, ?_⟩
    intro m hm V hV x
    simp [eval, varianceDegree, spaceDegree, Real.norm_of_nonneg (zero_le_one.trans hV)]
  | space =>
    refine ⟨1, le_rfl, ?_⟩
    intro m hm V hV x
    simp [eval, varianceDegree, spaceDegree, Real.norm_eq_abs]
  | tangent =>
    refine ⟨1, le_rfl, ?_⟩
    intro m hm V hV x
    simpa [eval, varianceDegree, spaceDegree, Real.norm_eq_abs] using
      (Real.abs_tanh_lt_one (m * x)).le
  | add a b ha hb =>
    obtain ⟨A, hA, ha⟩ := ha
    obtain ⟨B, hB, hb⟩ := hb
    refine ⟨A + B, by linarith, ?_⟩
    intro m hm V hV x
    have hR : 1 ≤ 1 + |x| := by linarith [abs_nonneg x]
    have ha' : A * V ^ a.varianceDegree * (1 + |x|) ^ a.spaceDegree ≤
        A * V ^ (max a.varianceDegree b.varianceDegree) *
          (1 + |x|) ^ (max a.spaceDegree b.spaceDegree) := by
      gcongr
      · exact le_max_left _ _
      · exact le_max_left _ _
    have hb' : B * V ^ b.varianceDegree * (1 + |x|) ^ b.spaceDegree ≤
        B * V ^ (max a.varianceDegree b.varianceDegree) *
          (1 + |x|) ^ (max a.spaceDegree b.spaceDegree) := by
      gcongr
      · exact le_max_right _ _
      · exact le_max_right _ _
    change ‖a.eval m V x + b.eval m V x‖ ≤ _
    exact (norm_add_le _ _).trans ((add_le_add ((ha m hm V hV x).trans ha')
      ((hb m hm V hV x).trans hb')).trans_eq (by simp only [varianceDegree, spaceDegree]; ring))
  | mul a b ha hb =>
    obtain ⟨A, hA, ha⟩ := ha
    obtain ⟨B, hB, hb⟩ := hb
    refine ⟨A * B, by nlinarith [mul_le_mul_of_nonneg_left hB (zero_le_one.trans hA)], ?_⟩
    intro m hm V hV x
    simp only [eval, norm_mul, varianceDegree, spaceDegree]
    have hh := mul_le_mul (ha m hm V hV x) (hb m hm V hV x) (norm_nonneg _)
      (show 0 ≤ A * V ^ a.varianceDegree * (1 + |x|) ^ a.spaceDegree by positivity)
    convert hh using 1 <;> rw [pow_add, pow_add] <;> ring

theorem NormalizerExpr.varianceDegree_dx (e : NormalizerExpr) :
    e.dx.varianceDegree ≤ e.varianceDegree := by
  induction e <;> simp_all [dx, varianceDegree] <;> omega

theorem NormalizerExpr.varianceDegree_dm (e : NormalizerExpr) :
    e.dm.varianceDegree ≤ e.varianceDegree := by
  induction e <;> simp_all [dm, varianceDegree] <;> omega

theorem NormalizerExpr.varianceDegree_dV (e : NormalizerExpr) :
    e.dV.varianceDegree ≤ e.varianceDegree := by
  induction e <;> simp_all [dV, varianceDegree] <;> omega

theorem NormalizerExpr.varianceDegree_weightedDx (e : NormalizerExpr) :
    e.weightedDx.varianceDegree ≤ e.varianceDegree := by
  simpa [weightedDx, varianceDegree, normalizerSpaceGenerator] using e.varianceDegree_dx

theorem NormalizerExpr.varianceDegree_weightedDm (e : NormalizerExpr) :
    e.weightedDm.varianceDegree ≤ e.varianceDegree + 1 := by
  have h := e.varianceDegree_dm
  simp only [weightedDm, varianceDegree, normalizerMassGenerator]
  omega

theorem NormalizerExpr.varianceDegree_weightedDV (e : NormalizerExpr) :
    e.weightedDV.varianceDegree ≤ e.varianceDegree := by
  simpa [weightedDV, varianceDegree, normalizerVarianceGenerator] using e.varianceDegree_dV

theorem NormalizerExpr.weighted_sharp_exponential_bound (e : NormalizerExpr)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ m ∈ Icc ε 1, ∀ V ≥ 1, ∀ x,
      ‖e.weightedEval m V x‖ ≤ C * V ^ e.varianceDegree * Real.exp (-(ε ^ 2) * V / 2) := by
  obtain ⟨C, hC, hbound⟩ := e.separate_polynomial_bound
  let d := e.spaceDegree
  let A : ℝ := (d.factorial : ℝ) / ε ^ d * Real.exp ε
  have hA : 0 < A := by
    dsimp only [A]
    have hf : 0 < (d.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos d
    positivity
  refine ⟨2 * C * A, by positivity, ?_⟩
  intro m hm V hV x
  have hm' : m ∈ Icc (0 : ℝ) 1 := ⟨hε.le.trans hm.1, hm.2⟩
  have hp : (1 + |x|) ^ d * Real.exp (-ε * |x|) ≤ A := by
    simpa only [mul_one] using polynomial_times_exp_bound d hε
      (by norm_num : (0 : ℝ) ≤ 1) (abs_nonneg x)
  unfold weightedEval
  rw [norm_mul]
  have hh := mul_le_mul (hbound m hm' V hV x) (normalizerInverse_decay hε hm hV x)
    (norm_nonneg _) (show 0 ≤ C * V ^ e.varianceDegree * (1 + |x|) ^ d by positivity)
  calc
    ‖e.eval m V x‖ * ‖normalizerInverse m V x‖ ≤
        (2 * C * V ^ e.varianceDegree * Real.exp (-(ε ^ 2) * V / 2)) *
          ((1 + |x|) ^ d * Real.exp (-ε * |x|)) := hh.trans_eq (by ring)
    _ ≤ (2 * C * V ^ e.varianceDegree * Real.exp (-(ε ^ 2) * V / 2)) * A :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (2 * C * A) * V ^ e.varianceDegree * Real.exp (-(ε ^ 2) * V / 2) := by ring

def MassResidualNormalizerExpr.varianceDegree : MassResidualNormalizerExpr → ℕ
  | .atom _ _ e => e.varianceDegree
  | .add a b => max a.varianceDegree b.varianceDegree
  | .scale _ a => a.varianceDegree

theorem MassResidualNormalizerExpr.varianceDegree_dx (a : MassResidualNormalizerExpr) :
    a.dx.varianceDegree ≤ a.varianceDegree := by
  induction a with
  | atom i j e => simpa [dx, varianceDegree] using e.varianceDegree_weightedDx
  | add a b ha hb => simp only [dx, varianceDegree]; omega
  | scale c a ha => exact ha

theorem MassResidualNormalizerExpr.varianceDegree_dV (a : MassResidualNormalizerExpr) :
    a.dV.varianceDegree ≤ a.varianceDegree := by
  induction a with
  | atom i j e => simpa [dV, varianceDegree] using e.varianceDegree_weightedDV
  | add a b ha hb => simp only [dV, varianceDegree]; omega
  | scale c a ha => exact ha

theorem MassResidualNormalizerExpr.varianceDegree_dm (a : MassResidualNormalizerExpr) :
    a.dm.varianceDegree ≤ a.varianceDegree + 1 := by
  induction a with
  | atom i j e =>
    have h := e.varianceDegree_weightedDm
    simp only [dm, varianceDegree]
    omega
  | add a b ha hb => simp only [dm, varianceDegree]; omega
  | scale c a ha => exact ha

theorem MassResidualNormalizerExpr.sharp_exponential_bound (a : MassResidualNormalizerExpr)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ m ∈ Icc ε 1, ∀ V ≥ 1, ∀ x,
      ‖a.eval m V x‖ ≤ C * V ^ a.varianceDegree * Real.exp (-(ε ^ 2) * V / 2) := by
  induction a with
  | atom i j e =>
    let δ : ℝ := min ε (1 / 2)
    have hδ : 0 < δ := lt_min hε (by norm_num)
    obtain ⟨K, hK, hheat⟩ := residualHeatMassJet_uniform_bound i j hδ
    obtain ⟨C, hC, he⟩ := e.weighted_sharp_exponential_bound hε
    refine ⟨K * C, mul_pos hK hC, ?_⟩
    intro m hm V hV x
    have hmδ : m ∈ Icc δ (2 - δ) := by
      constructor
      · exact (min_le_left _ _).trans hm.1
      · have hd : δ ≤ 1 / 2 := min_le_right _ _
        linarith [hm.2]
    change ‖residualHeatMassJet i j m V.toNNReal x * e.weightedEval m V x‖ ≤ _
    rw [norm_mul]
    have hh := mul_le_mul (hheat m hmδ V.toNNReal x) (he m hm V hV x)
      (norm_nonneg _) hK.le
    exact hh.trans_eq (by simp only [varianceDegree]; ring)
  | add a b ha hb =>
    obtain ⟨A, hA, ha⟩ := ha
    obtain ⟨B, hB, hb⟩ := hb
    refine ⟨A + B, add_pos hA hB, ?_⟩
    intro m hm V hV x
    have hvd : V ^ a.varianceDegree ≤ V ^ (max a.varianceDegree b.varianceDegree) :=
      pow_le_pow_right₀ hV (le_max_left _ _)
    have hve : V ^ b.varianceDegree ≤ V ^ (max a.varianceDegree b.varianceDegree) :=
      pow_le_pow_right₀ hV (le_max_right _ _)
    change ‖a.eval m V x + b.eval m V x‖ ≤ _
    calc
      _ ≤ ‖a.eval m V x‖ + ‖b.eval m V x‖ := norm_add_le _ _
      _ ≤ A * V ^ a.varianceDegree * Real.exp (-(ε ^ 2) * V / 2) +
          B * V ^ b.varianceDegree * Real.exp (-(ε ^ 2) * V / 2) :=
        add_le_add (ha m hm V hV x) (hb m hm V hV x)
      _ ≤ A * V ^ (max a.varianceDegree b.varianceDegree) * Real.exp (-(ε ^ 2) * V / 2) +
          B * V ^ (max a.varianceDegree b.varianceDegree) * Real.exp (-(ε ^ 2) * V / 2) :=
        add_le_add
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hvd hA.le) (Real.exp_pos _).le)
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hve hB.le) (Real.exp_pos _).le)
      _ = (A + B) * V ^ (MassResidualNormalizerExpr.add a b).varianceDegree *
          Real.exp (-(ε ^ 2) * V / 2) := by simp only [varianceDegree]; ring
  | scale c a ha =>
    obtain ⟨A, hA, ha⟩ := ha
    refine ⟨(‖c‖ + 1) * A, by positivity, ?_⟩
    intro m hm V hV x
    change ‖c * a.eval m V x‖ ≤ _
    rw [norm_mul]
    have hh := mul_le_mul_of_nonneg_left (ha m hm V hV x) (norm_nonneg c)
    have hv : 0 ≤ A * V ^ a.varianceDegree * Real.exp (-(ε ^ 2) * V / 2) := by positivity
    exact hh.trans ((mul_le_mul_of_nonneg_right (by linarith : ‖c‖ ≤ ‖c‖ + 1) hv).trans_eq
      (by simp only [varianceDegree]; ring))

end DepthPaper
