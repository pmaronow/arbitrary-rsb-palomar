module

public import DepthPaper.RevisedLargeVarianceLogBounds
public import DepthPaper.LargeVarianceCompactZeroth

@[expose] public section

/-! Appendix C.1 with the revised polynomial degree and exact decay rate.
The literal derivative order is variance, mass, then space. The intermediate
bound has variance degree at most the number of mass derivatives. -/
noncomputable section
open Set
open scoped BigOperators NNReal
namespace DepthPaper

theorem logarithmicError_source_mixed_sharp_bound (i j k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ m ∈ Icc ε 1, ∀ V ≥ 1, ∀ x,
      ‖iteratedDeriv i (fun y => iteratedDeriv j (fun r => iteratedDeriv k
        (fun v => logarithmicError r v y) V) m) x‖ ≤
          C * V ^ j * Real.exp (-(ε ^ 2) * V / 2) := by
  let a := LogDeficitExpr.massDx^[i] (LogDeficitExpr.dm^[j]
    (LogDeficitExpr.massDV^[k] errorMassBaseExpr))
  have hbase : errorMassBaseExpr.Small := by exact Or.inr trivial
  have hk := LogDeficitExpr.small_iterate_differentiate errorMassBaseExpr
    MassResidualNormalizerExpr.dV deficitBaseExpr.lift.dV 0 k hbase
  have hj := LogDeficitExpr.small_iterate_differentiate _
    MassResidualNormalizerExpr.dm deficitBaseExpr.lift.dm 1 j hk
  have ha : a.Small := LogDeficitExpr.small_iterate_differentiate _
    MassResidualNormalizerExpr.dx deficitBaseExpr.lift.dx 0 i hj
  obtain ⟨C, hC, hbound⟩ := a.small_sharp_exponential_bound hε ha
  refine ⟨C, hC, ?_⟩
  intro m hm V hV x
  have hm' : m ∈ Ioo (0 : ℝ) 2 :=
    ⟨hε.trans_le hm.1, hm.2.trans_lt (by norm_num)⟩
  rw [logarithmicError_source_mixed_eq i j k hm' (zero_lt_one.trans_le hV)]
  exact (hbound m hm V hV x).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hV (logarithmicError_source_expr_varianceDegree i j k)) hC.le)
    (Real.exp_pos _).le)

theorem largeVarianceError_source_mixed_sharp_bound (i j k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ m ∈ Icc ε 1, ∀ V ≥ 1, ∀ x,
      ‖iteratedDeriv i (fun y => iteratedDeriv j (fun r => iteratedDeriv k
        (fun v => largeVarianceError r v.toNNReal y) V) m) x‖ ≤
          C * V ^ j * Real.exp (-(ε ^ 2) * V / 2) := by
  obtain ⟨C, hC, hbound⟩ := logarithmicError_source_mixed_sharp_bound i j k hε
  refine ⟨C, hC, ?_⟩
  intro m hm V hV x
  have hm' : m ∈ Ioo (0 : ℝ) 2 :=
    ⟨hε.trans_le hm.1, hm.2.trans_lt (by norm_num)⟩
  rw [largeVarianceError_source_mixed_eq_logarithmicError i j k hm'
    (zero_lt_one.trans_le hV)]
  exact hbound m hm V hV x

theorem largeVarianceError_uniform_sharp_order {ε : ℝ} (hε : 0 < ε) (ell : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m ∈ Icc ε 1, ∀ V ≥ 1, ∀ x : ℝ,
      ∀ i j k : ℕ, i + j + k ≤ ell →
        ‖iteratedDeriv i (fun y => iteratedDeriv j (fun r => iteratedDeriv k
          (fun v => largeVarianceError r v.toNNReal y) V) m) x‖ ≤
            C * V ^ ell * Real.exp (-(ε ^ 2 / 2) * V) := by
  classical
  let A := Fin (ell + 1) × Fin (ell + 1) × Fin (ell + 1)
  have hf : ∀ a : A, ∃ C : ℝ, 0 < C ∧ ∀ m ∈ Icc ε 1, ∀ V ≥ 1, ∀ x,
      ‖iteratedDeriv a.1.val (fun y => iteratedDeriv a.2.1.val
        (fun r => iteratedDeriv a.2.2.val
          (fun v => largeVarianceError r v.toNNReal y) V) m) x‖ ≤
            C * V ^ a.2.1.val * Real.exp (-(ε ^ 2) * V / 2) :=
    fun a => largeVarianceError_source_mixed_sharp_bound a.1.val a.2.1.val a.2.2.val hε
  choose C hC hb using hf
  let CT : ℝ := 1 + ∑ a : A, C a
  have hs : 0 ≤ ∑ a : A, C a := Finset.sum_nonneg (fun a _ => (hC a).le)
  have hCT : 0 < CT := by dsimp only [CT]; linarith
  refine ⟨CT, hCT, ?_⟩
  intro m hm V hV x i j k hijk
  have hi : i < ell + 1 := by omega
  have hj : j < ell + 1 := by omega
  have hk : k < ell + 1 := by omega
  let a : A := (⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩)
  have hCa : C a ≤ CT := by
    have hh : C a ≤ ∑ a : A, C a :=
      Finset.single_le_sum (fun b _ => (hC b).le) (Finset.mem_univ a)
    exact hh.trans (by dsimp only [CT]; linarith)
  have hp : V ^ j ≤ V ^ ell := pow_le_pow_right₀ hV (by omega)
  have hbd := hb a m hm V hV x
  change ‖iteratedDeriv i (fun y => iteratedDeriv j (fun r => iteratedDeriv k
    (fun v => largeVarianceError r v.toNNReal y) V) m) x‖ ≤
      C a * V ^ j * Real.exp (-(ε ^ 2) * V / 2) at hbd
  have hmulp : C a * V ^ j ≤ CT * V ^ ell :=
    mul_le_mul hCa hp (by positivity) hCT.le
  have he : -(ε ^ 2) * V / 2 = -(ε ^ 2 / 2) * V := by ring
  exact hbd.trans (mul_le_mul_of_nonneg_right hmulp (Real.exp_pos _).le |>.trans_eq
    (by rw [he]))

/-- Revised Appendix C.1. `sInf I` is the minimum of the nonempty compact
positive mass set. The cutoff `1` works for every derivative order. -/
theorem large_variance_sharp (I : Set ℝ) (hI : IsCompact I) (hne : I.Nonempty)
    (hsub : I ⊆ Ioc (0 : ℝ) 1) :
    ∃ Vbar : ℝ, 1 ≤ Vbar ∧
      (∀ m ∈ I, ∀ V : ℝ≥0, ∀ x : ℝ,
        ColeHopfFoundation.ProbabilityTheory.coleHopf m V
            (fun y => Real.log (Real.cosh y)) x =
          m * (V : ℝ) / 2 + (1 / m - 1) * Real.log 2 +
            (1 / m) * Real.log (Real.cosh (m * x)) + largeVarianceError m V x) ∧
      ∀ ell : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ m ∈ I, ∀ V : ℝ, Vbar ≤ V →
        ∀ x : ℝ, ∀ i j k : ℕ, i + j + k ≤ ell →
          ‖iteratedDeriv i (fun y => iteratedDeriv j (fun r => iteratedDeriv k
            (fun v => largeVarianceError r v.toNNReal y) V) m) x‖ ≤
              C * V ^ ell * Real.exp (-((sInf I) ^ 2 / 2) * V) := by
  have hmin := hI.isLeast_sInf hne
  have hε : 0 < sInf I := (hsub hmin.1).1
  refine ⟨1, le_rfl, ?_, ?_⟩
  · intro m hm V x
    exact coleHopf_largeVariance_expansion m V x
  · intro ell
    obtain ⟨C, hC, hbound⟩ := largeVarianceError_uniform_sharp_order hε ell
    refine ⟨C, hC, ?_⟩
    intro m hm V hV x i j k hijk
    exact hbound m ⟨hmin.2 hm, (hsub hm).2⟩ V hV x i j k hijk

/-- Spatial derivatives satisfy the revised bound at the prescribed rate. -/
theorem largeVarianceError_spatial_sharp (I : Set ℝ) (hI : IsCompact I)
    (hne : I.Nonempty) (hsub : I ⊆ Ioc (0 : ℝ) 1) (ell : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m ∈ I, ∀ V : ℝ, 1 ≤ V → ∀ x : ℝ,
      ∀ i : ℕ, i ≤ ell →
        ‖iteratedDeriv i (largeVarianceError m V.toNNReal) x‖ ≤
          C * V ^ ell * Real.exp (-((sInf I) ^ 2 / 2) * V) := by
  have hmin := hI.isLeast_sInf hne
  obtain ⟨C, hC, hb⟩ := largeVarianceError_uniform_sharp_order (hsub hmin.1).1 ell
  refine ⟨C, hC, ?_⟩
  intro m hm V hV x i hi
  simpa only [iteratedDeriv_zero, Nat.add_zero] using
    hb m ⟨hmin.2 hm, (hsub hm).2⟩ V hV x i 0 0 hi

end DepthPaper
