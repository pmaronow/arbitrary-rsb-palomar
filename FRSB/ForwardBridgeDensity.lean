module

public import FRSB.ForwardBridge

@[expose] public section


/-! Smoothness and uniform all-order bounds for the concrete forward
Gaussian-bridge density candidate.  No diffusion-law premise is used. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper Filter
open scoped ContDiff Topology
namespace FRSB

def forwardBridgeDerivativeConstant (β : ℝ) (j : ℕ) : ℝ :=
  uniformSpatialConstant β (j - 1)

def forwardBridgeExponentialConstant (β : ℝ) (j : ℕ) : ℝ :=
  exponentialDerivativeConstant (forwardBridgeDerivativeConstant β) j

lemma forwardBridgeExponentialConstant_nonneg (β : ℝ) (j : ℕ) :
    0 ≤ forwardBridgeExponentialConstant β j :=
  exponentialDerivativeConstant_nonneg _ (fun n => (uniformSpatialConstant_pos β _).le) j

def forwardBridgePathFactor (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) : ℝ :=
  Real.exp (-forwardBridgeAction β μ s hs path x)

theorem forwardBridgePathFactor_pos (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) :
    0 < forwardBridgePathFactor β μ s hs path x := Real.exp_pos _

theorem forwardBridgePathFactor_le_one (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) :
    forwardBridgePathFactor β μ s hs path x ≤ 1 :=
  Real.exp_le_one_iff.mpr (neg_nonpos.mpr (forwardBridgeAction_nonneg β μ s hs path x))

theorem contDiff_forwardBridgePathFactor (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) :
    ContDiff ℝ ∞ (forwardBridgePathFactor β μ s hs path) :=
  (contDiff_forwardBridgeAction β μ s hs path).neg.exp

theorem continuous_iteratedDeriv_forwardBridgePathFactor (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) :
    Continuous (fun p : ForwardBridgePath × ℝ =>
      iteratedDeriv j (forwardBridgePathFactor β μ s hs p.1) p.2) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero => exact Real.continuous_exp.comp (continuous_forwardBridgeJet β μ s hs 0).neg
    | succ n =>
      have he : (fun p : ForwardBridgePath × ℝ =>
          iteratedDeriv (n + 1) (forwardBridgePathFactor β μ s hs p.1) p.2) =
          fun p => ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            (-1 * forwardBridgeJet β μ s hs (i + 1) p.1 p.2) *
              iteratedDeriv (n - i) (forwardBridgePathFactor β μ s hs p.1) p.2 := by
        funext p
        have h := exp_neg_mul_iteratedDeriv_formula (forwardBridgeAction β μ s hs p.1) 1
          (contDiff_forwardBridgeAction β μ s hs p.1) n p.2
        unfold forwardBridgePathFactor
        simpa only [neg_mul, one_mul, forwardBridgePathFactor,
          iteratedDeriv_forwardBridgeAction] using h
      rw [he]
      apply continuous_finset_sum
      intro i hi
      exact (continuous_const.mul (continuous_const.mul
        (continuous_forwardBridgeJet β μ s hs (i + 1)))).mul (ih (n - i) (by omega))

theorem norm_iteratedDeriv_forwardBridgePathFactor_le (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (path : ForwardBridgePath) (x : ℝ) :
    ‖iteratedDeriv j (forwardBridgePathFactor β μ s hs path) x‖ ≤
      forwardBridgeExponentialConstant β j * forwardBridgePathFactor β μ s hs path x := by
  have h := norm_iteratedDeriv_exp_neg_mul_le (forwardBridgeAction β μ s hs path) 1
    (contDiff_forwardBridgeAction β μ s hs path) (by norm_num)
    (forwardBridgeDerivativeConstant β) (fun n => (uniformSpatialConstant_pos β _).le)
    (fun n y => by
      rw [iteratedDeriv_forwardBridgeAction]
      exact norm_forwardBridgeJet_succ_le β μ s hs n path y) j x
  unfold forwardBridgePathFactor
  simpa only [forwardBridgePathFactor, forwardBridgeExponentialConstant, neg_mul, one_mul] using h

def forwardBridgeFactor (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) : ℝ :=
  ∫ path, forwardBridgePathFactor β μ s hs path x ∂canonicalWienerMeasure

lemma integrable_forwardBridgePathFactor (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    Integrable (fun path => forwardBridgePathFactor β μ s hs path x) canonicalWienerMeasure :=
  (integrable_const (1 : ℝ)).mono'
    (((continuous_iteratedDeriv_forwardBridgePathFactor β μ s hs 0).comp
      (show Continuous (fun path : ForwardBridgePath => (path, x)) by fun_prop)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun path => by
      rw [Real.norm_of_nonneg (forwardBridgePathFactor_pos β μ s hs path x).le]
      exact forwardBridgePathFactor_le_one β μ s hs path x)

theorem forwardBridgeFactor_pos (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) : 0 < forwardBridgeFactor β μ s hs x := by
  exact integral_pos_iff_support_of_nonneg (fun path =>
    (forwardBridgePathFactor_pos β μ s hs path x).le)
    (integrable_forwardBridgePathFactor β μ s hs x) |>.mpr (by
      have he : Function.support (fun path => forwardBridgePathFactor β μ s hs path x) = univ := by
        ext path
        simp only [Function.mem_support, mem_univ, iff_true]
        exact (forwardBridgePathFactor_pos β μ s hs path x).ne'
      simp [he])

theorem forwardBridgeFactor_le_one (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) : forwardBridgeFactor β μ s hs x ≤ 1 := by
  have h := integral_mono (integrable_forwardBridgePathFactor β μ s hs x)
    (integrable_const (1 : ℝ)) (forwardBridgePathFactor_le_one β μ s hs · x)
  simpa [forwardBridgeFactor] using h

theorem iteratedDeriv_forwardBridgeFactor (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (x : ℝ) :
    iteratedDeriv j (forwardBridgeFactor β μ s hs) x =
      ∫ path, iteratedDeriv j (forwardBridgePathFactor β μ s hs path) x ∂canonicalWienerMeasure := by
  apply iteratedDeriv_integral_uniform canonicalWienerMeasure
    (fun y path => forwardBridgePathFactor β μ s hs path y)
    (contDiff_forwardBridgePathFactor β μ s hs)
    (integrable_forwardBridgePathFactor β μ s hs)
    (fun n y => ((continuous_iteratedDeriv_forwardBridgePathFactor β μ s hs n).comp
      (show Continuous (fun path : ForwardBridgePath => (path, y)) by fun_prop)).aestronglyMeasurable)
    (fun n => forwardBridgeExponentialConstant β (n + 1))
  intro n y path
  exact (norm_iteratedDeriv_forwardBridgePathFactor_le β μ s hs (n + 1) path y).trans
    (mul_le_of_le_one_right (forwardBridgeExponentialConstant_nonneg β _)
      (forwardBridgePathFactor_le_one β μ s hs path y))

theorem contDiff_forwardBridgeFactor (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) : ContDiff ℝ ∞ (forwardBridgeFactor β μ s hs) := by
  apply contDiff_integral_uniform canonicalWienerMeasure
    (fun y path => forwardBridgePathFactor β μ s hs path y)
    (contDiff_forwardBridgePathFactor β μ s hs)
    (integrable_forwardBridgePathFactor β μ s hs)
    (fun n y => ((continuous_iteratedDeriv_forwardBridgePathFactor β μ s hs n).comp
      (show Continuous (fun path : ForwardBridgePath => (path, y)) by fun_prop)).aestronglyMeasurable)
    (fun n => forwardBridgeExponentialConstant β (n + 1))
  intro n y path
  exact (norm_iteratedDeriv_forwardBridgePathFactor_le β μ s hs (n + 1) path y).trans
    (mul_le_of_le_one_right (forwardBridgeExponentialConstant_nonneg β _)
      (forwardBridgePathFactor_le_one β μ s hs path y))

theorem forwardBridgeFactor_relative_derivative_bound (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (x : ℝ) :
    ‖iteratedDeriv j (forwardBridgeFactor β μ s hs) x‖ ≤
      forwardBridgeExponentialConstant β j * forwardBridgeFactor β μ s hs x := by
  have hi : Integrable (fun path =>
      iteratedDeriv j (forwardBridgePathFactor β μ s hs path) x) canonicalWienerMeasure :=
    (integrable_const (forwardBridgeExponentialConstant β j)).mono'
      (((continuous_iteratedDeriv_forwardBridgePathFactor β μ s hs j).comp
        (show Continuous (fun path : ForwardBridgePath => (path, x)) by fun_prop)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun path =>
        (norm_iteratedDeriv_forwardBridgePathFactor_le β μ s hs j path x).trans
          (mul_le_of_le_one_right (forwardBridgeExponentialConstant_nonneg β _)
            (forwardBridgePathFactor_le_one β μ s hs path x)))
  rw [iteratedDeriv_forwardBridgeFactor]
  calc
    _ ≤ ∫ path, ‖iteratedDeriv j (forwardBridgePathFactor β μ s hs path) x‖ ∂canonicalWienerMeasure := norm_integral_le_integral_norm _
    _ ≤ ∫ path, forwardBridgeExponentialConstant β j * forwardBridgePathFactor β μ s hs path x ∂canonicalWienerMeasure :=
      integral_mono hi.norm ((integrable_forwardBridgePathFactor β μ s hs x).const_mul _)
        (norm_iteratedDeriv_forwardBridgePathFactor_le β μ s hs j · x)
    _ = _ := integral_const_mul _ _

def forwardBridgeCorrection (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) : ℝ :=
  -Real.log (forwardBridgeFactor β μ s hs x)

theorem contDiff_forwardBridgeCorrection (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) : ContDiff ℝ ∞ (forwardBridgeCorrection β μ s hs) :=
  ((contDiff_forwardBridgeFactor β μ s hs).log (fun x => (forwardBridgeFactor_pos β μ s hs x).ne')).neg

theorem forwardBridgeCorrection_nonneg (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) : 0 ≤ forwardBridgeCorrection β μ s hs x :=
  neg_nonneg.mpr (Real.log_nonpos (forwardBridgeFactor_pos β μ s hs x).le
    (forwardBridgeFactor_le_one β μ s hs x))

def forwardBridgeRelativeConstant (β : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), forwardBridgeExponentialConstant β i

theorem forwardBridgeRelativeConstant_nonneg (β : ℝ) (k : ℕ) :
    0 ≤ forwardBridgeRelativeConstant β k :=
  Finset.sum_nonneg (fun i hi => forwardBridgeExponentialConstant_nonneg β i)

theorem forwardBridgeExponentialConstant_le_relative (β : ℝ) (k j : ℕ) (hj : j ≤ k) :
    forwardBridgeExponentialConstant β j ≤ forwardBridgeRelativeConstant β k :=
  Finset.single_le_sum (fun i hi => forwardBridgeExponentialConstant_nonneg β i)
    (Finset.mem_range.mpr (by omega))

/-- Every positive-order derivative has a bound depending only on beta
and its order, uniform over measures and positive times. -/
theorem forwardBridgeCorrection_uniform_derivative_bound (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (hj : 1 ≤ j) (x : ℝ) :
    ‖iteratedDeriv j (forwardBridgeCorrection β μ s hs) x‖ ≤
      negativeLogDerivativeConstant (forwardBridgeRelativeConstant β j) j := by
  apply norm_iteratedDeriv_negativeLog_le (forwardBridgeFactor β μ s hs)
    (contDiff_forwardBridgeFactor β μ s hs) (forwardBridgeFactor_pos β μ s hs)
    (forwardBridgeRelativeConstant β j) (forwardBridgeRelativeConstant_nonneg β j) j
  · intro n hn y
    exact (forwardBridgeFactor_relative_derivative_bound β μ s hs n y).trans
      (mul_le_mul_of_nonneg_right (forwardBridgeExponentialConstant_le_relative β j n hn)
        (forwardBridgeFactor_pos β μ s hs y).le)
  · exact hj
  · exact le_rfl

lemma norm_forwardBridgeAction_deriv_le_one (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) :
    ‖deriv (forwardBridgeAction β μ s hs path) x‖ ≤ 1 := by
  unfold forwardBridgeAction
  rw [(hasDerivAt_forwardBridgeJet β μ s hs 0 path x).deriv]
  have hbound : ∀ᵐ t : Overlap ∂(μ : Measure Overlap),
      ‖if (t : ℝ) ≤ s then forwardBridgeFraction s t ^ 1 *
        parisiSpatialField β μ 1 (t, forwardBridgePoint β s hs path x t) else 0‖ ≤ 1 :=
    Filter.Eventually.of_forall fun t => by
      split_ifs
      · have he : parisiSpatialField β μ 1 = parisiGradient β μ := by
          funext p
          simp only [parisiSpatialField, bcfSpatialDerivative, iteratedDeriv_zero,
            parisiGradient, bcfTranslate_zero]
        rw [he, pow_one, norm_mul, Real.norm_of_nonneg (forwardBridgeFraction_mem s hs.1 t).1]
        exact (mul_le_mul (forwardBridgeFraction_mem s hs.1 t).2
          (norm_parisiGradient_le_one β μ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
      · simp
  exact (norm_integral_le_of_norm_le_const hbound).trans_eq (by simp)

lemma forwardBridgeFactor_first_relative_bound (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    ‖deriv (forwardBridgeFactor β μ s hs) x‖ ≤ forwardBridgeFactor β μ s hs x := by
  have hpoint (path : ForwardBridgePath) :
      ‖iteratedDeriv 1 (forwardBridgePathFactor β μ s hs path) x‖ ≤
        forwardBridgePathFactor β μ s hs path x := by
    have hh := ((contDiff_forwardBridgeAction β μ s hs path).differentiable
      (by simp) x).hasDerivAt.neg.exp
    have he : (fun y => Real.exp (-forwardBridgeAction β μ s hs path y)) =
        forwardBridgePathFactor β μ s hs path := rfl
    simp only [Pi.neg_apply] at hh
    rw [he] at hh
    rw [iteratedDeriv_one, hh.deriv, norm_mul, norm_neg,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    exact (mul_le_mul_of_nonneg_left (norm_forwardBridgeAction_deriv_le_one β μ s hs path x)
      (forwardBridgePathFactor_pos β μ s hs path x).le).trans_eq (mul_one _)
  have hi : Integrable (fun path => iteratedDeriv 1 (forwardBridgePathFactor β μ s hs path) x)
      canonicalWienerMeasure := (integrable_forwardBridgePathFactor β μ s hs x).mono'
    (((continuous_iteratedDeriv_forwardBridgePathFactor β μ s hs 1).comp
      (show Continuous (fun path : ForwardBridgePath => (path, x)) by fun_prop)).aestronglyMeasurable)
    (Filter.Eventually.of_forall hpoint)
  rw [← iteratedDeriv_one, iteratedDeriv_forwardBridgeFactor]
  exact (norm_integral_le_integral_norm _).trans
    (integral_mono hi.norm (integrable_forwardBridgePathFactor β μ s hs x) hpoint)

/-- The sharp unit slope bound. -/
theorem forwardBridgeCorrection_slope_bound (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    ‖deriv (forwardBridgeCorrection β μ s hs) x‖ ≤ 1 := by
  have h := ((contDiff_forwardBridgeFactor β μ s hs).differentiable (by simp) x).hasDerivAt.log
    (forwardBridgeFactor_pos β μ s hs x).ne' |>.neg
  have he : (-fun y => Real.log (forwardBridgeFactor β μ s hs y)) =
      forwardBridgeCorrection β μ s hs := rfl
  rw [he] at h
  rw [h.deriv, norm_neg, norm_div, Real.norm_of_nonneg (forwardBridgeFactor_pos β μ s hs x).le]
  exact (div_le_one (forwardBridgeFactor_pos β μ s hs x)).mpr
    (forwardBridgeFactor_first_relative_bound β μ s hs x)

def forwardBridgeDensity (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) : ℝ :=
  heatDensity (β ^ 2 * s) x * Real.exp (parisiCDF μ s * parisiPotential β μ (s, x)) *
    forwardBridgeFactor β μ s hs x

theorem forwardBridgeDensity_pos (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) : 0 < forwardBridgeDensity β μ s hs x :=
  mul_pos (mul_pos (heatDensity_pos (mul_pos (sq_pos_of_ne_zero hβ) hs.1) x)
    (Real.exp_pos _)) (forwardBridgeFactor_pos β μ s hs x)

theorem contDiff_forwardBridgeDensity (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) : ContDiff ℝ ∞ (forwardBridgeDensity β μ s hs) := by
  have hg : ContDiff ℝ ∞ (heatDensity (β ^ 2 * s)) := by
    unfold heatDensity
    fun_prop
  exact (hg.mul ((contDiff_const.mul
    (contDiff_parisiPotential_spatial β μ s ⟨hs.1.le, hs.2⟩)).exp)).mul
      (contDiff_forwardBridgeFactor β μ s hs)

theorem forwardBridgeDensity_gaussian_envelope (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    forwardBridgeDensity β μ s hs x ≤ Real.exp (β ^ 2 + |x|) * heatDensity (β ^ 2 * s) x := by
  have hu := parisiPotential_absolute_growth β μ s x ⟨hs.1.le, hs.2⟩
  have he : Real.exp (parisiCDF μ s * parisiPotential β μ (s, x)) ≤ Real.exp (β ^ 2 + |x|) := by
    apply Real.exp_le_exp.mpr
    exact (mul_le_of_le_one_left (parisiPotential_nonneg β μ s x hs.2)
      (parisiCDF_le_one μ s)).trans ((le_abs_self _).trans hu)
  unfold forwardBridgeDensity
  have hg : 0 ≤ heatDensity (β ^ 2 * s) x := by unfold heatDensity; positivity
  calc
    _ ≤ heatDensity (β ^ 2 * s) x * Real.exp (parisiCDF μ s * parisiPotential β μ (s, x)) * 1 :=
      mul_le_mul_of_nonneg_left (forwardBridgeFactor_le_one β μ s hs x) (mul_nonneg hg (Real.exp_pos _).le)
    _ ≤ _ := by simpa only [mul_one, one_mul, mul_comm] using mul_le_mul_of_nonneg_left he hg

end FRSB
