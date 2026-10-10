module

public import FRSB.ForwardBridgeJetContinuity
public import FRSB.ForwardJetLimits
public import FRSB.CompactLocalConvergence

@[expose] public section


/-! Weak-measure convergence of every spatial density jet and local uniform
convergence of the logarithmic correction away from CDF discontinuities. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped ContDiff Topology BigOperators
namespace FRSB

def forwardBridgeExponential (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) : ℝ :=
  Real.exp (forwardBridgeExponent β μ s hs path x)

def forwardBridgeExponentialMean (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) : ℝ :=
  ∫ path, forwardBridgeExponential β μ s hs path x ∂canonicalWienerMeasure

def forwardBridgeExponentDerivativeConstant (β : ℝ) (j : ℕ) : ℝ :=
  2 * uniformSpatialConstant β (j - 1)

def forwardBridgeExponentialJetConstant (β : ℝ) (j : ℕ) : ℝ :=
  exponentialDerivativeConstant (forwardBridgeExponentDerivativeConstant β) j

theorem forwardBridgeExponentialJetConstant_nonneg (β : ℝ) (j : ℕ) :
    0 ≤ forwardBridgeExponentialJetConstant β j :=
  exponentialDerivativeConstant_nonneg _
    (fun n => mul_nonneg (by norm_num) (uniformSpatialConstant_pos β _).le) j

theorem forwardBridgeExponential_eq_product (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) :
    forwardBridgeExponential β μ s hs path x =
      Real.exp (parisiCDF μ s * parisiPotential β μ (s, x)) *
        forwardBridgePathFactor β μ s hs path x := by
  unfold forwardBridgeExponential
  rw [forwardBridgeExponent_eq, sub_eq_add_neg, Real.exp_add]
  rfl

theorem forwardBridgeExponentialMean_eq_product (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    forwardBridgeExponentialMean β μ s hs x =
      Real.exp (parisiCDF μ s * parisiPotential β μ (s, x)) *
        forwardBridgeFactor β μ s hs x := by
  unfold forwardBridgeExponentialMean
  simp_rw [forwardBridgeExponential_eq_product]
  rw [integral_const_mul]
  rfl

theorem contDiff_forwardBridgeExponentialMean (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) : ContDiff ℝ ∞ (forwardBridgeExponentialMean β μ s hs) := by
  have he : forwardBridgeExponentialMean β μ s hs = fun x =>
      Real.exp (parisiCDF μ s * parisiPotential β μ (s, x)) * forwardBridgeFactor β μ s hs x :=
    funext (forwardBridgeExponentialMean_eq_product β μ s hs)
  rw [he]
  exact ((contDiff_const.mul (contDiff_parisiPotential_spatial β μ s ⟨hs.1.le, hs.2⟩)).exp).mul
    (contDiff_forwardBridgeFactor β μ s hs)

theorem continuous_forwardBridgeExponentJet_path (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (x : ℝ) :
    Continuous (fun path => forwardBridgeExponentJet β μ s hs j path x) := by
  have he : (fun path => forwardBridgeExponentJet β μ s hs j path x) =
      fun path => parisiCDF μ s * parisiSpatialField β μ j (s, x) -
        forwardBridgeJet β μ s hs j path x := funext (fun path => forwardBridgeExponentJet_eq β μ s hs j path x)
  rw [he]
  exact continuous_const.sub ((continuous_forwardBridgeJet β μ s hs j).comp
    (show Continuous (fun path : ForwardBridgePath => (path, x)) by fun_prop))

theorem continuous_iteratedDeriv_forwardBridgeExponential_path
    (β : ℝ) (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (x : ℝ) :
    Continuous (fun path => iteratedDeriv j (forwardBridgeExponential β μ s hs path) x) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero => exact Real.continuous_exp.comp (continuous_forwardBridgeExponent β μ s hs x)
    | succ n =>
      change Continuous (fun path => iteratedDeriv (n+1)
        (fun y => Real.exp (forwardBridgeExponent β μ s hs path y)) x)
      simp_rw [iteratedDeriv_exp_formula _
        (contDiff_forwardBridgeExponent β μ s hs _), iteratedDeriv_forwardBridgeExponent]
      apply continuous_finsetSum
      intro i hi
      exact (continuous_const.mul (continuous_forwardBridgeExponentJet_path β μ s hs (i+1) x)).mul
        (ih (n-i) (by omega))

theorem norm_iteratedDeriv_forwardBridgeExponential_le
    (β : ℝ) (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (j : ℕ) (path : ForwardBridgePath) (x : ℝ) :
    ‖iteratedDeriv j (forwardBridgeExponential β μ s hs path) x‖ ≤
      forwardBridgeExponentialJetConstant β j * Real.exp (β ^ 2 + |x|) := by
  have hK : ∀ n, 0 ≤ forwardBridgeExponentDerivativeConstant β n :=
    fun n => mul_nonneg (by norm_num) (uniformSpatialConstant_pos β _).le
  have h := norm_iteratedDeriv_exp_neg_mul_le
    (fun y => -forwardBridgeExponent β μ s hs path y) 1
    (contDiff_forwardBridgeExponent β μ s hs path).neg (by norm_num) _ hK
    (fun n y => by
      change ‖iteratedDeriv (n+1) (-forwardBridgeExponent β μ s hs path) y‖ ≤ _
      rw [iteratedDeriv_neg, norm_neg, iteratedDeriv_forwardBridgeExponent]
      simpa only [forwardBridgeExponentDerivativeConstant, Nat.add_sub_cancel] using
        norm_forwardBridgeExponentJet_succ_le β μ s hs n path y) j x
  simp only [neg_mul, one_mul, neg_neg] at h
  exact h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (forwardBridgeExponent_upper_bound β μ s hs path x))
      (exponentialDerivativeConstant_nonneg _ hK j))

theorem integrable_iteratedDeriv_forwardBridgeExponential (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (x : ℝ) :
    Integrable (fun path => iteratedDeriv j (forwardBridgeExponential β μ s hs path) x)
      canonicalWienerMeasure :=
  (integrable_const (forwardBridgeExponentialJetConstant β j * Real.exp (β ^ 2 + |x|))).mono'
    (continuous_iteratedDeriv_forwardBridgeExponential_path β μ s hs j x).aestronglyMeasurable
    (.of_forall fun path => norm_iteratedDeriv_forwardBridgeExponential_le β μ s hs j path x)

theorem integrable_iteratedDeriv_forwardBridgePathFactor (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (x : ℝ) :
    Integrable (fun path => iteratedDeriv j (forwardBridgePathFactor β μ s hs path) x)
      canonicalWienerMeasure :=
  (integrable_const (forwardBridgeExponentialConstant β j)).mono'
    (((continuous_iteratedDeriv_forwardBridgePathFactor β μ s hs j).comp
      (show Continuous (fun path : ForwardBridgePath => (path, x)) by fun_prop)).aestronglyMeasurable)
    (.of_forall fun path => (norm_iteratedDeriv_forwardBridgePathFactor_le β μ s hs j path x).trans
      (mul_le_of_le_one_right (forwardBridgeExponentialConstant_nonneg β j)
        (forwardBridgePathFactor_le_one β μ s hs path x)))

/-- The outer spatial derivatives are genuine integral derivatives. This
 follows by the finite Leibniz formula and the already proved differentiation
 under the bounded bridge-factor expectation. -/
theorem iteratedDeriv_forwardBridgeExponentialMean (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (x : ℝ) :
    iteratedDeriv j (forwardBridgeExponentialMean β μ s hs) x =
      ∫ path, iteratedDeriv j (forwardBridgeExponential β μ s hs path) x ∂canonicalWienerMeasure := by
  let G : ℝ → ℝ := fun y => Real.exp (parisiCDF μ s * parisiPotential β μ (s, y))
  have hG : ContDiff ℝ ∞ G :=
    (contDiff_const.mul (contDiff_parisiPotential_spatial β μ s ⟨hs.1.le, hs.2⟩)).exp
  have hm : forwardBridgeExponentialMean β μ s hs = G * forwardBridgeFactor β μ s hs :=
    funext (forwardBridgeExponentialMean_eq_product β μ s hs)
  have hp (path : ForwardBridgePath) : forwardBridgeExponential β μ s hs path =
      G * forwardBridgePathFactor β μ s hs path :=
    funext (forwardBridgeExponential_eq_product β μ s hs path)
  rw [hm, iteratedDeriv_mul (hG.of_le (by simp)).contDiffAt
    ((contDiff_forwardBridgeFactor β μ s hs).of_le (by simp)).contDiffAt]
  simp_rw [hp, iteratedDeriv_mul (hG.of_le (by simp)).contDiffAt
    ((contDiff_forwardBridgePathFactor β μ s hs _).of_le (by simp)).contDiffAt]
  rw [integral_finsetSum (Finset.range (j+1)) (fun i _ =>
    (integrable_iteratedDeriv_forwardBridgePathFactor β μ s hs (j-i) x).const_mul
      ((j.choose i : ℝ) * iteratedDeriv i G x))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, iteratedDeriv_forwardBridgeFactor]

theorem tendsto_iteratedDeriv_forwardBridgeExponentialMean_of_weak
    {A : Type*} {l : Filter A} [l.IsCountablyGenerated] (β : ℝ) (μ : ParisiMeasure)
    (ν : A → ParisiMeasure) (hν : Tendsto ν l (𝓝 μ)) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (x : ℝ) :
    Tendsto (fun a => iteratedDeriv j (forwardBridgeExponentialMean β (ν a) s hs) x) l
      (𝓝 (iteratedDeriv j (forwardBridgeExponentialMean β μ s hs) x)) := by
  simp_rw [iteratedDeriv_forwardBridgeExponentialMean]
  apply tendsto_integral_filter_of_dominated_convergence
    (fun _ => forwardBridgeExponentialJetConstant β j * Real.exp (β ^ 2 + |x|))
  · exact .of_forall fun a =>
      (continuous_iteratedDeriv_forwardBridgeExponential_path β (ν a) s hs j x).aestronglyMeasurable
  · exact .of_forall fun a => .of_forall fun path =>
      norm_iteratedDeriv_forwardBridgeExponential_le β (ν a) s hs j path x
  · exact integrable_const _
  · exact .of_forall fun path => tendsto_iteratedDeriv_exp_of_jets
      (fun a => forwardBridgeExponent β (ν a) s hs path) (forwardBridgeExponent β μ s hs path)
      (fun a => contDiff_forwardBridgeExponent β (ν a) s hs path)
      (contDiff_forwardBridgeExponent β μ s hs path) x
      (fun i => by
        simp_rw [iteratedDeriv_forwardBridgeExponent]
        exact tendsto_forwardBridgeExponentJet_of_weak β μ ν hν s hs i path x) j

/-- Every density jet converges even when the approximation moves atoms
 through the observation time. The endpoint-vanishing exponent cancels the
 apparent CDF jump. -/
theorem tendsto_iteratedDeriv_forwardBridgeDensity_of_weak
    {A : Type*} {l : Filter A} [l.IsCountablyGenerated] (β : ℝ) (μ : ParisiMeasure)
    (ν : A → ParisiMeasure) (hν : Tendsto ν l (𝓝 μ)) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (x : ℝ) :
    Tendsto (fun a => iteratedDeriv j (forwardBridgeDensity β (ν a) s hs) x) l
      (𝓝 (iteratedDeriv j (forwardBridgeDensity β μ s hs) x)) := by
  have he (η : ParisiMeasure) : forwardBridgeDensity β η s hs =
      fun y => heatDensity (β ^ 2 * s) y * forwardBridgeExponentialMean β η s hs y := by
    funext y
    exact forwardBridgeDensity_eq_exponent β η s hs y
  simp_rw [he]
  apply tendsto_iteratedDeriv_mul_of_jets
    (fun _ => heatDensity (β ^ 2 * s)) (fun a => forwardBridgeExponentialMean β (ν a) s hs)
    (heatDensity (β ^ 2 * s)) (forwardBridgeExponentialMean β μ s hs)
  · intro a; unfold heatDensity; fun_prop
  · exact fun a => contDiff_forwardBridgeExponentialMean β (ν a) s hs
  · unfold heatDensity; fun_prop
  · exact contDiff_forwardBridgeExponentialMean β μ s hs
  · intro i; exact tendsto_const_nhds
  · exact fun i => tendsto_iteratedDeriv_forwardBridgeExponentialMean_of_weak β μ ν hν s hs i x

theorem tendsto_parisiSpatialField_at_of_weak
    {A : Type*} {l : Filter A} [l.IsCountablyGenerated] (β : ℝ) (μ : ParisiMeasure)
    (ν : A → ParisiMeasure) (hν : Tendsto ν l (𝓝 μ)) (j : ℕ)
    (s x : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun a => parisiSpatialField β (ν a) j (s, x)) l
      (𝓝 (parisiSpatialField β μ j (s, x))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun a => parisiSpatialField_measure_error_bound β (ν a) μ j s x hs)
    (tendsto_parisiSpatialMeasureError_of_weak β μ ν hν j)

theorem tendsto_forwardBridgeJet_of_weak_cdf
    {A : Type*} {l : Filter A} [l.IsCountablyGenerated] (β : ℝ) (μ : ParisiMeasure)
    (ν : A → ParisiMeasure) (hν : Tendsto ν l (𝓝 μ)) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1)
    (hα : Tendsto (fun a => parisiCDF (ν a) s) l (𝓝 (parisiCDF μ s)))
    (j : ℕ) (path : ForwardBridgePath) (x : ℝ) :
    Tendsto (fun a => forwardBridgeJet β (ν a) s hs j path x) l
      (𝓝 (forwardBridgeJet β μ s hs j path x)) := by
  have he (η : ParisiMeasure) : forwardBridgeJet β η s hs j path x =
      parisiCDF η s * parisiSpatialField β η j (s, x) -
        forwardBridgeExponentJet β η s hs j path x := by
    have hh := forwardBridgeExponentJet_eq β η s hs j path x
    linarith
  simp_rw [he]
  exact (hα.mul (tendsto_parisiSpatialField_at_of_weak β μ ν hν j s x ⟨hs.1.le, hs.2⟩)).sub
    (tendsto_forwardBridgeExponentJet_of_weak β μ ν hν s hs j path x)

theorem tendsto_iteratedDeriv_forwardBridgeFactor_of_weak_cdf
    {A : Type*} {l : Filter A} [l.IsCountablyGenerated] (β : ℝ) (μ : ParisiMeasure)
    (ν : A → ParisiMeasure) (hν : Tendsto ν l (𝓝 μ)) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1)
    (hα : Tendsto (fun a => parisiCDF (ν a) s) l (𝓝 (parisiCDF μ s))) (j : ℕ) (x : ℝ) :
    Tendsto (fun a => iteratedDeriv j (forwardBridgeFactor β (ν a) s hs) x) l
      (𝓝 (iteratedDeriv j (forwardBridgeFactor β μ s hs) x)) := by
  simp_rw [iteratedDeriv_forwardBridgeFactor]
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => forwardBridgeExponentialConstant β j)
  · exact .of_forall fun a => ((continuous_iteratedDeriv_forwardBridgePathFactor β (ν a) s hs j).comp
      (show Continuous (fun path : ForwardBridgePath => (path, x)) by fun_prop)).aestronglyMeasurable
  · exact .of_forall fun a => .of_forall fun path =>
      (norm_iteratedDeriv_forwardBridgePathFactor_le β (ν a) s hs j path x).trans
        (mul_le_of_le_one_right (forwardBridgeExponentialConstant_nonneg β j)
          (forwardBridgePathFactor_le_one β (ν a) s hs path x))
  · exact integrable_const _
  · refine .of_forall fun path => ?_
    apply tendsto_iteratedDeriv_exp_of_jets
      (fun a => -forwardBridgeAction β (ν a) s hs path) (-forwardBridgeAction β μ s hs path)
      (fun a => (contDiff_forwardBridgeAction β (ν a) s hs path).neg)
      (contDiff_forwardBridgeAction β μ s hs path).neg x
    intro i
    simp_rw [iteratedDeriv_neg, iteratedDeriv_forwardBridgeAction]
    exact (tendsto_forwardBridgeJet_of_weak_cdf β μ ν hν s hs hα i path x).neg

theorem tendsto_iteratedDeriv_forwardBridgeCorrection_of_weak_cdf
    {A : Type*} {l : Filter A} [l.IsCountablyGenerated] (β : ℝ) (μ : ParisiMeasure)
    (ν : A → ParisiMeasure) (hν : Tendsto ν l (𝓝 μ)) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1)
    (hα : Tendsto (fun a => parisiCDF (ν a) s) l (𝓝 (parisiCDF μ s))) (j : ℕ) (x : ℝ) :
    Tendsto (fun a => iteratedDeriv j (forwardBridgeCorrection β (ν a) s hs) x) l
      (𝓝 (iteratedDeriv j (forwardBridgeCorrection β μ s hs) x)) := by
  apply tendsto_iteratedDeriv_negativeLog_of_jets
    (fun a => forwardBridgeFactor β (ν a) s hs) (forwardBridgeFactor β μ s hs)
    (fun a => contDiff_forwardBridgeFactor β (ν a) s hs) (contDiff_forwardBridgeFactor β μ s hs)
    (fun a => forwardBridgeFactor_pos β (ν a) s hs) (forwardBridgeFactor_pos β μ s hs) x
  exact fun i => tendsto_iteratedDeriv_forwardBridgeFactor_of_weak_cdf β μ ν hν s hs hα i x

/-- The exact local-uniform all-orders convergence of W. CDF convergence
 at the observation time is explicitly required, as atoms may move through
 that time under weak convergence alone. -/
theorem tendstoUniformlyOn_iteratedDeriv_forwardBridgeCorrection_of_weak_cdf
    {A : Type*} {l : Filter A} [l.IsCountablyGenerated] (β : ℝ) (μ : ParisiMeasure)
    (ν : A → ParisiMeasure) (hν : Tendsto ν l (𝓝 μ)) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1)
    (hα : Tendsto (fun a => parisiCDF (ν a) s) l (𝓝 (parisiCDF μ s)))
    (j : ℕ) (S : Set ℝ) (hS : IsCompact S) :
    TendstoUniformlyOn (fun a => iteratedDeriv j (forwardBridgeCorrection β (ν a) s hs))
      (iteratedDeriv j (forwardBridgeCorrection β μ s hs)) l S := by
  apply tendstoUniformlyOn_of_common_derivative_bound _ _ S hS
    (Real.nnabs (negativeLogDerivativeConstant (forwardBridgeRelativeConstant β (j+1)) (j+1)))
  · intro a
    exact (contDiff_forwardBridgeCorrection β (ν a) s hs).differentiable_iteratedDeriv j
      (by exact_mod_cast ENat.natCast_lt_top j)
  · intro a x
    rw [← iteratedDeriv_succ]
    simpa only [Real.coe_nnabs] using
      (forwardBridgeCorrection_uniform_derivative_bound β (ν a) s hs (j+1) (by omega) x).trans
        (le_abs_self _)
  · exact fun x _ => tendsto_iteratedDeriv_forwardBridgeCorrection_of_weak_cdf β μ ν hν s hs hα j x

theorem norm_iteratedDeriv_forwardBridgeExponentialMean_le (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (x : ℝ) :
    ‖iteratedDeriv j (forwardBridgeExponentialMean β μ s hs) x‖ ≤
      forwardBridgeExponentialJetConstant β j * Real.exp (β ^ 2 + |x|) := by
  rw [iteratedDeriv_forwardBridgeExponentialMean]
  exact (norm_integral_le_of_norm_le_const (.of_forall fun path =>
    norm_iteratedDeriv_forwardBridgeExponential_le β μ s hs j path x)).trans_eq (by simp)

def forwardBridgeDensityJetEnvelope (β s : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (j+1), (j.choose i : ℝ) * ‖iteratedDeriv i (heatDensity (β ^ 2 * s)) x‖ *
    (forwardBridgeExponentialJetConstant β (j-i) * Real.exp (β ^ 2 + |x|))

theorem continuous_forwardBridgeDensityJetEnvelope (β s : ℝ) (j : ℕ) :
    Continuous (forwardBridgeDensityJetEnvelope β s j) := by
  have hh : ContDiff ℝ ∞ (heatDensity (β ^ 2 * s)) := by unfold heatDensity; fun_prop
  unfold forwardBridgeDensityJetEnvelope
  apply continuous_finsetSum
  intro i _
  exact (continuous_const.mul ((hh.continuous_iteratedDeriv i (by simp)).norm)).mul
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.add continuous_abs)))

theorem norm_iteratedDeriv_forwardBridgeDensity_le_envelope (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (x : ℝ) :
    ‖iteratedDeriv j (forwardBridgeDensity β μ s hs) x‖ ≤ forwardBridgeDensityJetEnvelope β s j x := by
  have hh : ContDiff ℝ ∞ (heatDensity (β ^ 2 * s)) := by unfold heatDensity; fun_prop
  have he : forwardBridgeDensity β μ s hs =
      heatDensity (β ^ 2 * s) * forwardBridgeExponentialMean β μ s hs := by
    funext y
    exact forwardBridgeDensity_eq_exponent β μ s hs y
  rw [he, iteratedDeriv_mul (hh.of_le (by simp)).contDiffAt
    ((contDiff_forwardBridgeExponentialMean β μ s hs).of_le (by simp)).contDiffAt]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  simp only [norm_mul, Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact mul_le_mul_of_nonneg_left (norm_iteratedDeriv_forwardBridgeExponentialMean_le β μ s hs (j-i) x)
    (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))

/-- Genuine all-orders local uniform density convergence at every positive
 physical time, with no CDF-at-that-time premise. -/
theorem tendstoUniformlyOn_iteratedDeriv_forwardBridgeDensity_of_weak
    {A : Type*} {l : Filter A} [l.IsCountablyGenerated] (β : ℝ) (μ : ParisiMeasure)
    (ν : A → ParisiMeasure) (hν : Tendsto ν l (𝓝 μ)) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (S : Set ℝ) (hS : IsCompact S) :
    TendstoUniformlyOn (fun a => iteratedDeriv j (forwardBridgeDensity β (ν a) s hs))
      (iteratedDeriv j (forwardBridgeDensity β μ s hs)) l S := by
  apply tendstoUniformlyOn_of_common_continuous_derivative_bound _ _
    (forwardBridgeDensityJetEnvelope β s (j+1)) (continuous_forwardBridgeDensityJetEnvelope β s (j+1)) S hS
  · intro a
    exact (contDiff_forwardBridgeDensity β (ν a) s hs).differentiable_iteratedDeriv j
      (by exact_mod_cast ENat.natCast_lt_top j)
  · intro a x
    rw [← iteratedDeriv_succ]
    exact norm_iteratedDeriv_forwardBridgeDensity_le_envelope β (ν a) s hs (j+1) x
  · exact fun x _ => tendsto_iteratedDeriv_forwardBridgeDensity_of_weak β μ ν hν s hs j x

end FRSB
