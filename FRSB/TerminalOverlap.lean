module

public import FRSB.SupportGeometry
public import FRSB.ConstantMassEvolution
public import Paper.ParisiDiracIdentification
public import FRSB.OptimalCurvatureMoment

@[expose] public section


/-! The exact terminal log-cosh region for a probability law supported below q. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
open SpinGlass SpinGlass.Targets
namespace FRSB

theorem parisiCDF_eq_one_above_support (μ : ParisiMeasure) {q s : ℝ}
    (hmax : ∀ x ∈ parisiSupport μ, x ≤ q) (hs : q ≤ s) : parisiCDF μ s = 1 := by
  have heq : {r : Overlap | (r : ℝ) ≤ s} =ᵐ[(μ : Measure Overlap)] univ := by
    filter_upwards [(μ : Measure Overlap).support_mem_ae] with r hr
    apply propext
    exact ⟨fun _ => mem_univ _, fun _ => (hmax r ⟨r, hr, rfl⟩).trans hs⟩
  unfold parisiCDF
  rw [measure_congr heq, measure_univ, ENNReal.toReal_one]

theorem parisiPotential_terminal_region (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    {q t : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    (hmax : ∀ x ∈ parisiSupport μ, x ≤ q) (ht : t ∈ Icc q 1) (x : ℝ) :
    parisiPotential β μ (t,x) = Real.log (Real.cosh x) + β ^ 2 * (1-t) / 2 := by
  by_cases ht1 : t = 1
  · subst t
    simp only [parisiPotential_terminal, sub_self, mul_zero, zero_div, add_zero]
  have hlt : t < 1 := lt_of_le_of_ne ht.2 ht1
  have he := parisiPotential_exp_heat_on_constant_interval β hβ μ
    (hq.1.trans ht.1) hlt (le_refl 1) (by norm_num : (0 : ℝ) < 1)
    (fun s hs => parisiCDF_eq_one_above_support μ hmax (ht.1.trans hs.1))
    (show t ∈ Icc t 1 from ⟨le_rfl, ht.2⟩)
    (show (1 : ℝ) ∈ Icc t 1 from ⟨ht.2, le_rfl⟩) x
  simp only [one_mul, parisiPotential_terminal, Real.exp_log (Real.cosh_pos _)] at he
  have hheat : heatSemigroup (β ^ 2 * (1-t)) Real.cosh x =
      Real.cosh x * Real.exp (β ^ 2 * (1-t) / 2) := by
    unfold heatSemigroup gaussianExpectation
    rw [integral_cosh_add_mul_stdGaussian,
      Real.sq_sqrt (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr ht.2))]
  rw [hheat] at he
  have hlog := congrArg Real.log he
  rw [Real.log_exp, Real.log_mul (Real.cosh_pos x).ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
  exact hlog

theorem parisiGradient_terminal_region (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    {q t : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    (hmax : ∀ x ∈ parisiSupport μ, x ≤ q) (ht : t ∈ Icc q 1) (x : ℝ) :
    parisiGradient β μ (t,x) = Real.tanh x := by
  have he : (fun y => parisiPotential β μ (t,y)) =
      fun y => Real.log (Real.cosh y) + β^2*(1-t)/2 :=
    funext (parisiPotential_terminal_region β hβ μ hq hmax ht)
  have hd := hasDerivAt_parisiPotential_spatial_all β μ t x ⟨hq.1.trans ht.1, ht.2⟩
  rw [he] at hd
  exact hd.unique ((Paper.hasDerivAt_log_cosh x).add_const _)

theorem parisiHessian_terminal_region (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    {q t : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    (hmax : ∀ x ∈ parisiSupport μ, x ≤ q) (ht : t ∈ Icc q 1) (x : ℝ) :
    parisiHessian β μ (t,x) = sech x ^ 2 := by
  have he : (fun y => parisiGradient β μ (t,y)) = Real.tanh :=
    funext (parisiGradient_terminal_region β hβ μ hq hmax ht)
  have hd := hasDerivAt_parisiGradient_spatial_all β μ t x
  rw [he] at hd
  exact hd.unique (hasDerivAt_tanh x)

theorem parisiSpatialJet_three_terminal_region (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    {q t : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    (hmax : ∀ x ∈ parisiSupport μ, x ≤ q) (ht : t ∈ Icc q 1) (x : ℝ) :
    parisiSpatialJet β μ 3 t x = -2 * Real.tanh x * sech x ^ 2 := by
  have he : (fun y => parisiSpatialJet β μ 2 t y) = fun y => sech y ^ 2 := by
    funext y
    rw [parisiSpatialJet_two]
    exact parisiHessian_terminal_region β hβ μ hq hmax ht y
  have hd := hasDerivAt_parisiSpatialJet β μ 2 t x ⟨hq.1.trans ht.1, ht.2⟩
  rw [he] at hd
  exact hd.unique (hasDerivAt_sech_sq x)

end FRSB
