module

public import FourPapersCommon.WienerBrownianDriver

@[expose] public section

/-! The deterministic Wiener integral of the reconstructed Brownian driver
is the original Wiener integral after an independently constructed isometry
of deterministic kernels. Both operators are the dense-step extensions from
their Brownian coordinates; their equality is proved on that dense span. -/

noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus
open scoped InnerProductSpace NNReal ENNReal

namespace FourPapersCommon

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

def wienerKernelCombination (f : ℝ≥0 → Lp ℝ 2 nonnegativeLebesgueMeasure) :
    (ℝ≥0 →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 nonnegativeLebesgueMeasure :=
  Finsupp.linearCombination ℝ f

theorem inner_wienerKernelCombination
    (f : ℝ≥0 → Lp ℝ 2 nonnegativeLebesgueMeasure)
    (hGram : ∀ s t, ⟪f s, f t⟫_ℝ = (min s t : ℝ))
    (v w : ℝ≥0 →₀ ℝ) :
    ⟪wienerKernelCombination f v, wienerKernelCombination f w⟫_ℝ =
      ⟪stepToLp v, stepToLp w⟫_ℝ := by
  have he : stepToLp = Finsupp.linearCombination ℝ intervalIndicator := by
    apply Finsupp.lhom_ext
    intro t c
    rw [stepToLp_single, Finsupp.linearCombination_single]
  rw [he]
  unfold wienerKernelCombination
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, hGram, inner_intervalIndicator]

theorem norm_wienerKernelCombination
    (f : ℝ≥0 → Lp ℝ 2 nonnegativeLebesgueMeasure)
    (hGram : ∀ s t, ⟪f s, f t⟫_ℝ = (min s t : ℝ))
    (v : ℝ≥0 →₀ ℝ) :
    ‖wienerKernelCombination f v‖ = ‖stepToLp v‖ := by
  have h := inner_wienerKernelCombination f hGram v v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- The kernel isometry is determined by the Brownian Gram matrix and the
dense interval-indicator span, independently of any stochastic identity. -/
def wienerKernelTransport
    (f : ℝ≥0 → Lp ℝ 2 nonnegativeLebesgueMeasure)
    (hGram : ∀ s t, ⟪f s, f t⟫_ℝ = (min s t : ℝ)) :
    Lp ℝ 2 nonnegativeLebesgueMeasure →ₗᵢ[ℝ] Lp ℝ 2 nonnegativeLebesgueMeasure :=
  (wienerKernelCombination f).extendOfIsometry denseRange_stepToLp
    (norm_wienerKernelCombination f hGram)

theorem wienerKernelTransport_stepToLp
    (f : ℝ≥0 → Lp ℝ 2 nonnegativeLebesgueMeasure)
    (hGram : ∀ s t, ⟪f s, f t⟫_ℝ = (min s t : ℝ))
    (v : ℝ≥0 →₀ ℝ) :
    wienerKernelTransport f hGram (stepToLp v) = wienerKernelCombination f v :=
  LinearMap.extendOfIsometry_eq _ _ _ _

theorem wienerKernelTransport_intervalIndicator
    (f : ℝ≥0 → Lp ℝ 2 nonnegativeLebesgueMeasure)
    (hGram : ∀ s t, ⟪f s, f t⟫_ℝ = (min s t : ℝ)) (t : ℝ≥0) :
    wienerKernelTransport f hGram (intervalIndicator t) = f t := by
  have h := wienerKernelTransport_stepToLp f hGram (Finsupp.single t 1)
  simpa only [stepToLp_single, one_smul, wienerKernelCombination,
    Finsupp.linearCombination_single] using h

/-- Interval pairings and the exact norm determine a transported kernel.
This permits singular inverse-clock transformations to be identified without
assuming an inverse-clock density is bounded at the origin. -/
theorem wienerKernelTransport_eq_of_interval_pairings
    (f : ℝ≥0 → Lp ℝ 2 nonnegativeLebesgueMeasure)
    (hGram : ∀ s t, ⟪f s, f t⟫_ℝ = (min s t : ℝ))
    (g u : Lp ℝ 2 nonnegativeLebesgueMeasure)
    (hPair : ∀ t, ⟪f t, u⟫_ℝ = ⟪intervalIndicator t, g⟫_ℝ)
    (hNorm : ‖u‖ = ‖g‖) : wienerKernelTransport f hGram g = u := by
  have hp (k : Lp ℝ 2 nonnegativeLebesgueMeasure) :
      ⟪wienerKernelTransport f hGram k, u⟫_ℝ = ⟪k, g⟫_ℝ := by
    refine denseRange_stepToLp.induction_on k ?_ ?_
    · exact isClosed_eq ((wienerKernelTransport f hGram).continuous.inner continuous_const)
        (continuous_id.inner continuous_const)
    · intro v
      rw [wienerKernelTransport_stepToLp]
      have he : stepToLp = Finsupp.linearCombination ℝ intervalIndicator := by
        apply Finsupp.lhom_ext
        intro t c
        rw [stepToLp_single, Finsupp.linearCombination_single]
      rw [he]
      unfold wienerKernelCombination
      simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner,
        real_inner_smul_left, hPair]
  have hz : ‖wienerKernelTransport f hGram g - u‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, hp, real_inner_self_eq_norm_sq,
      (wienerKernelTransport f hGram).norm_map, hNorm]
    ring
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

/-- Equality of the genuine deterministic Wiener operators. -/
theorem wienerIntegral_wienerBrownianDriver
    (hB : IsPreBrownianReal B P)
    (f : ℝ≥0 → Lp ℝ 2 nonnegativeLebesgueMeasure)
    (hGram : ∀ s t, ⟪f s, f t⟫_ℝ = (min s t : ℝ))
    (k : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    wienerIntegral (isBrownianReal_wienerBrownianDriver hB f hGram).toIsPreBrownianReal k =
      wienerIntegral hB (wienerKernelTransport f hGram k) := by
  let hC := (isBrownianReal_wienerBrownianDriver hB f hGram).toIsPreBrownianReal
  have hcoord (t : ℝ≥0) : brownianLp hC t = wienerIntegral hB (f t) := by
    apply Lp.ext
    exact (coeFn_brownianLp hC t).trans (wienerBrownianDriver_ae_eq hB f hGram t)
  refine denseRange_stepToLp.induction_on k ?_ ?_
  · exact isClosed_eq (wienerIntegral hC).continuous
      ((wienerIntegral hB).continuous.comp (wienerKernelTransport f hGram).continuous)
  · intro v
    rw [wienerIntegral_stepToLp, wienerKernelTransport_stepToLp]
    have he : stepToRandom hC = Finsupp.linearCombination ℝ (brownianLp hC) := by
      apply Finsupp.lhom_ext
      intro t c
      rw [stepToRandom_single, Finsupp.linearCombination_single]
    rw [he]
    unfold wienerKernelCombination
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, hcoord]

/-- Extend a kernel family on the closed physical unit interval by untouched
original Brownian increments after normalized time one. -/
def unitWienerKernelExtension
    (f : Set.Icc (0 : ℝ) 1 → Lp ℝ 2 nonnegativeLebesgueMeasure)
    (t : ℝ≥0) : Lp ℝ 2 nonnegativeLebesgueMeasure :=
  if ht : t ≤ 1 then f ⟨t, t.coe_nonneg, NNReal.coe_le_coe.mpr ht⟩
  else f ⟨1, by norm_num⟩ + (intervalIndicator t - intervalIndicator 1)

theorem unitWienerKernelExtension_unit
    (f : Set.Icc (0 : ℝ) 1 → Lp ℝ 2 nonnegativeLebesgueMeasure)
    (q : Set.Icc (0 : ℝ) 1) :
    unitWienerKernelExtension f q.val.toNNReal = f q := by
  have hq : q.val.toNNReal ≤ 1 := by
    exact_mod_cast (Real.coe_toNNReal _ q.property.1).trans_le q.property.2
  rw [unitWienerKernelExtension, dite_eq_left hq]
  congr 1
  apply Subtype.ext
  exact Real.coe_toNNReal _ q.property.1

theorem inner_unitWienerKernelExtension
    (f : Set.Icc (0 : ℝ) 1 → Lp ℝ 2 nonnegativeLebesgueMeasure)
    (hGram : ∀ s t, ⟪f s, f t⟫_ℝ = min (s : ℝ) (t : ℝ))
    (hTail : ∀ q t, 1 ≤ t → ⟪f q, intervalIndicator t - intervalIndicator 1⟫_ℝ = 0)
    (s t : ℝ≥0) :
    ⟪unitWienerKernelExtension f s, unitWienerKernelExtension f t⟫_ℝ =
      (min s t : ℝ) := by
  have htail (a b : ℝ≥0) (ha : 1 ≤ a) (hb : 1 ≤ b) :
      ⟪intervalIndicator a - intervalIndicator 1,
        intervalIndicator b - intervalIndicator 1⟫_ℝ = (min a b : ℝ) - 1 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right,
      inner_intervalIndicator, inner_intervalIndicator, inner_intervalIndicator,
      inner_intervalIndicator]
    have har : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    have hbr : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    simp only [NNReal.coe_one, min_eq_right har, min_eq_left hbr, min_self]
    ring
  have hTailRev (q : Set.Icc (0 : ℝ) 1) (a : ℝ≥0) (ha : 1 ≤ a) :
      ⟪intervalIndicator a - intervalIndicator 1, f q⟫_ℝ = 0 := by
    rw [real_inner_comm (f q), hTail _ _ ha]
  by_cases hs : s ≤ 1 <;> by_cases ht : t ≤ 1
  · simp only [unitWienerKernelExtension, dite_eq_left hs, dite_eq_left ht]
    exact hGram _ _
  · simp only [unitWienerKernelExtension, dite_eq_left hs, dite_eq_right ht]
    rw [inner_add_right, hGram, hTail _ _ (le_of_not_ge ht), add_zero]
    change min (s : ℝ) 1 = min (s : ℝ) (t : ℝ)
    have hsr : (s : ℝ) ≤ 1 := by exact_mod_cast hs
    have htr : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast le_of_not_ge ht
    rw [min_eq_left hsr, min_eq_left (hsr.trans htr)]
  · simp only [unitWienerKernelExtension, dite_eq_right hs, dite_eq_left ht]
    rw [inner_add_left, hGram,
      hTailRev _ _ (le_of_not_ge hs), add_zero]
    change min 1 (t : ℝ) = min (s : ℝ) (t : ℝ)
    have htr : (t : ℝ) ≤ 1 := by exact_mod_cast ht
    have hsr : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast le_of_not_ge hs
    rw [min_eq_right htr, min_eq_right (htr.trans hsr)]
  · simp only [unitWienerKernelExtension, dite_eq_right hs, dite_eq_right ht]
    rw [inner_add_left, inner_add_right, inner_add_right, hGram,
      hTail _ _ (le_of_not_ge ht),
      hTailRev _ _ (le_of_not_ge hs), htail s t (le_of_not_ge hs) (le_of_not_ge ht)]
    simp

end FourPapersCommon
