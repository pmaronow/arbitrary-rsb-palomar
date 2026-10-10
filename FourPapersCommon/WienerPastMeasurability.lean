module

public import FourPapersCommon.WienerBrownianDriver
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
public import Mathlib.Probability.Process.Adapted

@[expose] public section

/-! Supported deterministic Wiener kernels are measurable in the original
Brownian natural past, at the almost-everywhere level appropriate for L²
and for a continuous modification. The initial time is included. -/

noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Filter
open scoped Topology NNReal ENNReal InnerProductSpace

namespace FourPapersCommon

abbrev WienerKernelL2 := Lp ℝ 2 nonnegativeLebesgueMeasure

/-- Cut off a deterministic kernel after the specified original Brownian time. -/
def wienerKernelPast (a : ℝ≥0) (f : WienerKernelL2) : WienerKernelL2 :=
  ((Lp.memLp f).indicator measurableSet_Iic).toLp ((Set.Iic a).indicator (f : ℝ≥0 → ℝ))

theorem wienerKernelPast_coeFn (a : ℝ≥0) (f : WienerKernelL2) :
    (wienerKernelPast a f : ℝ≥0 → ℝ) =ᵐ[nonnegativeLebesgueMeasure]
      (Set.Iic a).indicator (f : ℝ≥0 → ℝ) :=
  MemLp.coeFn_toLp _

theorem wienerKernelPast_add (a : ℝ≥0) (f g : WienerKernelL2) :
    wienerKernelPast a (f + g) = wienerKernelPast a f + wienerKernelPast a g := by
  apply Lp.ext
  filter_upwards [wienerKernelPast_coeFn a (f + g), wienerKernelPast_coeFn a f,
    wienerKernelPast_coeFn a g, Lp.coeFn_add f g,
    Lp.coeFn_add (wienerKernelPast a f) (wienerKernelPast a g)] with t hfg hf hg ha hb
  rw [hfg, hb]
  change (Set.Iic a).indicator ((f + g : WienerKernelL2) : ℝ≥0 → ℝ) t =
    wienerKernelPast a f t + wienerKernelPast a g t
  rw [hf, hg]
  by_cases ht : t ∈ Set.Iic a
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, Set.indicator_of_mem ht, ha]
    rfl
  · simp only [Set.indicator_of_notMem ht, zero_add]

theorem wienerKernelPast_smul (a : ℝ≥0) (c : ℝ) (f : WienerKernelL2) :
    wienerKernelPast a (c • f) = c • wienerKernelPast a f := by
  apply Lp.ext
  filter_upwards [wienerKernelPast_coeFn a (c • f), wienerKernelPast_coeFn a f,
    Lp.coeFn_smul c f, Lp.coeFn_smul c (wienerKernelPast a f)] with t hcf hf ha hb
  by_cases ht : t ∈ Set.Iic a <;> simp [hcf, hf, hb, ht, ha]

theorem norm_wienerKernelPast_le (a : ℝ≥0) (f : WienerKernelL2) :
    ‖wienerKernelPast a f‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (wienerKernelPast_coeFn a f)]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_indicator_le _ measurableSet_Iic)

/-- Deterministic past truncation is a continuous contraction on L². -/
def wienerKernelPastCLM (a : ℝ≥0) : WienerKernelL2 →L[ℝ] WienerKernelL2 :=
  LinearMap.mkContinuous
    { toFun := wienerKernelPast a
      map_add' := wienerKernelPast_add a
      map_smul' := wienerKernelPast_smul a }
    1 (fun f => by simpa using norm_wienerKernelPast_le a f)

theorem wienerKernelPast_intervalIndicator (a t : ℝ≥0) :
    wienerKernelPast a (intervalIndicator t) = intervalIndicator (min t a) := by
  apply Lp.ext
  filter_upwards [wienerKernelPast_coeFn a (intervalIndicator t),
    (show (intervalIndicator t : ℝ≥0 → ℝ) =ᵐ[nonnegativeLebesgueMeasure]
      (Set.Ioc 0 t).indicator (fun _ => (1 : ℝ)) from indicatorConstLp_coeFn),
    (show (intervalIndicator (min t a) : ℝ≥0 → ℝ) =ᵐ[nonnegativeLebesgueMeasure]
      (Set.Ioc 0 (min t a)).indicator (fun _ => (1 : ℝ)) from indicatorConstLp_coeFn)]
      with u hcut ht hmin
  rw [hcut, hmin]
  by_cases hua : u ≤ a <;> by_cases hut : u ∈ Set.Ioc (0 : ℝ≥0) t
  · have hum : u ∈ Set.Ioc (0 : ℝ≥0) (min t a) := ⟨hut.1, le_min hut.2 hua⟩
    simp [Set.mem_Iic, hua, ht, hut, hum]
  · have hum : u ∉ Set.Ioc (0 : ℝ≥0) (min t a) :=
      fun h => hut ⟨h.1, h.2.trans (min_le_left _ _)⟩
    simp [Set.mem_Iic, hua, ht, hut, hum]
  · have hum : u ∉ Set.Ioc (0 : ℝ≥0) (min t a) :=
      fun h => hua (h.2.trans (min_le_right _ _))
    simp [Set.mem_Iic, hua, hum]
  · have hum : u ∉ Set.Ioc (0 : ℝ≥0) (min t a) :=
      fun h => hua (h.2.trans (min_le_right _ _))
    simp [Set.mem_Iic, hua, hum]

theorem wienerKernelPast_eq_self (a : ℝ≥0) (f : WienerKernelL2)
    (hsupport : ∀ᵐ t ∂nonnegativeLebesgueMeasure, a < t → f t = 0) :
    wienerKernelPast a f = f := by
  apply Lp.ext
  filter_upwards [wienerKernelPast_coeFn a f, hsupport] with t hcut ht
  rw [hcut]
  by_cases hta : t ≤ a
  · simp [Set.mem_Iic, hta]
  · simp [Set.mem_Iic, hta, ht (lt_of_not_ge hta)]

/-- The initial-time cutoff is zero in L², even if a representative takes an
arbitrary value at the Lebesgue-null initial endpoint. -/
theorem wienerKernelPast_zero (f : WienerKernelL2) : wienerKernelPast 0 f = 0 := by
  let C := wienerKernelPastCLM 0
  have hind (t : ℝ≥0) : C (intervalIndicator t) = 0 := by
    change wienerKernelPast 0 (intervalIndicator t) = 0
    rw [wienerKernelPast_intervalIndicator, min_eq_right (show (0 : ℝ≥0) ≤ t from bot_le)]
    simp only [intervalIndicator, Set.Ioc_self]
    exact indicatorConstLp_empty
  change C f = 0
  refine denseRange_stepToLp.induction_on f
    (isClosed_eq C.continuous continuous_const) ?_
  intro v
  induction v using Finsupp.induction with
  | zero => simp only [map_zero]
  | single_add t c v _ _ ih =>
    rw [map_add, stepToLp_single, map_add, map_smul, hind, ih, smul_zero, add_zero]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The Wiener integral of a truncated kernel is AE strongly measurable in
the original Brownian natural past. -/
theorem aestronglyMeasurable_wienerIntegral_past
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (a : ℝ≥0) (f : WienerKernelL2) :
    AEStronglyMeasurable[Filtration.natural B hsm a]
      (wienerIntegral hB (wienerKernelPast a f) : Ω → ℝ) P := by
  let C := (wienerIntegral hB).comp (wienerKernelPastCLM a)
  let 𝓕 := Filtration.natural B hsm
  have hm : 𝓕 a ≤ (inferInstance : MeasurableSpace Ω) := 𝓕.le a
  have hclosed : IsClosed {f : WienerKernelL2 | AEStronglyMeasurable[𝓕 a] (C f : Ω → ℝ) P} :=
    (isClosed_aestronglyMeasurable (F := ℝ) (p := (2 : ℝ≥0∞)) (μ := P) hm).preimage
      C.continuous
  have hind (t : ℝ≥0) : C (intervalIndicator t) ∈ lpMeas ℝ ℝ (𝓕 a) 2 P := by
    apply mem_lpMeas_iff_aestronglyMeasurable.mpr
    change AEStronglyMeasurable[𝓕 a]
      (wienerIntegral hB (wienerKernelPast a (intervalIndicator t)) : Ω → ℝ) P
    rw [wienerKernelPast_intervalIndicator, wienerIntegral_intervalIndicator]
    have hmeas : StronglyMeasurable[𝓕 a] (B (min t a)) :=
      ((Filtration.stronglyAdapted_natural hsm) (min t a)).mono
        ((Filtration.natural B hsm).mono (min_le_right t a))
    exact hmeas.aestronglyMeasurable.congr (coeFn_brownianLp hB (min t a)).symm
  change AEStronglyMeasurable[𝓕 a] (C f : Ω → ℝ) P
  refine denseRange_stepToLp.induction_on f hclosed ?_
  intro v
  apply (mem_lpMeas_iff_aestronglyMeasurable (𝕜 := ℝ)).mp
  induction v using Finsupp.induction with
  | zero =>
    simp only [map_zero]
    exact (lpMeas ℝ ℝ (𝓕 a) 2 P).zero_mem
  | single_add t c v _ _ ih =>
    rw [map_add, stepToLp_single, map_add, map_smul]
    exact (lpMeas ℝ ℝ (𝓕 a) 2 P).add_mem
      ((lpMeas ℝ ℝ (𝓕 a) 2 P).smul_mem c (hind t)) ih

/-- A deterministic kernel supported at or before `a` has a Wiener integral
measurable in the original Brownian natural sigma-algebra at `a`. -/
theorem aestronglyMeasurable_wienerIntegral_of_supported
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (a : ℝ≥0) (f : WienerKernelL2)
    (hsupport : ∀ᵐ t ∂nonnegativeLebesgueMeasure, a < t → f t = 0) :
    AEStronglyMeasurable[Filtration.natural B hsm a]
      (wienerIntegral hB f : Ω → ℝ) P := by
  have h := aestronglyMeasurable_wienerIntegral_past hB hsm a f
  rwa [wienerKernelPast_eq_self a f hsupport] at h

/-- Every fixed value of the continuous Brownian driver is AE adapted to the
original Brownian past containing the support of its deterministic kernel. -/
theorem aestronglyMeasurable_wienerBrownianDriver_of_supported
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (f : ℝ≥0 → WienerKernelL2)
    (hGram : ∀ s t, ⟪f s, f t⟫_ℝ = (min s t : ℝ)) (t a : ℝ≥0)
    (hsupport : ∀ᵐ u ∂nonnegativeLebesgueMeasure, a < u → f t u = 0) :
    AEStronglyMeasurable[Filtration.natural B hsm a]
      (wienerBrownianDriver hB f hGram t) P :=
  (aestronglyMeasurable_wienerIntegral_of_supported hB hsm a (f t) hsupport).congr
    (wienerBrownianDriver_ae_eq hB f hGram t).symm

end FourPapersCommon
