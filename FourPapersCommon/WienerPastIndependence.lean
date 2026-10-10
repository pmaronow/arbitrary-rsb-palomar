module

public import FourPapersCommon.WienerBrownianDriver
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
public import Mathlib.Probability.Independence.Process.Basic
public import Mathlib.Probability.Process.Filtration

@[expose] public section

/-! Deterministic Wiener kernels orthogonal to the original Brownian past
give random variables independent of its whole natural past sigma-algebra.
The process independence theorem uses per-coordinate almost-everywhere
equalities, so it does not require an uncountable intersection of null sets. -/

noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace

namespace FourPapersCommon

variable {Ω S T : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ}

/-- Orthogonal families of deterministic kernels have independent Wiener
integral processes, including families with an arbitrary index type. -/
theorem indepFun_wienerIntegral_families
    (hB : IsPreBrownianReal B P)
    (f : S → Lp ℝ 2 nonnegativeLebesgueMeasure)
    (g : T → Lp ℝ 2 nonnegativeLebesgueMeasure)
    (horth : ∀ s t, ⟪f s, g t⟫_ℝ = 0) :
    IndepFun (fun ω s => wienerIntegral hB (f s) ω)
      (fun ω t => wienerIntegral hB (g t) ω) P := by
  have hjoint := isGaussianProcess_wienerIntegral hB (Sum.elim f g)
  have hprocess : (fun i ω => wienerIntegral hB (Sum.elim f g i) ω) =
      Sum.elim (fun s ω => wienerIntegral hB (f s) ω)
        (fun t ω => wienerIntegral hB (g t) ω) := by
    funext i ω
    cases i <;> rfl
  rw [hprocess] at hjoint
  apply hjoint.indepFun_of_covariance_eq_zero
  · intro s
    exact (Lp.aestronglyMeasurable (wienerIntegral hB (f s))).aemeasurable
  · intro t
    exact (Lp.aestronglyMeasurable (wienerIntegral hB (g t))).aemeasurable
  · intro s t
    rw [covariance_wienerIntegral, horth]

/-- A deterministic Wiener kernel orthogonal to every past interval
indicator is independent of the entire original Brownian past process. -/
theorem indepFun_wienerIntegral_past
    (hB : IsPreBrownianReal B P)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) (a : ℝ≥0)
    (horth : ∀ t : ℝ≥0, t ≤ a → ⟪f, intervalIndicator t⟫_ℝ = 0) :
    IndepFun (wienerIntegral hB f : Ω → ℝ)
      (fun ω (t : Set.Iic a) => B t ω) P := by
  have hfamilies := indepFun_wienerIntegral_families hB
    (fun _ : Unit => f) (fun t : Set.Iic a => intervalIndicator t)
    (fun _ t => horth t t.property)
  have hpast : IndepFun (fun ω (_ : Unit) => wienerIntegral hB f ω)
      (fun ω (t : Set.Iic a) => B t ω) P := by
    apply hfamilies.process_congr_right
    intro t
    rw [wienerIntegral_intervalIndicator]
    exact coeFn_brownianLp hB t
  simpa only [Function.comp_def, id_eq] using
    hpast.comp (measurable_pi_apply ()) measurable_id

/-- The orthogonal future kernel is independent of the original Brownian
natural filtration at the given time, without replacing that filtration. -/
theorem indep_wienerIntegral_natural
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) (a : ℝ≥0)
    (horth : ∀ t : ℝ≥0, t ≤ a → ⟪f, intervalIndicator t⟫_ℝ = 0) :
    Indep (MeasurableSpace.comap (wienerIntegral hB f : Ω → ℝ) inferInstance)
      (Filtration.natural B hsm a) P := by
  rw [Filtration.natural_eq_comap]
  exact (IndepFun_iff_Indep _ _ P).1 (indepFun_wienerIntegral_past hB f a horth)

/-- Independence from the original past survives replacing the Wiener value
by any almost-everywhere equal representative or continuous modification. -/
theorem indepFun_wienerIntegral_past_congr
    (hB : IsPreBrownianReal B P)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) (a : ℝ≥0)
    (horth : ∀ t : ℝ≥0, t ≤ a → ⟪f, intervalIndicator t⟫_ℝ = 0)
    (Z : Ω → ℝ) (hZ : (wienerIntegral hB f : Ω → ℝ) =ᵐ[P] Z) :
    IndepFun Z (fun ω (t : Set.Iic a) => B t ω) P :=
  (indepFun_wienerIntegral_past hB f a horth).congr hZ (Filter.EventuallyEq.rfl)

theorem indep_wienerIntegral_natural_congr
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) (a : ℝ≥0)
    (horth : ∀ t : ℝ≥0, t ≤ a → ⟪f, intervalIndicator t⟫_ℝ = 0)
    (Z : Ω → ℝ) (hZ : (wienerIntegral hB f : Ω → ℝ) =ᵐ[P] Z) :
    Indep (MeasurableSpace.comap Z inferInstance) (Filtration.natural B hsm a) P := by
  rw [Filtration.natural_eq_comap]
  exact (IndepFun_iff_Indep _ _ P).1
    (indepFun_wienerIntegral_past_congr hB f a horth Z hZ)

/-- An increment of the continuous Brownian modification remains independent
of the original Brownian natural past whenever its kernel difference is
orthogonal to all interval indicators from that past. -/
theorem indep_wienerBrownianDriver_increment_natural
    (hB : IsPreBrownianReal B P) (hsm : ∀ u, StronglyMeasurable (B u))
    (f : ℝ≥0 → Lp ℝ 2 nonnegativeLebesgueMeasure)
    (hGram : ∀ u v, ⟪f u, f v⟫_ℝ = (min u v : ℝ))
    (s t a : ℝ≥0)
    (horth : ∀ u : ℝ≥0, u ≤ a → ⟪f t - f s, intervalIndicator u⟫_ℝ = 0) :
    Indep (MeasurableSpace.comap
      (wienerBrownianDriver hB f hGram t - wienerBrownianDriver hB f hGram s)
      inferInstance) (Filtration.natural B hsm a) P := by
  apply indep_wienerIntegral_natural_congr hB hsm (f t - f s) a horth
  calc
    (wienerIntegral hB (f t - f s) : Ω → ℝ)
        =ᵐ[P] (wienerIntegral hB (f t) : Ω → ℝ) - wienerIntegral hB (f s) := by
      rw [map_sub]
      exact Lp.coeFn_sub _ _
    _ =ᵐ[P] wienerBrownianDriver hB f hGram t - wienerBrownianDriver hB f hGram s :=
      (wienerBrownianDriver_ae_eq hB f hGram t).symm.sub
        (wienerBrownianDriver_ae_eq hB f hGram s).symm

end FourPapersCommon
