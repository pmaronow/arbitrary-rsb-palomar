module

public import Paper.ParisiControlDerivative
public import Mathlib.Analysis.Calculus.DerivativeTest

@[expose] public section

/-! Second derivatives of the genuine fixed-control Parisi payoff.
This supplies the quantitative strict-convexity contribution used in the
revised paper's atomic Hessian argument. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace DepthPaper
open Paper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

def parisiAffineControlSecondDerivative {Ω : Type*} (β h : ℝ) (B : Ω → ℝ)
    (A : ℝ → Ω → ℝ) (μ ν : ParisiMeasure) (t : ℝ) (ω : Ω) : ℝ :=
  sech (h + β * B ω + parisiControlDrift β μ A ω +
    t * (parisiControlDrift β ν A ω - parisiControlDrift β μ A ω)) ^ 2 *
      (parisiControlDrift β ν A ω - parisiControlDrift β μ A ω) ^ 2

theorem parisiAffineControlDerivative_hasDerivAt {Ω : Type*} (β h : ℝ)
    (B : Ω → ℝ) (A : ℝ → Ω → ℝ) (μ ν : ParisiMeasure) (t : ℝ) (ω : Ω) :
    HasDerivAt (fun r => parisiAffineControlDerivative β h B A μ ν r ω)
      (parisiAffineControlSecondDerivative β h B A μ ν t ω) t := by
  let d := parisiControlDrift β ν A ω - parisiControlDrift β μ A ω
  have hin : HasDerivAt (fun r => h + β * B ω + parisiControlDrift β μ A ω + r * d) d t := by
    simpa only [id_eq, one_mul] using
      ((hasDerivAt_id t).mul_const d).const_add (h + β * B ω + parisiControlDrift β μ A ω)
  convert (((hasDerivAt_tanh _).comp t hin).mul_const d).sub_const
    (parisiControlCost β ν A ω - parisiControlCost β μ A ω) using 1
  · rfl
  · dsimp only [parisiAffineControlSecondDerivative, d]
    ring

theorem measurable_parisiAffineControlSecondDerivative {Ω : Type*} [MeasurableSpace Ω]
    (β h : ℝ) (B : Ω → ℝ) (hB : Measurable B) (A : ℝ → Ω → ℝ)
    (hA : Measurable (Function.uncurry A)) (μ ν : ParisiMeasure) (t : ℝ) :
    Measurable (parisiAffineControlSecondDerivative β h B A μ ν t) := by
  have hdμ := measurable_parisiControlDrift β μ A hA
  have hdν := measurable_parisiControlDrift β ν A hA
  have hs : Measurable sech := (continuous_iff_continuousAt.mpr
    fun x => (hasDerivAt_sech x).continuousAt).measurable
  exact ((hs.comp (((measurable_const.add (hB.const_mul β)).add hdμ).add
    ((hdν.sub hdμ).const_mul t))).pow_const 2).mul ((hdν.sub hdμ).pow_const 2)

theorem parisiAffineControlSecondDerivative_norm_le {Ω : Type*} (β h : ℝ)
    (B : Ω → ℝ) (A : ℝ → Ω → ℝ) (hb : ∀ s ω, ‖A s ω‖ ≤ 1)
    (μ ν : ParisiMeasure) (t : ℝ) (ω : Ω) :
    ‖parisiAffineControlSecondDerivative β h B A μ ν t ω‖ ≤ (2 * β ^ 2) ^ 2 := by
  have hd : ‖parisiControlDrift β ν A ω - parisiControlDrift β μ A ω‖ ≤ 2 * β ^ 2 :=
    (norm_sub_le _ _).trans (by
      have hi := parisiControlDrift_norm_le β μ A hb ω
      have hj := parisiControlDrift_norm_le β ν A hb ω
      linarith)
  unfold parisiAffineControlSecondDerivative
  rw [norm_mul, norm_pow, norm_pow]
  have hs : ‖sech (h + β * B ω + parisiControlDrift β μ A ω +
      t * (parisiControlDrift β ν A ω - parisiControlDrift β μ A ω))‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (sech_pos _)]
    exact sech_le_one _
  calc
    _ ≤ 1 * (2 * β ^ 2) ^ 2 := mul_le_mul
      (pow_le_one₀ (norm_nonneg _) hs) (pow_le_pow_left₀ (norm_nonneg _) hd 2)
      (sq_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem integrable_parisiAffineControlDerivative {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (β h : ℝ) (B : Ω → ℝ)
    (hB : Measurable B) (A : ℝ → Ω → ℝ) (hA : Measurable (Function.uncurry A))
    (hb : ∀ s ω, ‖A s ω‖ ≤ 1) (μ ν : ParisiMeasure) (t : ℝ) :
    Integrable (parisiAffineControlDerivative β h B A μ ν t) P :=
  (integrable_const (3 * β ^ 2)).mono'
    (measurable_parisiAffineControlDerivative β h B hB A hA μ ν t).aestronglyMeasurable
    (.of_forall fun ω => parisiAffineControlDerivative_norm_le β h B A hb μ ν t ω)

theorem hasDerivAt_integral_parisiAffineControlDerivative {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (β h : ℝ) (B : Ω → ℝ)
    (hB : Measurable B) (A : ℝ → Ω → ℝ) (hA : Measurable (Function.uncurry A))
    (hb : ∀ s ω, ‖A s ω‖ ≤ 1) (μ ν : ParisiMeasure) (t : ℝ) :
    HasDerivAt (fun r => ∫ω, parisiAffineControlDerivative β h B A μ ν r ω ∂P)
      (∫ω, parisiAffineControlSecondDerivative β h B A μ ν t ω ∂P) t := by
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun r ω => parisiAffineControlDerivative β h B A μ ν r ω)
    (F' := fun r ω => parisiAffineControlSecondDerivative β h B A μ ν r ω)
    (bound := fun _ => (2 * β ^ 2) ^ 2) (s := (univ : Set ℝ)) (by simp)
    (.of_forall fun r =>
      (measurable_parisiAffineControlDerivative β h B hB A hA μ ν r).aestronglyMeasurable)
    (integrable_parisiAffineControlDerivative P β h B hB A hA hb μ ν t)
    (measurable_parisiAffineControlSecondDerivative β h B hB A hA μ ν t).aestronglyMeasurable
    (.of_forall fun ω r _ => parisiAffineControlSecondDerivative_norm_le β h B A hb μ ν r ω)
    (integrable_const ((2 * β ^ 2) ^ 2))
    (.of_forall fun ω r _ => parisiAffineControlDerivative_hasDerivAt β h B A μ ν r ω)).2

theorem integrable_parisiAffineControlPayoff {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (β h : ℝ) (B : Ω → ℝ)
    (hB : Measurable B) (hBi : Integrable B P) (A : ℝ → Ω → ℝ)
    (hA : Measurable (Function.uncurry A)) (hb : ∀ s ω, ‖A s ω‖ ≤ 1)
    (μ ν : ParisiMeasure) (t : ℝ) :
    Integrable (parisiAffineControlPayoff β h B A μ ν t) P := by
  have hd (ρ : ParisiMeasure) : Integrable (parisiControlDrift β ρ A) P :=
    (integrable_const (β ^ 2)).mono'
      (measurable_parisiControlDrift β ρ A hA).aestronglyMeasurable
      (.of_forall fun ω => parisiControlDrift_norm_le β ρ A hb ω)
  have hc (ρ : ParisiMeasure) : Integrable (parisiControlCost β ρ A) P :=
    (integrable_const (β ^ 2 / 2)).mono'
      (measurable_parisiControlCost β ρ A hA).aestronglyMeasurable
      (.of_forall fun ω => parisiControlCost_norm_le β ρ A hb ω)
  let X : Ω → ℝ := fun ω => h + β * B ω + parisiControlDrift β μ A ω +
    t * (parisiControlDrift β ν A ω - parisiControlDrift β μ A ω)
  have hX : Integrable X P :=
    (((integrable_const h).add (hBi.const_mul β)).add (hd μ)).add (((hd ν).sub (hd μ)).const_mul t)
  have hXm : Measurable X :=
    (((measurable_const.add (hB.const_mul β)).add (measurable_parisiControlDrift β μ A hA))).add
      (((measurable_parisiControlDrift β ν A hA).sub
        (measurable_parisiControlDrift β μ A hA)).const_mul t)
  have hlog : Integrable (fun ω => Real.log (Real.cosh (X ω))) P :=
    hX.norm.mono' ((((Real.continuous_cosh).log
      (fun x => (Real.cosh_pos x).ne')).measurable.comp hXm).aestronglyMeasurable)
      (.of_forall fun ω => by simpa only [Real.norm_eq_abs] using norm_logcosh_le_abs (X ω))
  exact hlog.sub ((hc μ).add (((hc ν).sub (hc μ)).const_mul t))

theorem hasDerivAt_integral_parisiAffineControlPayoff {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (β h : ℝ) (B : Ω → ℝ)
    (hB : Measurable B) (hBi : Integrable B P) (A : ℝ → Ω → ℝ)
    (hA : Measurable (Function.uncurry A)) (hb : ∀ s ω, ‖A s ω‖ ≤ 1)
    (μ ν : ParisiMeasure) (t : ℝ) :
    HasDerivAt (fun r => ∫ω, parisiAffineControlPayoff β h B A μ ν r ω ∂P)
      (∫ω, parisiAffineControlDerivative β h B A μ ν t ω ∂P) t := by
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun r ω => parisiAffineControlPayoff β h B A μ ν r ω)
    (F' := fun r ω => parisiAffineControlDerivative β h B A μ ν r ω)
    (bound := fun _ => 3 * β ^ 2) (s := (univ : Set ℝ)) (by simp)
    (.of_forall fun r =>
      (measurable_parisiAffineControlPayoff β h B hB A hA μ ν r).aestronglyMeasurable)
    (integrable_parisiAffineControlPayoff P β h B hB hBi A hA hb μ ν t)
    (measurable_parisiAffineControlDerivative β h B hB A hA μ ν t).aestronglyMeasurable
    (.of_forall fun ω r _ => parisiAffineControlDerivative_norm_le β h B A hb μ ν r ω)
    (integrable_const (3 * β ^ 2))
    (.of_forall fun ω r _ => parisiAffineControlPayoff_hasDerivAt β h B A μ ν r ω)).2

theorem hasDerivAt_deriv_integral_parisiAffineControlPayoff {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (β h : ℝ) (B : Ω → ℝ)
    (hB : Measurable B) (hBi : Integrable B P) (A : ℝ → Ω → ℝ)
    (hA : Measurable (Function.uncurry A)) (hb : ∀ s ω, ‖A s ω‖ ≤ 1)
    (μ ν : ParisiMeasure) (t : ℝ) :
    HasDerivAt (deriv (fun r => ∫ω, parisiAffineControlPayoff β h B A μ ν r ω ∂P))
      (∫ω, parisiAffineControlSecondDerivative β h B A μ ν t ω ∂P) t := by
  have he : deriv (fun r => ∫ω, parisiAffineControlPayoff β h B A μ ν r ω ∂P) =
      fun r => ∫ω, parisiAffineControlDerivative β h B A μ ν r ω ∂P :=
    funext fun r => (hasDerivAt_integral_parisiAffineControlPayoff P β h B hB hBi A hA hb μ ν r).deriv
  rw [he]
  exact hasDerivAt_integral_parisiAffineControlDerivative P β h B hB A hA hb μ ν t

theorem integral_parisiAffineControlSecondDerivative_pos {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (β h : ℝ) (B : Ω → ℝ)
    (hB : Measurable B) (A : ℝ → Ω → ℝ) (hA : Measurable (Function.uncurry A))
    (hb : ∀ s ω, ‖A s ω‖ ≤ 1) (μ ν : ParisiMeasure) (t : ℝ)
    (hne : ¬ parisiControlDrift β ν A =ᵐ[P] parisiControlDrift β μ A) :
    0 < ∫ω, parisiAffineControlSecondDerivative β h B A μ ν t ω ∂P := by
  have hi : Integrable (parisiAffineControlSecondDerivative β h B A μ ν t) P :=
    (integrable_const ((2 * β ^ 2) ^ 2)).mono'
      (measurable_parisiAffineControlSecondDerivative β h B hB A hA μ ν t).aestronglyMeasurable
      (.of_forall fun ω => parisiAffineControlSecondDerivative_norm_le β h B A hb μ ν t ω)
  have hn : ∀ω, 0 ≤ parisiAffineControlSecondDerivative β h B A μ ν t ω :=
    fun ω => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hnonneg : 0 ≤ ∫ω, parisiAffineControlSecondDerivative β h B A μ ν t ω ∂P :=
    MeasureTheory.integral_nonneg hn
  apply lt_of_le_of_ne hnonneg
  intro he
  have hz := (integral_eq_zero_iff_of_nonneg_ae (.of_forall hn) hi).mp he.symm
  apply hne
  filter_upwards [hz] with ω hω
  change sech _ ^ 2 * (parisiControlDrift β ν A ω - parisiControlDrift β μ A ω) ^ 2 = 0 at hω
  have hd := (mul_eq_zero.mp hω).resolve_left (pow_ne_zero 2 (sech_pos _).ne')
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hd)

end DepthPaper
