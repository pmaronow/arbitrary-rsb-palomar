module

public import FRSB.MomentPolynomials
public import FRSB.JetMomentContinuity

@[expose] public section


/-! Genuine boundedness, integrability and physical-time continuity of every
polynomial moment of the actual optimal diffusion's positive spatial jets. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter MvPolynomial
open scoped Topology BigOperators
namespace FRSB
open Paper

def polynomialMomentBound (β : ℝ) (μ : ParisiMeasure) (f : MomentPolynomial) : ℝ :=
  ∑ d ∈ f.support, ‖f.coeff d‖ *
    ∏ j ∈ d.support, ‖bcfSpatialDerivative (parisiGradientBCF β μ) j‖ ^ d j

theorem polynomialMomentBound_nonneg (β : ℝ) (μ : ParisiMeasure) (f : MomentPolynomial) :
    0 ≤ polynomialMomentBound β μ f := by
  apply Finset.sum_nonneg
  intro d _
  exact mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _)

theorem norm_momentPolynomialValue_le (β : ℝ) (μ : ParisiMeasure)
    (f : MomentPolynomial) (s : ℝ) (ω : BrownianSample) :
    ‖momentPolynomialValue β μ f s ω‖ ≤ polynomialMomentBound β μ f := by
  unfold momentPolynomialValue polynomialMomentBound
  rw [eval_eq]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d _
  rw [norm_mul, norm_prod]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro j _
  exact norm_jetProcess_pow_le β μ j (d j) s ω

theorem measurable_momentPolynomialValue (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (f : MomentPolynomial) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    Measurable (momentPolynomialValue β μ f s) := by
  unfold momentPolynomialValue
  simp_rw [eval_eq]
  apply Finset.measurable_sum
  intro d _
  apply measurable_const.mul
  apply Finset.measurable_prod
  intro j _
  exact (measurable_jetProcess_succ β hβ μ j hs).pow_const _

theorem integrable_momentPolynomialValue (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (f : MomentPolynomial) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    Integrable (momentPolynomialValue β μ f s) canonicalBrownianMeasure :=
  (integrable_const (polynomialMomentBound β μ f)).mono'
    (measurable_momentPolynomialValue β hβ μ f hs).aestronglyMeasurable
    (.of_forall (norm_momentPolynomialValue_le β μ f s))

theorem continuous_momentPolynomialValue_path (β : ℝ) (μ : ParisiMeasure)
    (f : MomentPolynomial) (ω : BrownianSample) :
    Continuous (fun s => momentPolynomialValue β μ f s ω) := by
  unfold momentPolynomialValue
  simp_rw [eval_eq]
  apply continuous_finsetSum
  intro d _
  apply continuous_const.mul
  apply continuous_finsetProd
  intro j _
  exact ((continuous_parisiSpatialJet_succ β μ j).comp
    (continuous_id.prodMk (continuous_optimalStateReal β μ ω))).pow _

theorem continuousOn_moment (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (f : MomentPolynomial) : ContinuousOn (moment β μ f) (Icc (0 : ℝ) 1) := by
  apply continuousOn_of_dominated (μ := canonicalBrownianMeasure)
    (F := fun s ω => momentPolynomialValue β μ f s ω)
    (bound := fun _ => polynomialMomentBound β μ f)
  · intro s hs
    exact (measurable_momentPolynomialValue β hβ μ f hs).aestronglyMeasurable
  · intro s _
    exact .of_forall (norm_momentPolynomialValue_le β μ f s)
  · exact integrable_const _
  · exact .of_forall fun ω => (continuous_momentPolynomialValue_path β μ f ω).continuousOn

end FRSB
