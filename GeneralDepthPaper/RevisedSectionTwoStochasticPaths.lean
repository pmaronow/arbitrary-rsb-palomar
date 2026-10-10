module

public import GeneralDepthPaper.RevisedSectionTwoCurvature
public import FRSB.FiniteSchemeRepresentation

@[expose] public section

/-! Continuity, measurability, and actual finite-law representations used
to assemble the Hessian stochastic integral in Lemma 2.2. These results
use the genuine PDE-selected state and permit atoms at either endpoint. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus
open scoped Topology NNReal

namespace Paper

theorem continuous_selectedParisiGradientProcess_path
    (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) (sample : BrownianSample) :
    Continuous (fun t : ℝ≥0 => selectedParisiGradientProcess β h hβ μ t sample) := by
  exact (continuous_parisiGradient β μ).comp
    (NNReal.continuous_coe.prodMk
      (continuous_canonicalParisiItoState β h μ
        (fun t x => parisiGradient β μ (t,x))
        (continuous_parisiGradient β μ)
        (fun t x => norm_parisiGradient_le_one β μ (t,x))
        (lipschitzWith_parisiGradient β hβ μ) sample))

theorem measurable_selectedParisiGradientProcess_fixed
    (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) (t : ℝ≥0) :
    Measurable (selectedParisiGradientProcess β h hβ μ t) :=
  ((stronglyAdapted_selectedParisiGradientProcess β h hβ μ t).mono
    (canonicalBrownianFiltration.le t)).measurable

end Paper

namespace GeneralDepthPaper
open FourPapersCommon

theorem continuous_sectionTwoGradientProcess_path
    (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) (sample : BrownianSample) :
    Continuous (fun q : Overlap => sectionTwoGradientProcess Ξ μ q sample) := by
  have ht : Continuous (sectionTwoBrownianTime Ξ) :=
    continuous_real_toNNReal.comp (Ξ.continuous_clock.comp continuous_subtype_val)
  have he : (fun q : Overlap => sectionTwoGradientProcess Ξ μ q sample)=
      fun q => Paper.selectedParisiGradientProcess (mixedBeta Ξ.toEvenMixture) 0
        (mixedBeta_ne_zero Ξ.toEvenMixture) (mixedMeasure Ξ.toEvenMixture μ)
        (sectionTwoBrownianTime Ξ q) sample := by
    funext q
    exact congrFun (sectionTwoGradientProcess_eq_selected Ξ μ q) sample
  rw [he]
  exact (Paper.continuous_selectedParisiGradientProcess_path _ _ _ _ sample).comp ht

theorem measurable_sectionTwoGradientProcess_fixed
    (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) (q : Overlap) :
    Measurable (sectionTwoGradientProcess Ξ μ q) := by
  rw [sectionTwoGradientProcess_eq_selected]
  exact Paper.measurable_selectedParisiGradientProcess_fixed _ _ _ _ _

/-- A continuous covariance-clock push-forward of a genuinely finite
probability law has finite support, including any transported endpoint atoms. -/
theorem finite_support_sectionTwoMixedMeasure
    (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (hμ : (μ : Measure Overlap).support.Finite) :
    (mixedMeasure Ξ.toEvenMixture μ : Measure Overlap).support.Finite := by
  let S := Ξ.toEvenMixture.unitClock '' (μ : Measure Overlap).support
  have hS : S.Finite := hμ.image _
  apply hS.subset
  apply Measure.support_subset_of_isClosed hS.isClosed
  change ∀ᵐ q ∂(μ : Measure Overlap).map Ξ.toEvenMixture.unitClock, q∈S
  apply (ae_map_iff Ξ.toEvenMixture.continuous_unitClock.measurable.aemeasurable
    hS.isClosed.measurableSet).mpr
  filter_upwards [(μ : Measure Overlap).support_mem_ae] with q hq
  exact ⟨q,hq,rfl⟩

def sectionTwoMixedFiniteScheme (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (hμ : (μ : Measure Overlap).support.Finite) :=
  FRSB.finiteLawRSBScheme (mixedMeasure Ξ.toEvenMixture μ)
    (finite_support_sectionTwoMixedMeasure Ξ μ hμ)

theorem sectionTwoMixedFiniteScheme_represents
    (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (hμ : (μ : Measure Overlap).support.Finite) :
    Paper.parisiSchemeMeasure (sectionTwoMixedFiniteScheme Ξ μ hμ)=
      mixedMeasure Ξ.toEvenMixture μ :=
  FRSB.parisiSchemeMeasure_finiteLawRSBScheme _ _

theorem sectionTwoMixedFiniteScheme_gradient
    (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (hμ : (μ : Measure Overlap).support.Finite) :
    Paper.parisiGradient (mixedBeta Ξ.toEvenMixture) (mixedMeasure Ξ.toEvenMixture μ)=
      Paper.parisiFiniteGradient (sectionTwoMixedFiniteScheme Ξ μ hμ)
        (mixedBeta Ξ.toEvenMixture) :=
  FRSB.parisiGradient_finiteLawRSBScheme _ (mixedBeta_ne_zero _) _ _

end GeneralDepthPaper
