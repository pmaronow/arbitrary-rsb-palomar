module

public import GeneralDepthPaper.RevisedSectionTwoPhysicalBrownian

@[expose] public section

/-! The actual selected diffusion satisfies the physical-time state SDE
with the same independently proved standard Brownian motion used by the
physical Hessian integral. The stochastic noise is the genuine Wiener
integral of `sqrt (Ξ'')`, proved equal to the existing clock driver.
No stochastic representation is a hypothesis. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus Paper
open scoped Topology NNReal
namespace GeneralDepthPaper
open FourPapersCommon

/-- The actual covariance-clock noise has continuous physical-time paths. -/
theorem continuous_sectionTwoClockDriver (Ξ : AdmissibleCovariance)
    (sample : BrownianSample) :
    Continuous (fun q : Overlap => sectionTwoClockDriver Ξ q sample) := by
  unfold sectionTwoClockDriver sectionTwoBrownianTime
  exact continuous_const.mul ((continuous_canonicalBrownian sample).comp
    (continuous_real_toNNReal.comp (Ξ.continuous_clock.comp continuous_subtype_val)))

/-- The constructed physical Wiener integral has the actual continuous
clock driver as a modification, with fixed-time almost-sure equality. -/
theorem sectionTwoPhysicalNoiseWienerIntegral_continuous_modification
    (Ξ : AdmissibleCovariance) :
    (∀sample,Continuous (fun q : Overlap => sectionTwoClockDriver Ξ q sample)) ∧
    (∀q,sectionTwoPhysicalNoiseWienerIntegral Ξ q =ᵐ[canonicalBrownianMeasure]
      sectionTwoClockDriver Ξ q) :=
  ⟨continuous_sectionTwoClockDriver Ξ,sectionTwoPhysicalNoiseWienerIntegral_ae_eq_clock Ξ⟩

/-- The original-clock state equation with the literal `sqrt (Ξ'')`
Wiener integral against the proved physical-time standard Brownian motion.
This identity holds for every probability measure, a stronger scope than
the manuscript's finite-support diffusion clause. -/
theorem optimalState_physicalBrownian_integral_equation
    (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) (q : Overlap) :
    (fun sample => optimalState Ξ μ sample q) =ᵐ[canonicalBrownianMeasure]
      (fun sample => sectionTwoPhysicalNoiseWienerIntegral Ξ q sample+
        ∫s in (0:ℝ)..(q:ℝ),Ξ.second s*Paper.parisiCDF μ s*
          gradient Ξ μ s (optimalState Ξ μ sample s)) := by
  filter_upwards [sectionTwoPhysicalNoiseWienerIntegral_ae_eq_clock Ξ q] with sample hs
  rw [optimalState_integral_equation Ξ μ sample q.property]
  change sectionTwoClockDriver Ξ q sample+_ = sectionTwoPhysicalNoiseWienerIntegral Ξ q sample+_
  rw [hs]

end GeneralDepthPaper
