module

public import GeneralDepthPaper.AtomMoveDerivative
public import GeneralDepthPaper.AtomMassTransfer

@[expose] public section


/-! Proposition 2.1, for the actual mixed Parisi functional and genuine
probability measures. The atom formulas hold for arbitrary order parameters,
which includes every finite positive atomic measure in the statement. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace GeneralDepthPaper

theorem first_variation_criterion (Ξ : AdmissibleCovariance) :
    (∀μ ν : ParisiMeasure,
      HasDerivWithinAt (fun t=>parisiFunctional Ξ (Paper.parisiMix μ ν t))
        (-((∫q : Overlap,firstVariation Ξ μ q ∂(ν : Measure Overlap))-
          (∫q : Overlap,firstVariation Ξ μ q ∂(μ : Measure Overlap)))) (Ioi (0:ℝ)) 0) ∧
    (∀(μ : ParisiMeasure)(a : Overlap),(a:ℝ)∈Ioo (0:ℝ) 1→
      HasDerivAt (fun t=>parisiFunctional Ξ (moveAtom μ a t))
        (-atomWeight μ a*firstVariationDerivative Ξ μ a) 0) ∧
    (∀(μ : ParisiMeasure)(a b : Overlap),0<atomWeight μ a→0<atomWeight μ b→
      HasDerivAt (fun t=>parisiFunctional Ξ (transferAtomMass μ a b t))
        (firstVariation Ξ μ b-firstVariation Ξ μ a) 0) ∧
    (∀μ : ParisiMeasure,
      (∀q∈Icc (0:ℝ) 1,firstVariation Ξ μ q≤0)→
      (μ : Measure Overlap) {q|firstVariation Ξ μ q=0}=1→
      μ=parisiMinimizer Ξ) :=
  ⟨hasDerivWithinAt_parisiFunctional_mix Ξ,
    hasDerivAt_parisiFunctional_moveAtom Ξ,
    hasDerivAt_parisiFunctional_transferAtomMass Ξ,
    unique_minimizer_of_firstVariation_criterion Ξ⟩

end GeneralDepthPaper
