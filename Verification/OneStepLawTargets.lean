module

public import DepthPaper.RevisedAppendixADiffusionLaw

@[expose] public section

/-! An expanded exact target check for revised Appendix A.1(iii).
The terminal datum is arbitrary in the paper's Banach space and is assumed
one-Lipschitz.  The drift is the actual derivative of the raw Cole--Hopf
transform.  The process is constructed from the common canonical Brownian
motion; its transition law and pathwise uniqueness are conclusions.
Both zero mass and zero variance belong to the quantified domain. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
open scoped NNReal

namespace Verification.OneStepLawTargets
open DepthPaper ColeHopfFoundation.ProbabilityTheory

/-- Exact arbitrary-terminal diffusion statement, with adaptedness,
existence, the normalized endpoint probability kernel and pathwise
uniqueness on the entire closed interval. -/
theorem appendixA1DiffusionLaw_exact (a V : ℝ) (ha : 0 ≤ a) (hV : 0 ≤ V)
    (g : TerminalSpace) (hg : LipschitzWith 1 (terminalValue g)) (x : ℝ) :
    ∃ ξ : ℝ≥0 → BrownianSample → ℝ,
      StronglyAdapted canonicalBrownianFiltration ξ ∧
      (∀ sample, Continuous (fun t => ξ t sample)) ∧
      (∀ sample, ξ 0 sample = x) ∧
      (∀ sample, ∀ t : ℝ≥0, (t : ℝ) ≤ V →
        ξ t sample = x + canonicalBrownian t sample +
          ∫ s in 0..(t : ℝ),
            a * deriv (coleHopf a (V - s).toNNReal (terminalValue g))
              (ξ s.toNNReal sample)) ∧
      canonicalBrownianMeasure.map (ξ V.toNNReal) =
        FRSB.constantMassKernel a V.toNNReal (terminalValue g) x ∧
      (∀ sample, ∀ X : ℝ → ℝ, ContinuousOn X (Icc (0 : ℝ) V) →
        (∀ t ∈ Icc (0 : ℝ) V,
          X t = x + canonicalBrownian t.toNNReal sample +
            ∫ s in 0..t,
              a * deriv (coleHopf a (V - s).toNNReal (terminalValue g)) (X s)) →
        ∀ t ∈ Icc (0 : ℝ) V, X t = ξ t.toNNReal sample) :=
  revised_appendix_a_1_iii a V ha hV g
    ((revised_terminal_oneLipschitz_iff g).mp hg) x

end Verification.OneStepLawTargets
