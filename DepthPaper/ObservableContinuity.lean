module

public import DepthPaper.TruncatedVariationConvergence

@[expose] public section


/-! Literal Appendix A.2 observable regularity and parameter continuity. No
smoothness, diffusion, moment, or approximation hypotheses replace the actual
truncated Parisi recursion and its constructed optimal diffusion. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper

/-- Appendix A.2, Lemma `observable-continuity`: full closed-interval regularity
and convergence of the actual overlap and actual C² first-variation jets. -/
theorem observable_continuity {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) :
    ContDiffOn ℝ 1 d.Gamma (Icc (0:ℝ) qc) ∧
    (∀q∈Icc (0:ℝ) qc,HasDerivWithinAt d.Gamma
      (d.covarianceField 2 q*d.Gamma2 q) (Icc (0:ℝ) qc) q) ∧
    ContDiffOn ℝ 2 d.firstVariation (Icc (0:ℝ) qc) ∧
    (∀dn : ℕ → TruncatedParisiData r qc,TruncatedDataConvergence dn d →
      TendstoUniformlyOn (fun n => (dn n).Gamma) d.Gamma atTop (Icc (0:ℝ) qc) ∧
      Tendsto (fun n => (dn n).firstVariationJets) atTop (𝓝 d.firstVariationJets)) :=
  ⟨d.contDiffOn_Gamma,d.hasDerivWithinAt_Gamma,d.contDiffOn_firstVariation,
    fun _ h => ⟨h.Gamma,h.firstVariation_C2⟩⟩

end DepthPaper
