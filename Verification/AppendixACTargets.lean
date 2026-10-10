module

public import DepthPaper.RevisedAppendixAStep
public import DepthPaper.RevisedAppendixARecursion
public import DepthPaper.RevisedAppendixAContinuity
public import DepthPaper.RevisedAppendixATemperatureDiffusion
public import DepthPaper.RevisedDoobKernel

@[expose] public section

/-! Independently elaborated, fully expanded numbered Appendix A/C targets.
The statements below have no proposition-valued target aliases or proof holes. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction
namespace Verification.AppendixACTargets
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 64

section
open DepthPaper

/-- Exact expanded target for A1 i; checked against the public proof. -/
theorem appendix_a1_i :
    ∀ (a V : ℝ) (hV : 0 ≤ V)
    (g : TerminalSpace),
    (∀ c, coleHopfTerminal ((a,V),g+terminalConstant c) =
      coleHopfTerminal ((a,V),g)+terminalConstant c) ∧
    (∀ c, FRSB.constantMassKernel a V.toNNReal (terminalValue (g+terminalConstant c)) =
      FRSB.constantMassKernel a V.toNNReal (terminalValue g)) ∧
    (∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      coleHopfTerminal ((a,s),coleHopfTerminal ((a,t),g)) = coleHopfTerminal ((a,s+t),g)):=
  @DepthPaper.revised_one_step_constants_semigroup

end

section
open DepthPaper

/-- Exact expanded target for A1 ii; checked against the public proof. -/
theorem appendix_a1_ii :
    ∀ (a V : ℝ) (hV : 0 ≤ V) (g : TerminalSpace)
    (hg : ‖terminalJet g 0‖ ≤ 1),
    LipschitzWith 1 (terminalValue (coleHopfTerminal ((a,V),g))) ∧
    (∀ x, HasDerivAt (terminalValue (coleHopfTerminal ((a,V),g)))
      (∫ y, terminalJet g 0 y ∂FRSB.constantMassKernel a V.toNNReal (terminalValue g) x) x) ∧
    (∀ x, HasDerivAt (terminalJet (coleHopfTerminal ((a,V),g)) 0)
      ((∫ y, terminalJet g 1 y ∂FRSB.constantMassKernel a V.toNNReal (terminalValue g) x)+
        a*((∫ y, (terminalJet g 0 y)^2 ∂FRSB.constantMassKernel a V.toNNReal (terminalValue g) x)-
          (∫ y, terminalJet g 0 y ∂FRSB.constantMassKernel a V.toNNReal (terminalValue g) x)^2)) x) :=
  @DepthPaper.revised_one_step_spatial

end

section
open DepthPaper

/-- Exact expanded target for A1 iv smooth; checked against the public proof. -/
theorem appendix_a1_iv_smooth :
    ∀ (alo ahi Vlo Vhi M : ℝ)
    (halo : 0 < alo) (ha : alo ≤ ahi) (hVlo : 0 < Vlo) (hV : Vlo ≤ Vhi),
    ContDiffOn ℝ ∞ coleHopfTerminal
      {p : ColeHopfParameter | 0 < p.1.1 ∧ 0 < p.1.2 ∧ ‖terminalJet p.2 0‖ < 2} ∧
    (∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ColeHopfParameter,
      p.1.1 ∈ Icc alo ahi → p.1.2 ∈ Icc Vlo Vhi → terminalSumNorm p.2 ≤ M →
      ‖iteratedFDeriv ℝ n coleHopfTerminal p‖ ≤ C) :=
  @DepthPaper.revised_one_step_smooth_bounds

end

section
open DepthPaper

/-- Exact expanded target for A1 iv terminal derivative; checked against the public proof. -/
theorem appendix_a1_iv_terminal_derivative :
    ∀ (a V : ℝ) (hV : 0 ≤ V)
    (g : TerminalSpace),
    DifferentiableAt ℝ (fun h : TerminalSpace => coleHopfTerminal ((a,V),h)) g ∧
    ∀ k x, terminalValue (revisedColeHopfTerminalDerivative a V g k) x =
      ∫ y, terminalValue k y ∂FRSB.constantMassKernel a V.toNNReal (terminalValue g) x :=
  @DepthPaper.revised_one_step_terminal_derivative

end

section
open DepthPaper

/-- Exact expanded target for A1 iv boundary; checked against the public proof. -/
theorem appendix_a1_iv_boundary :
    ∀ (a V : ℝ) (hV : 0 ≤ V),
    (∃ L : TerminalSpace →L[ℝ] TerminalSpace,
      (∀ g, L g = coleHopfTerminal ((0,V),g)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ g, terminalSumNorm (L g) ≤ C*terminalSumNorm g) ∧
    (∃ L : TerminalSpace →L[ℝ] TerminalSpace,
      ∀ g, L g = coleHopfTerminal ((a,0),g)) :=
  @DepthPaper.revised_one_step_boundary_linear

end

section
open DepthPaper

/-- Exact expanded target for A1 iv sum norm; checked against the public proof. -/
theorem appendix_a1_iv_sum_norm :
    ∀ (alo ahi Vlo Vhi M : ℝ)
    (halo : 0 < alo) (ha : alo ≤ ahi) (hVlo : 0 < Vlo) (hV : Vlo ≤ Vhi)
    (n : ℕ),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ColeHopfParameter,
      p.1.1 ∈ Icc alo ahi → p.1.2 ∈ Icc Vlo Vhi → terminalSumNorm p.2 ≤ M →
      ∀ v : Fin n → ColeHopfParameter,
        terminalSumNorm (iteratedFDeriv ℝ n coleHopfTerminal p v) ≤
          C*∏ i, revisedColeHopfParameterSumNorm (v i) :=
  @DepthPaper.revised_one_step_sum_norm_bounds

end

section
open DepthPaper

/-- Exact expanded target for A2; checked against the public proof. -/
theorem appendix_a2 :
    ∀ (L ell d : ℕ) (hL : 1≤L)
    (alo ahi Vlo Vhi C0 : ℝ) (halo : 0<alo) (ha : alo≤ahi)
    (hVlo : 0<Vlo) (hVrange : Vlo≤Vhi),
    ∃C:ℝ,0≤C ∧ ∀(D:Set (Fin d→ℝ))
      (f g:(Fin d→ℝ)→ ColeHopfRecursionParameter L)
      (hf:RevisedClosedCData ell D f) (hg:RevisedClosedCData ell D g),
      (∀x∈D,∀i,((f x).1 i).1∈Icc alo ahi) →
      (∀x∈D,∀i,((g x).1 i).1∈Icc alo ahi) →
      (∀x∈D,∀i,((f x).1 i).2∈Icc Vlo Vhi) →
      (∀x∈D,∀i,((g x).1 i).2∈Icc Vlo Vhi) →
      (∀x∈D,‖terminalJet (f x).2 0‖≤1) →
      (∀x∈D,‖terminalJet (g x).2 0‖≤1) →
      (∀j≤ell,∀x∈D,∀w:Fin j→Fin d,∀i,
        |((hf.jets x j (fun k=>revisedParameterAxis d (w k))).1 i).1|+
        |((hf.jets x j (fun k=>revisedParameterAxis d (w k))).1 i).2|+
        terminalSumNorm (hf.jets x j (fun k=>revisedParameterAxis d (w k))).2≤C0) →
      (∀j≤ell,∀x∈D,∀w:Fin j→Fin d,∀i,
        |((hg.jets x j (fun k=>revisedParameterAxis d (w k))).1 i).1|+
        |((hg.jets x j (fun k=>revisedParameterAxis d (w k))).1 i).2|+
        terminalSumNorm (hg.jets x j (fun k=>revisedParameterAxis d (w k))).2≤C0) →
      ∀ε:ℝ,0≤ε →
      (∀j≤ell,∀x∈D,∀w:Fin j→Fin d,∀i,
        |(((hf.jets x j-hg.jets x j) (fun k=>revisedParameterAxis d (w k))).1 i).1|≤ε ∧
        |(((hf.jets x j-hg.jets x j) (fun k=>revisedParameterAxis d (w k))).1 i).2|≤ε ∧
        terminalSumNorm ((hf.jets x j-hg.jets x j) (fun k=>revisedParameterAxis d (w k))).2≤ε) →
      ∃(uf:RevisedClosedCData ell D (revisedColeHopfOutputs L∘f))
        (ug:RevisedClosedCData ell D (revisedColeHopfOutputs L∘g)),
        Nonempty (RevisedClosedCData ell D (fun x=>terminalValue (coleHopfRecursion L (f x)) 0)) ∧
        (∀x∈D,∀i,LipschitzWith 1 (terminalValue (revisedColeHopfOutputs L (f x) i))) ∧
        (∀x∈D,∀i,LipschitzWith 1 (terminalValue (revisedColeHopfOutputs L (g x) i))) ∧
        ∀j≤ell,∀x∈D,∀w:Fin j→Fin d,∀i,
          terminalSumNorm ((uf.jets x j (fun k=>revisedParameterAxis d (w k))) i)≤C ∧
          terminalSumNorm (((uf.jets x j-ug.jets x j)
            (fun k=>revisedParameterAxis d (w k))) i)≤C*ε :=
  @DepthPaper.revised_appendix_a_2

end

section
open DepthPaper

/-- Exact expanded target for A3; checked against the public proof. -/
theorem appendix_a3 :
    ∀ {r : ℕ} {qc : ℝ}
    (d : ℕ → TruncatedParisiData r qc) (d0 : TruncatedParisiData r qc)
    (h : TruncatedDataConvergence d d0),
    TendstoUniformlyOn (fun n => (d n).Gamma) d0.Gamma atTop (Icc (0:ℝ) qc) ∧
    TendstoUniformlyOn (fun n => (d n).Gamma2) d0.Gamma2 atTop (Icc (0:ℝ) qc) ∧
    (∀ j ≤ 2, TendstoUniformlyOn (fun n => closedJet qc j (d n).firstVariation)
      (closedJet qc j d0.firstVariation) atTop (Icc (0:ℝ) qc)) ∧
    ContDiffOn ℝ 2 d0.firstVariation (Icc (0:ℝ) qc) ∧
    (∀ n, ContDiffOn ℝ 2 (d n).firstVariation (Icc (0:ℝ) qc)) :=
  @DepthPaper.revised_observable_continuity

end

section
open DepthPaper

/-- Exact expanded target for A4; checked against the public proof. -/
theorem appendix_a4 :
    ∀ {r : ℕ} {qc : ℝ}
    (d : ℕ → TruncatedParisiData r qc) (d0 : TruncatedParisiData r qc)
    (hqc : qc ≤ 1) (h : TruncatedDataConvergence d d0)
    (hcov : ∀ n q, q ∈ Ioc (0:ℝ) qc → 0 < (d n).covarianceField 2 q)
    (hFle : ∀ q ∈ Icc (0:ℝ) qc, d0.firstVariation q ≤ 0)
    (hFzero : ∀ q ∈ Icc (0:ℝ) qc, d0.firstVariation q = 0 ↔
      q = 0 ∨ ∃ i : Fin r, (d0.node i.castSucc.succ : ℝ) = q)
    (hFneg : ∀ i : Fin r, d0.firstVariationSecond (d0.node i.castSucc.succ) < 0)
    (horigin : ∃ ε > 0, ∀ᶠ n in atTop, ∀ q ∈ Icc (0:ℝ) ε,
      (d n).Gamma q ≤ (1-ε)*q)
    (hcontact : ∀ᶠ n in atTop, ∀ i : Fin r,
      (d n).firstVariation ((d n).node i.castSucc.succ) = 0 ∧
      (d n).firstVariationPrime ((d n).node i.castSucc.succ) = 0),
    ∀ᶠ n in atTop,
      (∀ q ∈ Icc (0:ℝ) qc, (d n).firstVariation q ≤ 0) ∧
      (∀ q ∈ Icc (0:ℝ) qc, (d n).firstVariation q = 0 ↔
        q = 0 ∨ ∃ i : Fin r, q = ((d n).node i.castSucc.succ : ℝ)) ∧
      (∀ i : Fin r, (d n).firstVariationSecond ((d n).node i.castSucc.succ) < 0) :=
  @DepthPaper.revised_contact_persistence

end

section
open GeneralDepthPaper

/-- Exact expanded target for A7; checked against the public proof. -/
theorem appendix_a7 :
    ∀ (Ξ : AdmissibleCovariance) (ν : ParisiMeasure)
    (hν : (ν:Measure Overlap).support.Finite)
    (m : ℝ) (hm : m∈Ioc (0:ℝ) 1) (qc : ℝ) (hc : qc∈Ioc (0:ℝ) 1)
    (hs : ∀s∈FRSB.parisiSupport ν,s<qc),
    let d := sectionTwoAtomicLowerData Ξ ν hν m hm qc hc (fun s hs' => (hs s hs').le)
    (∀sample q, q∈Icc (0:ℝ) qc → sectionTwoCommonNoiseState d Ξ sample q =
      m⁻¹*optimalState (Ξ.temperatureScale m hm.1.ne') ν sample q) ∧
    (∀q∈Icc (0:ℝ) qc, d.Gamma q=Gamma (Ξ.temperatureScale m hm.1.ne') ν q) ∧
    (∀q∈Icc (0:ℝ) qc, d.firstVariation q=(m^2)⁻¹*firstVariation (Ξ.temperatureScale m hm.1.ne') ν q) :=
  @GeneralDepthPaper.revised_temperature_mass_diffusion_finite_atomic

end

section
open DepthPaper

/-- Exact expanded target for C3; checked against the public proof. -/
theorem appendix_c3 :
    ∀ {m : ℝ} (hm : 0 < m) (hm1 : m≤1)
    (W : ℝ≥0) (hW : 0<W) (t : ℝ≥0) (ht : 0<t) (htW : t≤W) (x : ℝ),
    revisedDoobKernel m W t x = volume.withDensity (fun y => ENNReal.ofReal
      (gaussianPDFReal x t y*Real.exp (m*terminalDoobPotential m W t y)/
        Real.exp (m*terminalDoobPotential m W 0 x))) ∧
    limitingDoobMeasure m t x = volume.withDensity (fun y => ENNReal.ofReal
      ((Real.exp (m*x)*gaussianPDFReal (x+m*(t:ℝ)) t y+
        Real.exp (-m*x)*gaussianPDFReal (x-m*(t:ℝ)) t y)/(2*Real.cosh (m*x)))) ∧
    IsProbabilityMeasure (revisedDoobKernel m W t x) ∧
    IsProbabilityMeasure (limitingDoobMeasure m t x) ∧
    (1/4:ℝ≥0∞)•limitingDoobMeasure m t x≤revisedDoobKernel m W t x ∧
    revisedDoobKernel m W t x≤(4:ℝ≥0∞)•limitingDoobMeasure m t x :=
  @DepthPaper.revised_doob_kernel

end

end Verification.AppendixACTargets
