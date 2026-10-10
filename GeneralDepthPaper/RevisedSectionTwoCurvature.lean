module

public import GeneralDepthPaper.Curvature
public import Paper.ParisiGradientMartingaleLaw

@[expose] public section

/-! The analytic and genuine martingale clauses of revised Lemma 2.2.
The process is evaluated along the actual optimal diffusion in physical
covariance coordinates. Its filtration is the actual Brownian filtration
at the deterministic normalized variance clock.

The Hessian stochastic-integral representation is proved separately in
`RevisedSectionTwoPhysicalBrownianGluing`; this module supplies the analytic
and martingale clauses used by the full physical-time target. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus
open scoped Topology NNReal
namespace GeneralDepthPaper
open FourPapersCommon
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

def sectionTwoGradientProcess (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (q : Overlap) (ω : BrownianSample) : ℝ :=
  gradient Ξ μ q (optimalState Ξ μ ω q)

def sectionTwoBrownianTime (Ξ : AdmissibleCovariance) (q : Overlap) : ℝ≥0 :=
  (Ξ.clock q).toNNReal

theorem monotone_sectionTwoBrownianTime (Ξ : AdmissibleCovariance) :
    Monotone (sectionTwoBrownianTime Ξ) := by
  intro s t hst
  exact Real.toNNReal_mono (Ξ.clock_strictMonoOn.monotoneOn s.property.1 t.property.1 hst)

def sectionTwoGradientFiltration (Ξ : AdmissibleCovariance) :
    Filtration Overlap (inferInstance : MeasurableSpace BrownianSample) :=
  monotoneReindexFiltration Paper.canonicalBrownianFiltration
    (sectionTwoBrownianTime Ξ) (monotone_sectionTwoBrownianTime Ξ)

theorem sectionTwoGradientProcess_eq_selected (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (q : Overlap) :
    sectionTwoGradientProcess Ξ μ q=
      Paper.selectedParisiGradientProcess (mixedBeta Ξ.toEvenMixture) 0
        (mixedBeta_ne_zero Ξ.toEvenMixture) (mixedMeasure Ξ.toEvenMixture μ)
        (sectionTwoBrownianTime Ξ q) := by
  funext ω
  have hclock : Ξ.clock q ∈ Icc (0:ℝ) 1 := by
    simpa only [AdmissibleCovariance.toEvenMixture_clock] using
      Ξ.toEvenMixture.clock_mem_unitInterval q.property
  have hnn : ((Ξ.clock q).toNNReal:ℝ)=Ξ.clock q := Real.coe_toNNReal _ hclock.1
  simp only [sectionTwoGradientProcess,sectionTwoBrownianTime,gradient,optimalState,
    mixedGradient,mixedState,Paper.selectedParisiGradientProcess,
    AdmissibleCovariance.toEvenMixture_clock]
  rw [Paper.selectedParisiItoState_eq _ _ _ _
    (by simpa only [hnn] using hclock.2) ω,hnn]

theorem sectionTwoGradientProcess_martingale (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) :
    Martingale (sectionTwoGradientProcess Ξ μ) (sectionTwoGradientFiltration Ξ)
      Paper.canonicalBrownianMeasure := by
  refine ⟨?_,?_⟩
  · intro q
    change StronglyMeasurable[Paper.canonicalBrownianFiltration (sectionTwoBrownianTime Ξ q)]
      (sectionTwoGradientProcess Ξ μ q)
    rw [sectionTwoGradientProcess_eq_selected]
    exact Paper.stronglyAdapted_selectedParisiGradientProcess _ _ _ _ _
  · intro s t hst
    change Paper.canonicalBrownianMeasure[sectionTwoGradientProcess Ξ μ t |
      Paper.canonicalBrownianFiltration (sectionTwoBrownianTime Ξ s)] =ᵐ[Paper.canonicalBrownianMeasure]
      sectionTwoGradientProcess Ξ μ s
    rw [sectionTwoGradientProcess_eq_selected,sectionTwoGradientProcess_eq_selected]
    exact Paper.condExp_selectedParisiGradientProcess _ _ _ _ _ _
      (monotone_sectionTwoBrownianTime Ξ hst)
      (by
        have ht : Ξ.clock t ∈ Icc (0:ℝ) 1 := by
          simpa only [AdmissibleCovariance.toEvenMixture_clock] using
            Ξ.toEvenMixture.clock_mem_unitInterval t.property
        rw [sectionTwoBrownianTime,Real.coe_toNNReal _ ht.1]
        exact ht.2)

theorem sectionTwoGradientProcess_zero (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (ω : BrownianSample) : sectionTwoGradientProcess Ξ μ ⟨0,by norm_num⟩ ω=0 := by
  change mixedGradient Ξ.toEvenMixture μ (0,mixedState Ξ.toEvenMixture 0 μ ω 0)=0
  rw [mixedState_initial]
  exact mixedGradient_at_zero _ _ _ (by norm_num)

theorem sectionTwoGradientProcess_one (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (ω : BrownianSample) :
    sectionTwoGradientProcess Ξ μ ⟨1,by norm_num⟩ ω=Real.tanh (optimalState Ξ μ ω 1) := by
  simp only [sectionTwoGradientProcess,gradient,mixedGradient,
    AdmissibleCovariance.toEvenMixture_clock,Ξ.clock_one,Paper.parisiGradient_terminal]

/-- All analytic clauses of Lemma 2.2, together with its actual martingale
and endpoint identities. This declaration explicitly omits only the
Hessian stochastic-integral representation. -/
theorem revised_lemma_2_2_analytic_martingale (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) :
    (∀q∈Icc (0:ℝ) 1,∀x, |gradient Ξ μ q x|≤1 ∧
      0<hessian Ξ μ q x ∧ hessian Ξ μ q x≤1-gradient Ξ μ q x^2) ∧
    Martingale (sectionTwoGradientProcess Ξ μ) (sectionTwoGradientFiltration Ξ)
      Paper.canonicalBrownianMeasure ∧
    (∀ω,sectionTwoGradientProcess Ξ μ ⟨0,by norm_num⟩ ω=0 ∧
      sectionTwoGradientProcess Ξ μ ⟨1,by norm_num⟩ ω=Real.tanh (optimalState Ξ μ ω 1)) ∧
    ContDiffOn ℝ 1 (Gamma Ξ μ) (Icc (0:ℝ) 1) ∧ Gamma Ξ μ 0=0 ∧
    (∀q∈Icc (0:ℝ) 1,
      HasDerivWithinAt (Gamma Ξ μ)
        (Ξ.second q*(∫ω,hessian Ξ μ q (optimalState Ξ μ ω q)^2 ∂Paper.canonicalBrownianMeasure))
        (Icc (0:ℝ) 1) q ∧
      0≤derivWithin (Gamma Ξ μ) (Icc (0:ℝ) 1) q ∧
      derivWithin (Gamma Ξ μ) (Icc (0:ℝ) 1) q≤Ξ.second q*(1-Gamma Ξ μ q) ∧
      Gamma Ξ μ q≤Ξ.first q) := by
  refine ⟨?_,sectionTwoGradientProcess_martingale Ξ μ,?_,contDiffOn_Gamma_one Ξ μ,Gamma_zero Ξ μ,?_⟩
  · intro q hq x
    exact ⟨by simpa only [Real.norm_eq_abs] using norm_gradient_le_one Ξ μ q x,
      hessian_pos Ξ μ hq x,hessian_le_one_sub_gradient_sq Ξ μ q x⟩
  · intro ω
    exact ⟨sectionTwoGradientProcess_zero Ξ μ ω,sectionTwoGradientProcess_one Ξ μ ω⟩
  · intro q hq
    have hm : curvatureMoment Ξ μ q=
        ∫ω,hessian Ξ μ q (optimalState Ξ μ ω q)^2 ∂Paper.canonicalBrownianMeasure :=
      mixedCurvatureMoment2_eq_integral Ξ.toEvenMixture 0 μ hq
    refine ⟨?_,?_,?_,Gamma_le_first Ξ μ hq⟩
    · rw [←hm]
      exact hasDerivWithinAt_Gamma Ξ μ hq
    · rw [derivWithin_Gamma Ξ μ hq]
      exact GammaPrime_nonneg Ξ μ hq
    · rw [derivWithin_Gamma Ξ μ hq]
      exact GammaPrime_le Ξ μ hq

end GeneralDepthPaper
