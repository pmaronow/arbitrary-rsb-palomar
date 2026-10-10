module

public import GeneralDepthPaper.CutoffSplitting
public import GeneralDepthPaper.DoobScaledSechBounds
public import DepthPaper.RevisedDoobComparison
public import DepthPaper.RevisedDoobKernel

@[expose] public section

/-! Exact truncated-data and conditional-kernel statements in revised
Appendix B.2–B.3. The identities hold for arbitrary finite covariance and
valid two-level candidate data, hence for every candidate in Section 4. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace GeneralDepthPaper
open FourPapersCommon ColeHopfFoundation.ProbabilityTheory
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 64

/-- The exact finite-variance Doob kernel, with terminal potential at elapsed time t. -/
def revisedCutoffKernel (m : ℝ) (W t : ℝ≥0) : Kernel ℝ ℝ :=
  FRSB.constantMassKernel m t (terminalDoobPotential m W t)

theorem continuous_revisedCutoffPotential (m : ℝ) (W t : ℝ≥0) :
    Continuous (terminalDoobPotential m W t) := by
  change Continuous (fun x => coleHopf m (W-t) (fun y => Real.log (Real.cosh y)) x)
  simpa only [Real.toNNReal_coe, Function.comp_def, id_eq] using
    (continuous_coleHopf (Real.continuous_cosh.log (fun y => (Real.cosh_pos y).ne'))
      hasLinearGrowth_logCosh m).comp
        (continuous_id.prodMk (continuous_const (y := ((W-t : ℝ≥0) : ℝ))))

theorem revisedCutoffKernel_apply (m : ℝ) (W t : ℝ≥0) (ht : t ≤ W) (x : ℝ) :
    revisedCutoffKernel m W t x = terminalDoobMeasure m W t x := by
  rw [revisedCutoffKernel, FRSB.constantMassKernel_apply m t _
    (continuous_revisedCutoffPotential m W t)
    (HasLinearGrowth.of_lipschitz (terminalDoobPotential_lipschitz m W t))]
  exact (terminalDoobMeasure_eq_constantMass m W t ht x).symm

/-- Revised B.2: all three truncated problems, with their actual selected fields.
The selected and truncated state paths have the same law; the displayed
additive-state identity also specifies their original-clock realization. -/
theorem revised_below_cutoff (Ψ Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m ∈ Ioc (0 : ℝ) 1)
    (Q : Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r) < qc)
    (hqcQ : qc < (Q : ℝ)) :
    (∀ q ∈ Icc (0 : ℝ) qc, ∀ x,
      potential Ψ (twoLevelMeasure z hz m Q) q x =
        cutoffCandidateConstant Ψ m Q qc +
          (cutoffCandidateData Ψ z hz m ⟨hm.1.le, hm.2⟩ Q qc hc hqcQ.le).potential q x) ∧
    (Paper.canonicalBrownianMeasure.map
      (cutoffTruncatedStatePath Ψ z hz m ⟨hm.1.le, hm.2⟩ Q qc hc hqcQ.le) =
      Paper.canonicalBrownianMeasure.map (cutoffOptimalStatePath Ψ z hz m Q qc)) ∧
    (∀ sample, cutoffOptimalStatePath Ψ z hz m Q qc sample =
      additiveStatePath (cutoffCandidateData Ψ z hz m ⟨hm.1.le, hm.2⟩ Q qc hc hqcQ.le).driftData
        0 qc (cutoff_pos z hz qc hc).le
        (rescaledClockBrownianPath (mixedBeta Ψ.toEvenMixture)
          (cutoffCovarianceClock Ψ qc) sample)) ∧
    (∀ q ∈ Icc (0 : ℝ) qc,
      firstVariation Ψ (twoLevelMeasure z hz m Q) q =
        (cutoffCandidateData Ψ z hz m ⟨hm.1.le, hm.2⟩ Q qc hc hqcQ.le).firstVariation q) ∧
    ((cutoffComparisonData Ψ z hz m ⟨hm.1.le, hm.2⟩ qc hc).potential 0 0 =
      m⁻¹ * potential ((temperatureCovarianceFamily Ψ).covariance m) (atomicMeasure z hz) 0 0 -
        m / 2 * (Ψ.first 1 - Ψ.first qc)) ∧
    (∀ q ∈ Icc (0 : ℝ) qc,
      (cutoffComparisonData Ξ z hz m ⟨hm.1.le, hm.2⟩ qc hc).firstVariation q =
        (m^2)⁻¹ * firstVariation ((temperatureCovarianceFamily Ξ).covariance m)
          (atomicMeasure z hz) q) := by
  have H := cutoff_splitting_at Ψ Ξ z hz m hm Q qc hc hqcQ
  refine ⟨?_, H.below_state_law, ?_, H.below_firstVariation, ?_, H.comparison_firstVariation⟩
  · intro q hq x
    have h := H.below_potential q hq x
    linarith
  · exact cutoffOptimalStatePath_eq_additive Ψ z hz m ⟨hm.1.le, hm.2⟩ Q qc hc hqcQ.le
  · have h := potential_cutoffComparisonData Ψ z hz m hm qc hc
      (hqcQ.le.trans Q.property.2) 0 ⟨le_rfl, (cutoff_pos z hz qc hc).le⟩ 0
    simpa only [temperatureMassPotential, mul_zero] using h

/-- Revised B.3: the kernel is a conditional transition law, expressed for
every event measurable at the cutoff time, rather than only the marginal law. -/
theorem revised_cutoff_conditional_law (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m ∈ Icc (0 : ℝ) 1)
    (Q : Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r) < qc)
    (q : ℝ) (hq : q ∈ Ioc qc (Q : ℝ))
    (E : Set BrownianSample)
    (hE : MeasurableSet[Paper.canonicalBrownianFiltration (Ξ.clock qc).toNNReal] E) :
    (Paper.canonicalBrownianMeasure.restrict E).map
        (fun sample => optimalState Ξ (twoLevelMeasure z hz m Q) sample q) =
      revisedCutoffKernel m (Ξ.first Q - Ξ.first qc).toNNReal
        (Ξ.first q - Ξ.first qc).toNNReal ∘ₘ
          (Paper.canonicalBrownianMeasure.restrict E).map
            (fun sample => optimalState Ξ (twoLevelMeasure z hz m Q) sample qc) := by
  have hc0 := (cutoff_pos z hz qc hc).le
  have hcU : qc ∈ Icc (0 : ℝ) 1 := ⟨hc0, (hq.1.le.trans hq.2).trans Q.property.2⟩
  have hqU : q ∈ Icc (0 : ℝ) 1 := ⟨hc0.trans hq.1.le, hq.2.trans Q.property.2⟩
  have ht : (Ξ.first q - Ξ.first qc).toNNReal ≤ (Ξ.first Q - Ξ.first qc).toNNReal := by
    apply Real.toNNReal_mono
    have hh := Ξ.first_strictMonoOn.monotoneOn hqU.1 Q.property.1 hq.2
    linarith
  have hk : mixedScalarTransition Ξ.toEvenMixture (twoLevelMeasure z hz m Q) qc q m =
      revisedCutoffKernel m (Ξ.first Q - Ξ.first qc).toNNReal
        (Ξ.first q - Ξ.first qc).toNNReal := by
    apply Kernel.ext
    intro x
    rw [revisedCutoffKernel_apply _ _ _ ht]
    exact mixedScalarTransition_twoLevel_eq_terminalDoob Ξ z hz m hm Q qc hc q hq x
  have H := mixedState_constantMass_restricted_transitionLaw Ξ.toEvenMixture 0
    (twoLevelMeasure z hz m Q) hcU hqU hq.1
    (fun s hs => parisiCDF_twoLevelMeasure_middle z hz m hm Q s
      ⟨hc.le.trans hs.1, hs.2.trans_le hq.2⟩) E
    (by
      rw [AdmissibleCovariance.toEvenMixture_clock]
      exact hE)
  rw [hk] at H
  exact H

/-- Revised B.3: the printed expectation at the actual selected state. -/
theorem revised_cutoff_deficit_expectation (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m ∈ Icc (0 : ℝ) 1)
    (Q : Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r) < qc)
    (q : ℝ) (hq : q ∈ Icc qc (Q : ℝ)) :
    1 - Gamma Ξ (twoLevelMeasure z hz m Q) q =
      ∫ sample, 1 - (deriv (terminalDoobPotential m (Ξ.first Q - Ξ.first qc).toNNReal
        (Ξ.first q - Ξ.first qc).toNNReal)
          (optimalState Ξ (twoLevelMeasure z hz m Q) sample q))^2
            ∂Paper.canonicalBrownianMeasure := by
  let μ := twoLevelMeasure z hz m Q
  have hqU : q ∈ Icc (0 : ℝ) 1 :=
    ⟨(cutoff_pos z hz qc hc).le.trans hq.1, hq.2.trans Q.property.2⟩
  have hg : Measurable (fun sample => gradient Ξ μ q (optimalState Ξ μ sample q)) := by
    change Measurable (fun sample => Paper.parisiGradient (mixedBeta Ξ.toEvenMixture)
      (mixedMeasure Ξ.toEvenMixture μ) (Ξ.toEvenMixture.clock q, mixedState Ξ.toEvenMixture 0 μ sample q))
    exact (Paper.continuous_parisiGradient _ _).measurable.comp
      (measurable_const.prodMk (measurable_mixedState Ξ.toEvenMixture 0 μ hqU))
  have hi : Integrable (fun sample => gradient Ξ μ q (optimalState Ξ μ sample q)^2)
      Paper.canonicalBrownianMeasure := by
    apply (integrable_const (1 : ℝ)).mono' (hg.pow_const 2).aestronglyMeasurable
    exact .of_forall fun sample => by
      rw [norm_pow]
      have hh := norm_gradient_le_one Ξ μ q (optimalState Ξ μ sample q)
      nlinarith [norm_nonneg (gradient Ξ μ q (optimalState Ξ μ sample q))]
  simp_rw [← gradient_twoLevelMeasure_top_derivative Ξ z hz m hm Q qc hc q hq]
  change 1 - (∫ sample, gradient Ξ μ q (optimalState Ξ μ sample q)^2
    ∂Paper.canonicalBrownianMeasure) = _
  rw [integral_sub (integrable_const (1 : ℝ)) hi, integral_const]
  simp

/-- Revised B.3 at the top endpoint, where the terminal gradient is tanh. -/
theorem revised_cutoff_endpoint_expectation (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m ∈ Icc (0 : ℝ) 1)
    (Q : Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r) < qc)
    (hqcQ : qc ≤ (Q : ℝ)) :
    1 - Gamma Ξ (twoLevelMeasure z hz m Q) Q =
      ∫ sample, Paper.sech (optimalState Ξ (twoLevelMeasure z hz m Q) sample Q)^2
        ∂Paper.canonicalBrownianMeasure := by
  have H := revised_cutoff_deficit_expectation Ξ z hz m hm Q qc hc Q ⟨hqcQ, le_rfl⟩
  simp_rw [terminalDoobPotential_terminal_deriv] at H
  have he (x : ℝ) : 1 - Real.tanh x^2 = Paper.sech x^2 := by
    linarith [Paper.tanh_sq_add_sech_sq x]
  simpa only [he] using H


/-- The transition kernel in B.3 has exactly the printed Gaussian
h-transform density, with the finite-horizon Cole--Hopf potential. -/
theorem revisedCutoffKernel_density (m:ℝ) (W t:ℝ≥0) (ht:0<t) (htW:t≤W) (x:ℝ) :
    revisedCutoffKernel m W t x=volume.withDensity (fun y=>ENNReal.ofReal
      (gaussianPDFReal x t y*Real.exp (m*terminalDoobPotential m W t y)/
        Real.exp (m*terminalDoobPotential m W 0 x))) := by
  rw [revisedCutoffKernel_apply m W t htW x]
  change DepthPaper.terminalDoobMeasure m W t x=volume.withDensity (fun y=>ENNReal.ofReal
    (gaussianPDFReal x t y*Real.exp (m*DepthPaper.terminalDoobPotential m W t y)/
      Real.exp (m*DepthPaper.terminalDoobPotential m W 0 x)))
  rw [DepthPaper.terminalDoobMeasure_eq_density m W t ht x]
  congr 1
  funext y
  rw [DepthPaper.terminalDoobDensity_explicit]

end GeneralDepthPaper
