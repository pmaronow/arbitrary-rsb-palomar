module

public import DepthPaper.CutoffTerminalApproximation
public import DepthPaper.CutoffDeficitRepresentation
public import DepthPaper.CutoffComparisonState

@[expose] public section


/-! Literal cutoff-splitting Lemma 4.1. The statement uses the actual
high-degree covariance, actual two-level probability measure, actual
selected potential/diffusion and genuine truncated data. Parameter partials
are ordered genuine directional derivatives; at m=1 the smooth extension
agrees with the required one-sided derivatives. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff NNReal BigOperators
namespace DepthPaper
open ColeHopfFoundation.ProbabilityTheory
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 64

theorem terminalDoobPotential_terminal_deriv (m:ℝ) (W:ℝ≥0) (x:ℝ) :
    deriv (terminalDoobPotential m W W) x=Real.tanh x := by
  have he:terminalDoobPotential m W W=(fun y=>Real.log (Real.cosh y)) := by
    funext y
    simp only [terminalDoobPotential,tsub_self,coleHopf_zero_var]
  rw [he]
  exact (Paper.hasDerivAt_log_cosh x).deriv

structure CutoffSplittingAt (Ξ base:AdmissibleCovariance) {r:ℕ}
    (z:AtomicPoint r) (hz:IsAtomicPoint z) (m:ℝ) (hm:m∈Ioc (0:ℝ) 1)
    (Q:Overlap) (qc:ℝ) (hc:atomicLocation z (Fin.last r) < qc)
    (hqcQ:qc < (Q:ℝ)) : Prop where
  terminal_identity : ∀x,
    potential Ξ (twoLevelMeasure z hz m Q) qc x=
      cutoffCandidateConstant Ξ m Q qc+
        terminalValue (cutoffTerminal m (Ξ.first Q-Ξ.first qc)) x
  below_potential : ∀q∈Icc (0:ℝ) qc,∀x,
    potential Ξ (twoLevelMeasure z hz m Q) q x-cutoffCandidateConstant Ξ m Q qc=
      (cutoffCandidateData Ξ z hz m ⟨hm.1.le,hm.2⟩ Q qc hc hqcQ.le).potential q x
  below_state_law :
    Paper.canonicalBrownianMeasure.map
      (cutoffTruncatedStatePath Ξ z hz m ⟨hm.1.le,hm.2⟩ Q qc hc hqcQ.le)=
    Paper.canonicalBrownianMeasure.map (cutoffOptimalStatePath Ξ z hz m Q qc)
  below_firstVariation : ∀q∈Icc (0:ℝ) qc,
    firstVariation Ξ (twoLevelMeasure z hz m Q) q=
      (cutoffCandidateData Ξ z hz m ⟨hm.1.le,hm.2⟩ Q qc hc hqcQ.le).firstVariation q
  comparison_potential : ∀q∈Icc (0:ℝ) qc,∀x,
    (cutoffComparisonData base z hz m ⟨hm.1.le,hm.2⟩ qc hc).potential q x=
      temperatureMassPotential base (atomicMeasure z hz) m qc q x
  comparison_firstVariation : ∀q∈Icc (0:ℝ) qc,
    (cutoffComparisonData base z hz m ⟨hm.1.le,hm.2⟩ qc hc).firstVariation q=
      (m^2)⁻¹*firstVariation ((temperatureCovarianceFamily base).covariance m)
        (atomicMeasure z hz) q
  deficit : ∀q∈Ioc qc (Q:ℝ),
    1-Gamma Ξ (twoLevelMeasure z hz m Q) q=
      ∫x,∫y,1-(deriv (terminalDoobPotential m (Ξ.first Q-Ξ.first qc).toNNReal
        (Ξ.first q-Ξ.first qc).toNNReal) y)^2
        ∂terminalDoobMeasure m (Ξ.first Q-Ξ.first qc).toNNReal
          (Ξ.first q-Ξ.first qc).toNNReal x
        ∂(Paper.canonicalBrownianMeasure.map
          (fun sample=>optimalState Ξ (twoLevelMeasure z hz m Q) sample qc))
  endpoint_deficit :
    1-Gamma Ξ (twoLevelMeasure z hz m Q) Q=
      ∫x,∫y,Paper.sech y^2
        ∂terminalDoobMeasure m (Ξ.first Q-Ξ.first qc).toNNReal
          (Ξ.first Q-Ξ.first qc).toNNReal x
        ∂(Paper.canonicalBrownianMeasure.map
          (fun sample=>optimalState Ξ (twoLevelMeasure z hz m Q) sample qc))

theorem cutoff_splitting_at (Ξ base:AdmissibleCovariance) {r:ℕ}
    (z:AtomicPoint r) (hz:IsAtomicPoint z) (m:ℝ) (hm:m∈Ioc (0:ℝ) 1)
    (Q:Overlap) (qc:ℝ) (hc:atomicLocation z (Fin.last r) < qc)
    (hqcQ:qc < (Q:ℝ)) : CutoffSplittingAt Ξ base z hz m hm Q qc hc hqcQ := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact potential_twoLevelMeasure_at_cutoff Ξ z hz m ⟨hm.1.le,hm.2⟩ Q qc hc hqcQ.le
  · exact potential_twoLevelMeasure_eq_cutoff Ξ z hz m ⟨hm.1.le,hm.2⟩ Q qc hc hqcQ.le
  · exact cutoff_truncated_state_path_law Ξ z hz m ⟨hm.1.le,hm.2⟩ Q qc hc hqcQ.le
  · exact firstVariation_twoLevelMeasure_eq_cutoff Ξ z hz m ⟨hm.1.le,hm.2⟩ Q qc hc hqcQ.le
  · exact potential_cutoffComparisonData base z hz m hm qc hc
      (hqcQ.le.trans Q.property.2)
  · exact firstVariation_cutoffComparisonData base z hz m hm qc hc
      (hqcQ.le.trans Q.property.2)
  · exact cutoff_deficit_representation Ξ z hz m ⟨hm.1.le,hm.2⟩ Q qc hc
  · have hh:=cutoff_deficit_representation Ξ z hz m ⟨hm.1.le,hm.2⟩ Q qc hc Q
      ⟨hqcQ,le_rfl⟩
    simp_rw [terminalDoobPotential_terminal_deriv] at hh
    have hs:∀y:ℝ,1-(Real.tanh y)^2=Paper.sech y^2 := by
      intro y
      linarith [Paper.tanh_sq_add_sech_sq y]
    simpa only [hs] using hh

end DepthPaper
