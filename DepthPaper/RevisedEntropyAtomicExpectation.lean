module

public import DepthPaper.RevisedEntropyExpectation
public import DepthPaper.RevisedAtomicRegularity
public import FourPapersCommon.MixedFiniteDiffusionLaw

@[expose] public section

/-! The exact terminal derivative and entropy expectation for the positive
atomic chart, using the actual covariance and the actual optimal diffusion. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ContDiff
namespace DepthPaper.RevisedCovariance
open FourPapersCommon
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 64

theorem entropyTerminalDerivative_eq_expectation (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) :
    terminalValue (revisedColeHopfRecursionDerivative (r+1) (atomicRecursionData Ξ z)
      logCoshTerminal revisedEntropyTerminalDirection) 0 =
    ∫ sample, terminalValue revisedEntropyTerminalDirection
      (optimalState Ξ (atomicMeasure z hz) sample 1) ∂Paper.canonicalBrownianMeasure := by
  have H := revisedEntropy_grid_terminal_expectation Ξ.toEvenMixture 0 (atomicMeasure z hz)
    (r+1) (atomicNode z) (atomicRecursionData Ξ z)
    (atomicNode_mem_unit z hz)
    (fun i => (atomicNode_strictMono z hz) i.castSucc_lt_succ)
    (atomicRecursionData_variance_pos Ξ z hz)
    (fun i => by simp only [atomicRecursionData,toEvenMixture_first])
    (fun i s hs => parisiCDF_atomicMeasure_cell z hz i hs)
    logCoshTerminal revisedEntropyTerminalDirection
    (fun x => by rw [atomicNode_last,mixedPotential_terminal,terminalValue_logCoshTerminal])
    (Real.log 2) norm_revisedEntropyTerminalDirection_le_log_two
  simp only [atomicNode_last,atomicNode_zero,mixedState_initial,integral_const,
    probReal_univ,one_smul] at H
  exact H.symm

theorem integrable_entropyTerminalDirection (Ξ : RevisedCovariance) (μ : ParisiMeasure) :
    Integrable (fun sample => terminalValue revisedEntropyTerminalDirection
      (optimalState Ξ μ sample 1)) Paper.canonicalBrownianMeasure := by
  apply Integrable.of_bound
    (((contDiff_terminalValue revisedEntropyTerminalDirection).continuous.measurable.comp
      (measurable_mixedState Ξ.toEvenMixture 0 μ (by norm_num))).aestronglyMeasurable)
    (Real.log 2)
  exact Eventually.of_forall fun sample => norm_revisedEntropyTerminalDirection_le_log_two _

theorem entropy_expectation_eq_log_two_sub_derivative (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) :
    (∫ sample, revisedSpinEntropy (optimalState Ξ (atomicMeasure z hz) sample 1)
      ∂Paper.canonicalBrownianMeasure) = Real.log 2 -
      terminalValue (revisedColeHopfRecursionDerivative (r+1) (atomicRecursionData Ξ z)
        logCoshTerminal revisedEntropyTerminalDirection) 0 := by
  simp_rw [revisedSpinEntropy_eq_terminalDirection]
  rw [integral_sub (integrable_const _) (integrable_entropyTerminalDirection Ξ _),
    integral_const,probReal_univ,one_smul,entropyTerminalDerivative_eq_expectation Ξ z hz]

theorem integrable_spinEntropy (Ξ : RevisedCovariance) (μ : ParisiMeasure) :
    Integrable (fun sample => revisedSpinEntropy (optimalState Ξ μ sample 1))
      Paper.canonicalBrownianMeasure := by
  simp_rw [revisedSpinEntropy_eq_terminalDirection]
  exact (integrable_const _).sub (integrable_entropyTerminalDirection Ξ μ)

theorem spinEntropy_expectation_pos (Ξ : RevisedCovariance) (μ : ParisiMeasure) :
    0 < ∫ sample, revisedSpinEntropy (optimalState Ξ μ sample 1)
      ∂Paper.canonicalBrownianMeasure := by
  apply integral_pos_iff_support_of_nonneg (fun _ => (revisedSpinEntropy_pos _).le)
    (integrable_spinEntropy Ξ μ) |>.2
  have hs : Function.support (fun sample => revisedSpinEntropy (optimalState Ξ μ sample 1)) =
      Set.univ := by
    ext sample
    simp only [Function.mem_support,Set.mem_univ,iff_true]
    exact (revisedSpinEntropy_pos _).ne'
  rw [hs]
  simp

end DepthPaper.RevisedCovariance
