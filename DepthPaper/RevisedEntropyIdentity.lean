module

public import DepthPaper.RevisedEntropyScaling

@[expose] public section

/-! The revised paper's exact finite-atomic diffusion entropy identity. The
temperature derivative is taken for the actual functional, and smoothness
and the terminal-expectation bridge are proved without supplied premises. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace DepthPaper.RevisedCovariance
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 64

def entropyTemperatureFunctional (Ξ : RevisedCovariance) (μ : ParisiMeasure) (m : ℝ) : ℝ :=
  m⁻¹*parisiFunctional ((temperatureCovarianceFamily Ξ).covariance m) μ

theorem contDiffAt_entropyTemperatureFunctional (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) {m : ℝ} (hm : 0 < m) :
    ContDiffAt ℝ ∞ (entropyTemperatureFunctional Ξ (atomicMeasure z hz)) m := by
  have hp := (contDiffAt_temperature_atomicFunctional Ξ z hz hm).comp m
    (contDiffAt_id.prodMk contDiffAt_const)
  have hf : ContDiffAt ℝ ∞ (fun b:ℝ =>
      parisiFunctional ((temperatureCovarianceFamily Ξ).covariance b) (atomicMeasure z hz)) m := by
    convert hp using 1
    funext b
    exact (atomicFunctionalExtension_eq _ z hz).symm
  exact (contDiffAt_id.inv hm.ne').mul hf

theorem contDiffOn_entropyTemperatureFunctional (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) :
    ContDiffOn ℝ ∞ (entropyTemperatureFunctional Ξ (atomicMeasure z hz)) (Ioi (0:ℝ)) := by
  intro m hm
  exact (contDiffAt_entropyTemperatureFunctional Ξ z hz hm).contDiffWithinAt

theorem hasDerivWithinAt_entropyMassMeasure_functional
    (Ξ : RevisedCovariance) (μ : ParisiMeasure) :
    HasDerivWithinAt (fun m => parisiFunctional Ξ (entropyMassMeasure μ m))
      (firstVariation Ξ μ 1 - ∫q : Overlap,firstVariation Ξ μ q ∂(μ : Measure Overlap))
      (Iio (1:ℝ)) 1 := by
  have hd := hasDerivWithinAt_parisiFunctional_mix Ξ μ (Paper.diracOverlap 1 (by norm_num))
  have he : (∫q : Overlap,firstVariation Ξ μ q
      ∂(Paper.diracOverlap 1 (by norm_num) : Measure Overlap))=firstVariation Ξ μ 1 := by
    change (∫q : Overlap,firstVariation Ξ μ q ∂Measure.dirac (⟨1,by norm_num⟩ : Overlap))=_
    rw [integral_dirac]
  rw [he] at hd
  have ha : HasDerivWithinAt (fun m:ℝ=>1-m) (-1) (Iio (1:ℝ)) 1 := by
    convert! ((hasDerivAt_const (1:ℝ) (1:ℝ)).sub
      (hasDerivAt_id (1:ℝ))).hasDerivWithinAt using 1
    norm_num
  have hmap : MapsTo (fun m:ℝ => 1-m) (Iio (1:ℝ)) (Ioi (0:ℝ)) := by
    intro m hm
    change 0 < 1-m
    change m < 1 at hm
    linarith
  have H := hd.comp_of_eq (1:ℝ) ha hmap (by norm_num)
  convert! H using 1 <;> first | rfl | ring

theorem hasDerivAt_entropyTemperatureFunctional (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) :
    HasDerivAt (entropyTemperatureFunctional Ξ (atomicMeasure z hz))
      (firstVariation Ξ (atomicMeasure z hz) 1 -
        (∫q : Overlap,firstVariation Ξ (atomicMeasure z hz) q
          ∂(atomicMeasure z hz : Measure Overlap)) -
        ∫sample,revisedSpinEntropy (optimalState Ξ (atomicMeasure z hz) sample 1)
          ∂Paper.canonicalBrownianMeasure) 1 := by
  let μ := atomicMeasure z hz
  let D := terminalValue (revisedColeHopfRecursionDerivative (r+1) (atomicRecursionData Ξ z)
    logCoshTerminal revisedEntropyTerminalDirection) 0
  have hmass := hasDerivWithinAt_entropyMassMeasure_functional Ξ μ
  have hlog : HasDerivAt (fun m:ℝ=>(m⁻¹-1)*Real.log 2) (-Real.log 2) 1 := by
    convert ((hasDerivAt_inv (by norm_num : (1:ℝ)≠0)).sub_const 1).mul_const (Real.log 2) using 1
    norm_num
  have hterm := hasDerivAt_revisedMass_terminal_difference (r+1)
    (atomicRecursionData Ξ z) (atomicRecursionData_variance_pos Ξ z hz)
  have hsum := (hmass.add hlog.hasDerivWithinAt).add hterm.hasDerivWithinAt
  have hleft : HasDerivWithinAt (entropyTemperatureFunctional Ξ μ)
      (firstVariation Ξ μ 1-(∫q : Overlap,firstVariation Ξ μ q ∂(μ : Measure Overlap))-
        Real.log 2+D) (Iio (1:ℝ)) 1 := by
    apply hsum.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_gt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono
          (nhdsWithin_le_nhds (s:=Iio (1:ℝ)) (a:=1))] with m hm hm0
      rw [entropyTemperatureFunctional,temperatureCovarianceFamily_covariance Ξ m hm0.ne']
      exact temperature_entropyMass_difference Ξ z hz ⟨hm0,hm.le⟩
    · have H := temperature_entropyMass_difference Ξ z hz (m:=1) (by norm_num)
      convert! H using 1 <;> simp only [entropyTemperatureFunctional,
        temperatureCovarianceFamily_one,temperatureScale_one,μ]
  have hdiff : DifferentiableAt ℝ (entropyTemperatureFunctional Ξ μ) 1 :=
    (contDiffAt_entropyTemperatureFunctional Ξ z hz (by norm_num : (0:ℝ)<1)).differentiableAt
      (by simp)
  have hfull := hdiff.hasDerivAt
  apply hfull.congr_deriv
  have he := (hfull.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio (1:ℝ))).symm.trans
    (hleft.derivWithin (uniqueDiffWithinAt_Iio (1:ℝ)))
  rw [entropy_expectation_eq_log_two_sub_derivative Ξ z hz]
  dsimp only [μ,D] at he ⊢
  linarith

theorem entropyTemperatureFunctional_deriv (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) :
    deriv (entropyTemperatureFunctional Ξ (atomicMeasure z hz)) 1 =
      firstVariation Ξ (atomicMeasure z hz) 1 -
        (∫q : Overlap,firstVariation Ξ (atomicMeasure z hz) q
          ∂(atomicMeasure z hz : Measure Overlap)) -
        ∫sample,revisedSpinEntropy (optimalState Ξ (atomicMeasure z hz) sample 1)
          ∂Paper.canonicalBrownianMeasure :=
  (hasDerivAt_entropyTemperatureFunctional Ξ z hz).deriv

end DepthPaper.RevisedCovariance
