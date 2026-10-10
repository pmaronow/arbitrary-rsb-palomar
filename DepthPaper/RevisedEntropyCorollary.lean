module

public import DepthPaper.RevisedEntropyIdentity
public import DepthPaper.RevisedAtomicStationary
public import DepthPaper.RevisedNondegeneracy
public import DepthPaper.EntropyPressureLimit
public import GeneralDepthPaper.RevisedTemperatureBridge
public import GeneralDepthPaper.NondegeneratePressureSmooth

@[expose] public section

/-! The exact optimized diffusion entropy formula. Differentiability in
the auxiliary envelope lemma is discharged by the proved nondegenerate
pressure theorem in the final general-covariance corollary. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace DepthPaper.RevisedCovariance
open FourPapersCommon OverlapPaper
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 64

theorem scaledPressure_eq_temperature_pressure (Ξ : RevisedCovariance)
    {m : ℝ} (hm : m≠0) :
    scaledThermodynamicPressure Ξ.toEvenMixture m =
      parisiPressure (Ξ.temperatureScale m hm) := by
  rw [scaledThermodynamicPressure,dite_eq_right hm,thermodynamicPressure_eq_mixedPressure]
  rfl

theorem diffusion_entropy_of_pressure_differentiable (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (hmin : IsParisiMinimizer Ξ (atomicMeasure z hz))
    (hp : DifferentiableAt ℝ (scaledThermodynamicPressure Ξ.toEvenMixture) 1) :
    thermodynamicEntropy Ξ.toEvenMixture =
      (∫sample,revisedSpinEntropy (optimalState Ξ (atomicMeasure z hz) sample 1)
        ∂Paper.canonicalBrownianMeasure) - firstVariation Ξ (atomicMeasure z hz) 1 ∧
      0 < thermodynamicEntropy Ξ.toEvenMixture := by
  let μ := atomicMeasure z hz
  let p := scaledThermodynamicPressure Ξ.toEvenMixture
  have hvalue : parisiFunctional Ξ μ = p 1 := by
    dsimp only [p]
    rw [scaledPressure_eq_temperature_pressure Ξ one_ne_zero,temperatureScale_one,
      ←parisiMinimizer_value,←parisiMinimizer_unique Ξ μ hmin]
  have hzero := integral_firstVariation_atomic_minimizer Ξ z hz hmin
  have hfixed := hasDerivAt_entropyTemperatureFunctional Ξ z hz
  rw [hzero,sub_zero] at hfixed
  have hquot : HasDerivAt (fun m:ℝ=>m⁻¹*p m) (deriv p 1-p 1) 1 := by
    convert! (hasDerivAt_inv (by norm_num : (1:ℝ)≠0)).mul hp.hasDerivAt using 1
    norm_num
    ring
  have hlocal : IsLocalMin (fun m:ℝ=>entropyTemperatureFunctional Ξ μ m-m⁻¹*p m) 1 := by
    filter_upwards [eventually_gt_nhds (show (0:ℝ)<1 by norm_num)] with m hm
    have hpres : p m = parisiPressure ((temperatureCovarianceFamily Ξ).covariance m) := by
      rw [temperatureCovarianceFamily_covariance Ξ m hm.ne']
      exact scaledPressure_eq_temperature_pressure Ξ hm.ne'
    have hle : p m ≤ parisiFunctional ((temperatureCovarianceFamily Ξ).covariance m) μ := by
      rw [hpres,←parisiMinimizer_value]
      exact isParisiMinimizer_selected _ μ
    change entropyTemperatureFunctional Ξ μ 1-(1:ℝ)⁻¹*p 1≤_
    simp only [entropyTemperatureFunctional,temperatureCovarianceFamily_one,
      inv_one,one_mul,hvalue,sub_self]
    exact sub_nonneg.mpr (mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hm.le))
  have he := hlocal.hasDerivAt_eq_zero (hfixed.sub hquot)
  have hent : thermodynamicEntropy Ξ.toEvenMixture =
      (∫sample,revisedSpinEntropy (optimalState Ξ μ sample 1)
        ∂Paper.canonicalBrownianMeasure)-firstVariation Ξ μ 1 := by
    change p 1-deriv p 1=_
    linarith
  refine ⟨hent,?_⟩
  have hs := spinEntropy_expectation_pos Ξ μ
  have hf := (atomic_minimizer_contacts Ξ z hz hmin).1 1 (by norm_num)
  rw [hent]
  linarith

end DepthPaper.RevisedCovariance

namespace GeneralDepthPaper
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 64

/-- Exact revised Corollary 3.3 on the general finite covariance backend.
The internal nondegeneracy predicate is used only to invoke its proved
pressure smoothness; the revised paper predicate is transferred separately. -/
theorem diffusion_entropy (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (hnd : Nondegenerate Ξ z hz) :
    DepthPaper.thermodynamicEntropy Ξ.toEvenMixture =
      (∫sample,DepthPaper.revisedSpinEntropy (optimalState Ξ (atomicMeasure z hz) sample 1)
        ∂Paper.canonicalBrownianMeasure) - firstVariation Ξ (atomicMeasure z hz) 1 ∧
      0 < DepthPaper.thermodynamicEntropy Ξ.toEvenMixture := by
  have hmin : DepthPaper.RevisedCovariance.IsParisiMinimizer Ξ.toRevisedCovariance
      (DepthPaper.atomicMeasure z ((revised_isAtomicPoint z).mpr hz)) := by
    rw [revised_atomicMeasure,revised_isParisiMinimizer]
    exact hnd.1
  have hp : DifferentiableAt ℝ (DepthPaper.scaledThermodynamicPressure
      Ξ.toRevisedCovariance.toEvenMixture) 1 := by
    rw [AdmissibleCovariance.toRevisedCovariance_toEvenMixture]
    change DifferentiableAt ℝ (scaledThermodynamicPressure Ξ.toEvenMixture) 1
    exact (contDiffAt_temperature_pressure Ξ z hz hnd).differentiableAt (by simp)
  have H := DepthPaper.RevisedCovariance.diffusion_entropy_of_pressure_differentiable
    Ξ.toRevisedCovariance z ((revised_isAtomicPoint z).mpr hz) hmin hp
  convert! H using 1

/-- Literal revised Corollary 3.3, with the paper's subcritical covariance
and nondegenerate finite atomic minimizer. Positive definiteness is proved
from these conditions before invoking pressure smoothness. -/
theorem revised_diffusion_entropy (Ξ : AdmissibleCovariance) (hsub : Ξ.IsSubcritical)
    {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (hnd : DepthPaper.RevisedCovariance.Nondegenerate Ξ.toRevisedCovariance z
      ((revised_isAtomicPoint z).mpr hz)) :
    DepthPaper.thermodynamicEntropy Ξ.toEvenMixture =
      (∫sample,DepthPaper.revisedSpinEntropy (optimalState Ξ (atomicMeasure z hz) sample 1)
        ∂Paper.canonicalBrownianMeasure) - firstVariation Ξ (atomicMeasure z hz) 1 ∧
      0 < DepthPaper.thermodynamicEntropy Ξ.toEvenMixture := by
  have hhess := DepthPaper.RevisedCovariance.positiveAtomicHessian_of_nondegenerate
    Ξ.toRevisedCovariance z ((revised_isAtomicPoint z).mpr hz) hnd
  have hgeneral := nondegenerate_of_revised_data Ξ z hz hnd.1 hnd.2.1 hnd.2.2 hhess hsub
  exact diffusion_entropy Ξ z hz hgeneral

end GeneralDepthPaper
