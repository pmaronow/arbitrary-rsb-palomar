module

public import DepthPaper.NondegenerateStability
public import DepthPaper.TemperatureFamily
public import DepthPaper.EntropyPressureLimit
public import OverlapPaper.MixedParisiFormula

@[expose] public section


/-! The thermodynamic pressure itself is smooth near temperature one when
the actual finite-step optimizer is nondegenerate. This uses the verified
physical mixed Parisi formula, not a variational identification premise. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
open FourPapersCommon OverlapPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem scaledThermodynamicPressure_eq_temperature_parisiPressure
    (Ξ : AdmissibleCovariance) (b : ℝ) (hb : b≠0) :
    scaledThermodynamicPressure Ξ.toEvenMixture b=
      parisiPressure ((temperatureCovarianceFamily Ξ).covariance b) := by
  rw [scaledThermodynamicPressure,dite_eq_right hb,thermodynamicPressure_eq_mixedPressure]
  rw [temperatureCovarianceFamily_covariance Ξ b hb]
  simp only [parisiPressure,AdmissibleCovariance.toEvenMixture_temperatureScale]

theorem exists_smooth_temperature_pressure (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (hnd : Nondegenerate Ξ z hz) :
    ∃V:Set ℝ,IsOpen V ∧ (1:ℝ)∈V ∧ V⊆Ioi 0 ∧
      ContDiffOn ℝ ∞ (scaledThermodynamicPressure Ξ.toEvenMixture) V := by
  let F:=temperatureCovarianceFamily Ξ
  have hbase : Nondegenerate (F.covariance 1) z hz := by
    simpa only [F,temperatureCovarianceFamily_one] using hnd
  obtain ⟨V,hV,h1V,hVD,zF,hvalue,hsm,hdata⟩:=F.nondegenerate_stability
    (θ:=1) (by norm_num [F,temperatureCovarianceFamily]) z hz hbase
  have hJ : ContDiffOn ℝ ∞
      (fun b=>atomicFunctionalExtension (F.covariance b) r (zF b)) V := by
    apply (F.finite_step_regularity r).comp (contDiffOn_id.prodMk hsm)
    intro b hb
    exact ⟨hVD hb,(hdata b hb).choose⟩
  refine ⟨V,hV,h1V,hVD,?_⟩
  apply hJ.congr
  intro b hb
  have hbp : 0<b := hVD hb
  obtain ⟨hzb,hnb⟩:=hdata b hb
  rw [scaledThermodynamicPressure_eq_temperature_parisiPressure Ξ b hbp.ne',
    atomicFunctionalExtension_eq _ (zF b) hzb]
  have he:=parisiMinimizer_unique (F.covariance b) (atomicMeasure (zF b) hzb) hnb.1
  rw [he,parisiMinimizer_value]

theorem contDiffAt_temperature_pressure (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (hnd : Nondegenerate Ξ z hz) :
    ContDiffAt ℝ ∞ (scaledThermodynamicPressure Ξ.toEvenMixture) 1 := by
  obtain ⟨V,hV,h1V,_,hsm⟩:=exists_smooth_temperature_pressure Ξ z hz hnd
  exact hsm.contDiffAt (hV.mem_nhds h1V)

/-- Literal Proposition 3.2, with the quantitative strict-positive entropy
bound from Appendix C. The expectation is the genuine finite-spin Gibbs
entropy divided by N, and the pressure is its actual thermodynamic limit. -/
theorem positive_entropy (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (hnd : Nondegenerate Ξ z hz) :
    Tendsto (expectedEntropyDensity Ξ.toEvenMixture) atTop
      (𝓝 (thermodynamicEntropy Ξ.toEvenMixture)) ∧
    thermodynamicEntropy Ξ.toEvenMixture=
      scaledThermodynamicPressure Ξ.toEvenMixture 1-
        deriv (scaledThermodynamicPressure Ξ.toEvenMixture) 1 ∧
    0 < thermodynamicEntropy Ξ.toEvenMixture ∧
    ConvexOn ℝ univ (scaledThermodynamicPressure Ξ.toEvenMixture) ∧
    entropyPenalty (4*Ξ.variance)≤thermodynamicEntropy Ξ.toEvenMixture := by
  have hd:=(contDiffAt_temperature_pressure Ξ z hz hnd).differentiableAt (by norm_num)
  exact ⟨tendsto_expectedEntropyDensity_of_differentiable _ hd,rfl,
    thermodynamicEntropy_pos_of_differentiable _ hd,convexOn_scaledThermodynamicPressure _,
    by simpa only [AdmissibleCovariance.toEvenMixture_variance] using
      thermodynamicEntropy_ge_penalty_of_differentiable Ξ.toEvenMixture hd⟩

end DepthPaper
