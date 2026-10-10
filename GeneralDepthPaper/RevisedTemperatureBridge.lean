module

public import GeneralDepthPaper.RevisedBridge
public import GeneralDepthPaper.TemperatureFamily
public import DepthPaper.RevisedTemperatureFamily

@[expose] public section

/-! Exact compatibility of the two finite-covariance interfaces under
physical temperature scaling. The actual probability-measure functional,
pressure, and atomic coordinate functional are retained. -/
noncomputable section
namespace GeneralDepthPaper.AdmissibleCovariance

@[simp] theorem toRevisedCovariance_temperatureScale (Ξ : AdmissibleCovariance)
    (b : ℝ) (hb : b≠0) :
    (Ξ.temperatureScale b hb).toRevisedCovariance=
      Ξ.toRevisedCovariance.temperatureScale b hb := by
  apply Subtype.ext
  change (Ξ.temperatureScale b hb).toEvenMixture=
    Ξ.toEvenMixture.temperatureScale b hb
  exact Ξ.toEvenMixture_temperatureScale b hb

end GeneralDepthPaper.AdmissibleCovariance

namespace GeneralDepthPaper

@[simp] theorem revised_temperature_parisiFunctional (Ξ : AdmissibleCovariance)
    (b : ℝ) (hb : b≠0) :
    DepthPaper.RevisedCovariance.parisiFunctional
      (Ξ.toRevisedCovariance.temperatureScale b hb)=
      parisiFunctional (Ξ.temperatureScale b hb) := by
  rw [←Ξ.toRevisedCovariance_temperatureScale b hb]
  exact revised_parisiFunctional _

@[simp] theorem revised_temperature_parisiPressure (Ξ : AdmissibleCovariance)
    (b : ℝ) (hb : b≠0) :
    DepthPaper.RevisedCovariance.parisiPressure
      (Ξ.toRevisedCovariance.temperatureScale b hb)=
      parisiPressure (Ξ.temperatureScale b hb) := by
  rw [←Ξ.toRevisedCovariance_temperatureScale b hb]
  exact revised_parisiPressure _

@[simp] theorem revised_temperature_atomicFunctionalExtension (Ξ : AdmissibleCovariance)
    (b : ℝ) (hb : b≠0) (r : ℕ) :
    DepthPaper.RevisedCovariance.atomicFunctionalExtension
      (Ξ.toRevisedCovariance.temperatureScale b hb) r=
      atomicFunctionalExtension (Ξ.temperatureScale b hb) r := by
  rw [←Ξ.toRevisedCovariance_temperatureScale b hb]
  exact revised_atomicFunctionalExtension _ _

@[simp] theorem revised_temperature_atomicFunctional (Ξ : AdmissibleCovariance)
    (b : ℝ) (hb : b≠0) {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z) :
    DepthPaper.RevisedCovariance.atomicFunctional
      (Ξ.toRevisedCovariance.temperatureScale b hb) z
      ((revised_isAtomicPoint z).mpr hz)=
      atomicFunctional (Ξ.temperatureScale b hb) z hz := by
  rw [←Ξ.toRevisedCovariance_temperatureScale b hb]
  exact revised_atomicFunctional _ _ _

end GeneralDepthPaper
