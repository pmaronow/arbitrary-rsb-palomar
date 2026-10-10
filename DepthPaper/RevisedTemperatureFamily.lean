module

public import DepthPaper.RevisedSmoothCovarianceFamily

@[expose] public section

/-! The literal all-positive-temperature family b²ξ and joint smoothness
of its actual finite atomic functional, including quadratic interactions. -/
noncomputable section
open Set
open scoped Topology ContDiff BigOperators
namespace DepthPaper.RevisedCovariance

private theorem mixture_eq_of_coefficient
    (ξ η : FourPapersCommon.AdmissibleEvenMixture) (h : ξ.coefficient=η.coefficient) : ξ=η := by
  cases ξ
  cases η
  simpa only [FourPapersCommon.AdmissibleEvenMixture.mk.injEq] using h

@[simp] theorem temperatureScale_coefficient (Ξ : RevisedCovariance) (b : ℝ) (hb : b≠0)
    (p : ℕ) : (Ξ.temperatureScale b hb).coefficient p=b^2*Ξ.coefficient p := rfl

@[simp] theorem temperatureScale_degrees (Ξ : RevisedCovariance) (b : ℝ) (hb : b≠0) :
    (Ξ.temperatureScale b hb).degrees=Ξ.degrees := by
  ext p
  rw [mem_degrees,mem_degrees,temperatureScale_coefficient]
  exact mul_ne_zero_iff_left (pow_ne_zero 2 hb)

@[simp] theorem temperatureScale_one (Ξ : RevisedCovariance) :
    Ξ.temperatureScale 1 one_ne_zero=Ξ := by
  apply Subtype.ext
  have he : (Ξ.toEvenMixture.temperatureScale 1 one_ne_zero).coefficient=
      Ξ.toEvenMixture.coefficient := by
    funext p
    simp only [FourPapersCommon.AdmissibleEvenMixture.temperatureScale_coefficient,
      one_pow,one_mul]
  exact mixture_eq_of_coefficient _ _ he

def temperatureCovarianceFamily (Ξ : RevisedCovariance) : SmoothCovarianceFamily ℝ where
  domain := Ioi 0
  isOpen_domain := isOpen_Ioi
  covariance b := if hb:b=0 then Ξ else Ξ.temperatureScale b hb
  degrees := Ξ.degrees
  degrees_eq b hb := by split_ifs <;> simp
  smooth_coefficient p hp := by
    have hc : ContDiffOn ℝ ∞ (fun b:ℝ=>b^2*Ξ.coefficient p) (Ioi 0) :=
      (contDiffOn_id.pow 2).mul contDiffOn_const
    apply hc.congr
    intro b hb
    simp only [dite_eq_right (ne_of_gt (show 0<b from hb)),temperatureScale_coefficient]

theorem temperatureCovarianceFamily_covariance (Ξ : RevisedCovariance) (b : ℝ) (hb : b≠0) :
    (temperatureCovarianceFamily Ξ).covariance b=Ξ.temperatureScale b hb := by
  simp only [temperatureCovarianceFamily,dite_eq_right hb]

@[simp] theorem temperatureCovarianceFamily_one (Ξ : RevisedCovariance) :
    (temperatureCovarianceFamily Ξ).covariance 1=Ξ := by
  rw [temperatureCovarianceFamily_covariance Ξ 1 one_ne_zero,temperatureScale_one]

theorem contDiffAt_temperature_atomicFunctional (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) {b : ℝ} (hb : 0<b) :
    ContDiffAt ℝ ∞ (fun w:ℝ×AtomicPoint r=>
      atomicFunctionalExtension ((temperatureCovarianceFamily Ξ).covariance w.1) r w.2) (b,z) :=
  ((temperatureCovarianceFamily Ξ).finite_step_regularity r).contDiffAt
    ((isOpen_Ioi.prod (isOpen_atomic_domain r)).mem_nhds ⟨hb,hz⟩)

theorem temperatureScale_isSubcritical_of_mass (Ξ : RevisedCovariance)
    (hsub : Ξ.IsSubcritical) {b : ℝ} (hb : b∈Ioc (0:ℝ) 1) :
    (Ξ.temperatureScale b hb.1.ne').IsSubcritical := by
  change (Ξ.temperatureScale b hb.1.ne').second 0<1
  rw [temperatureScale_second]
  have hbsq : b^2≤1 := by nlinarith [hb.1,hb.2]
  have hn : 0≤Ξ.second 0 := Ξ.second_nonneg le_rfl
  exact (mul_le_mul_of_nonneg_right hbsq hn |>.trans_eq (one_mul _)).trans_lt hsub

theorem eventually_temperatureScale_isSubcritical (Ξ : RevisedCovariance)
    (hsub : Ξ.IsSubcritical) :
    ∀ᶠb:ℝ in nhds 1,∀hb:b≠0,(Ξ.temperatureScale b hb).IsSubcritical := by
  change Ξ.second 0<1 at hsub
  have hc : ContinuousAt (fun b:ℝ=>b^2*Ξ.second 0) 1 :=
    (continuousAt_id.pow 2).mul continuousAt_const
  have hs : (1:ℝ)^2*Ξ.second 0<1 := by simpa only [one_pow,one_mul] using hsub
  filter_upwards [hc.eventually (eventually_lt_nhds hs)] with b hb hn
  change (Ξ.temperatureScale b hn).second 0<1
  simpa only [temperatureScale_second] using hb

end DepthPaper.RevisedCovariance
