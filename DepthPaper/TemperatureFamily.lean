module

public import DepthPaper.SmoothCovarianceFamily
public import FourPapersCommon.MixtureTemperatureScale

set_option backward.privateInPublic true

@[expose] public section


/-! The literal smooth finite-polynomial family b²Ξ, on positive
temperatures, with an exact bridge to the physical mixed model. -/
noncomputable section
open Set
open scoped Topology ContDiff BigOperators
namespace DepthPaper
private theorem mixture_eq_of_coefficient
    (ξ η : FourPapersCommon.AdmissibleEvenMixture) (h : ξ.coefficient=η.coefficient) : ξ=η := by
  cases ξ
  cases η
  simpa only [FourPapersCommon.AdmissibleEvenMixture.mk.injEq] using h

namespace AdmissibleCovariance

def temperatureScale (Ξ : AdmissibleCovariance) (b : ℝ) (hb : b≠0) : AdmissibleCovariance where
  degrees:=Ξ.degrees
  nonempty:=Ξ.nonempty
  coefficient p:=b^2*Ξ.coefficient p
  coefficient_pos p hp:=mul_pos (sq_pos_of_ne_zero hb) (Ξ.coefficient_pos p hp)
  degree_ge_four:=Ξ.degree_ge_four
  degree_even:=Ξ.degree_even

@[simp] theorem temperatureScale_one (Ξ : AdmissibleCovariance) :
    Ξ.temperatureScale 1 one_ne_zero=Ξ := by
  cases Ξ
  simp only [temperatureScale,one_pow,one_mul]

theorem toEvenMixture_temperatureScale (Ξ : AdmissibleCovariance) (b : ℝ) (hb : b≠0) :
    (Ξ.temperatureScale b hb).toEvenMixture=Ξ.toEvenMixture.temperatureScale b hb := by
  apply mixture_eq_of_coefficient
  funext p
  change (if p∈Ξ.degrees then b^2*Ξ.coefficient p else 0)=
    b^2*(if p∈Ξ.degrees then Ξ.coefficient p else 0)
  split_ifs <;> simp

theorem temperatureScale_value (Ξ : AdmissibleCovariance) (b : ℝ) (hb : b≠0) (q : ℝ) :
    (Ξ.temperatureScale b hb).value q=b^2*Ξ.value q := by
  simp only [value,temperatureScale,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  ring

theorem temperatureScale_first (Ξ : AdmissibleCovariance) (b : ℝ) (hb : b≠0) (q : ℝ) :
    (Ξ.temperatureScale b hb).first q=b^2*Ξ.first q := by
  simp only [first,temperatureScale,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  ring

theorem temperatureScale_second (Ξ : AdmissibleCovariance) (b : ℝ) (hb : b≠0) (q : ℝ) :
    (Ξ.temperatureScale b hb).second q=b^2*Ξ.second q := by
  simp only [second,temperatureScale,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  ring

end AdmissibleCovariance

def temperatureCovarianceFamily (Ξ : AdmissibleCovariance) : SmoothCovarianceFamily ℝ where
  domain:=Ioi 0
  isOpen_domain:=isOpen_Ioi
  covariance b:=if hb:b=0 then Ξ else Ξ.temperatureScale b hb
  degrees:=Ξ.degrees
  degrees_eq b hb:=by split_ifs <;> rfl
  smooth_coefficient p hp:=by
    have hc:ContDiffOn ℝ ∞ (fun b:ℝ=>b^2*Ξ.coefficient p) (Ioi 0):=
      (contDiffOn_id.pow 2).mul contDiffOn_const
    apply hc.congr
    intro b hb
    simp only [dite_eq_right (ne_of_gt (show 0<b from hb)),AdmissibleCovariance.temperatureScale]

theorem temperatureCovarianceFamily_covariance (Ξ : AdmissibleCovariance) (b : ℝ) (hb : b≠0) :
    (temperatureCovarianceFamily Ξ).covariance b=Ξ.temperatureScale b hb := by
  simp only [temperatureCovarianceFamily,dite_eq_right hb]

@[simp] theorem temperatureCovarianceFamily_one (Ξ : AdmissibleCovariance) :
    (temperatureCovarianceFamily Ξ).covariance 1=Ξ := by
  rw [temperatureCovarianceFamily_covariance Ξ 1 one_ne_zero,Ξ.temperatureScale_one]

end DepthPaper
