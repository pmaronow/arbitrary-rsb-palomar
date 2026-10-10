module

public import GeneralDepthPaper.RevisedCovarianceBridge

@[expose] public section

/-! A finite-support common covariance has an exact finite coefficient
presentation. This inverse interface adds no mathematical restrictions and
retains the genuine mixed-model backend. -/
noncomputable section
namespace DepthPaper.RevisedCovariance

private theorem mixture_eq_of_coefficient
    (ξ η : FourPapersCommon.AdmissibleEvenMixture) (h : ξ.coefficient=η.coefficient) : ξ=η := by
  cases ξ
  cases η
  simpa only [FourPapersCommon.AdmissibleEvenMixture.mk.injEq] using h

def toGeneralCovariance (Ξ : RevisedCovariance) : GeneralDepthPaper.AdmissibleCovariance where
  degrees := Ξ.degrees
  nonempty := Ξ.nonempty
  coefficient := Ξ.coefficient
  coefficient_pos := Ξ.coefficient_pos
  degree_ge_two := Ξ.degree_ge_two
  degree_even := Ξ.degree_even

@[simp] theorem toGeneralCovariance_toEvenMixture (Ξ : RevisedCovariance) :
    Ξ.toGeneralCovariance.toEvenMixture=Ξ.toEvenMixture := by
  apply mixture_eq_of_coefficient
  funext p
  change (if p∈Ξ.degrees then Ξ.coefficient p else 0)=Ξ.coefficient p
  split_ifs with hp
  · rfl
  · have hzero : Ξ.coefficient p=0 := by
      simpa only [mem_degrees,not_not] using hp
    exact hzero.symm

@[simp] theorem toGeneralCovariance_toRevisedCovariance (Ξ : RevisedCovariance) :
    Ξ.toGeneralCovariance.toRevisedCovariance=Ξ := by
  apply Subtype.ext
  exact Ξ.toGeneralCovariance_toEvenMixture

end DepthPaper.RevisedCovariance
