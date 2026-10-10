module

public import GeneralDepthPaper.CovarianceBridge
public import DepthPaper.RevisedCovariance
public import GeneralDepthPaper.Model
public import DepthPaper.RevisedModel

@[expose] public section

/-! Exact embedding of the general finite coefficient datatype into the
finite-support common-mixture datatype. Inactive coefficients are removed
exactly as in the genuine mixed-model backend. -/
noncomputable section
open Set
namespace GeneralDepthPaper.AdmissibleCovariance

def toRevisedCovariance (Ξ : AdmissibleCovariance) : DepthPaper.RevisedCovariance :=
  ⟨Ξ.toEvenMixture, Ξ.degrees.finite_toSet.subset (by
    intro p hp
    by_contra hn
    change Ξ.toEvenMixture.coefficient p≠0 at hp
    have hn' : p∉Ξ.degrees := hn
    exact hp (by rw [toEvenMixture_coefficient,ite_eq_right hn']))⟩

@[simp] theorem toRevisedCovariance_toEvenMixture (Ξ : AdmissibleCovariance) :
    Ξ.toRevisedCovariance.toEvenMixture=Ξ.toEvenMixture := rfl

@[simp] theorem toRevisedCovariance_value (Ξ : AdmissibleCovariance) (q : ℝ) :
    Ξ.toRevisedCovariance.value q=Ξ.value q := by
  rw [←DepthPaper.RevisedCovariance.toEvenMixture_value,toRevisedCovariance_toEvenMixture,
    toEvenMixture_value]

@[simp] theorem toRevisedCovariance_first (Ξ : AdmissibleCovariance) (q : ℝ) :
    Ξ.toRevisedCovariance.first q=Ξ.first q := by
  rw [←DepthPaper.RevisedCovariance.toEvenMixture_first,toRevisedCovariance_toEvenMixture,
    toEvenMixture_first]

@[simp] theorem toRevisedCovariance_second (Ξ : AdmissibleCovariance) (q : ℝ) :
    Ξ.toRevisedCovariance.second q=Ξ.second q := by
  rw [←DepthPaper.RevisedCovariance.toEvenMixture_second,toRevisedCovariance_toEvenMixture,
    toEvenMixture_second]

theorem toRevisedCovariance_isSubcritical_iff (Ξ : AdmissibleCovariance) :
    Ξ.toRevisedCovariance.IsSubcritical ↔ Ξ.IsSubcritical := by
  change Ξ.toRevisedCovariance.second 0<1 ↔ Ξ.second 0<1
  rw [toRevisedCovariance_second]

end GeneralDepthPaper.AdmissibleCovariance

namespace GeneralDepthPaper

@[simp] theorem revised_potential (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) (q x : ℝ) :
    DepthPaper.RevisedCovariance.potential Ξ.toRevisedCovariance μ q x=potential Ξ μ q x := rfl

@[simp] theorem revised_gradient (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) (q x : ℝ) :
    DepthPaper.RevisedCovariance.gradient Ξ.toRevisedCovariance μ q x=gradient Ξ μ q x := rfl

@[simp] theorem revised_hessian (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) (q x : ℝ) :
    DepthPaper.RevisedCovariance.hessian Ξ.toRevisedCovariance μ q x=hessian Ξ μ q x := rfl

@[simp] theorem revised_optimalState (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (sample : BrownianSample) (q : ℝ) :
    DepthPaper.RevisedCovariance.optimalState Ξ.toRevisedCovariance μ sample q=
      optimalState Ξ μ sample q := rfl

@[simp] theorem revised_Gamma (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) :
    DepthPaper.RevisedCovariance.Gamma Ξ.toRevisedCovariance μ=Gamma Ξ μ := rfl

@[simp] theorem revised_curvatureMoment (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) :
    DepthPaper.RevisedCovariance.curvatureMoment Ξ.toRevisedCovariance μ=curvatureMoment Ξ μ := rfl

@[simp] theorem revised_firstVariation (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) :
    DepthPaper.RevisedCovariance.firstVariation Ξ.toRevisedCovariance μ=firstVariation Ξ μ := rfl

@[simp] theorem revised_parisiFunctional (Ξ : AdmissibleCovariance) :
    DepthPaper.RevisedCovariance.parisiFunctional Ξ.toRevisedCovariance=parisiFunctional Ξ := rfl

@[simp] theorem revised_parisiPressure (Ξ : AdmissibleCovariance) :
    DepthPaper.RevisedCovariance.parisiPressure Ξ.toRevisedCovariance=parisiPressure Ξ := rfl

@[simp] theorem revised_isParisiMinimizer (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) :
    DepthPaper.RevisedCovariance.IsParisiMinimizer Ξ.toRevisedCovariance μ ↔
      IsParisiMinimizer Ξ μ := Iff.rfl

end GeneralDepthPaper
