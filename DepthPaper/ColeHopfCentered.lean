module

public import DepthPaper.ColeHopfMassRegularity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section


/-! The centered cumulant representation removes the zero-mass singularity
using an actual integral of normalized Gaussian tilted moments. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ContDiff NNReal
namespace DepthPaper
open ColeHopfFoundation.ProbabilityTheory

def tiltedGaussianMean (g : ℝ→ℝ) (v : ℝ≥0) (x a : ℝ) : ℝ :=
  (∫z,g (x+z)*Real.exp (a*g (x+z)) ∂gaussianReal 0 v)/
    (∫z,Real.exp (a*g (x+z)) ∂gaussianReal 0 v)

theorem coleHopf_eq_integral_tiltedMean (g : ℝ→ℝ) (hg : HasLinearGrowth g)
    (hm : Measurable g) (v : ℝ≥0) (x a : ℝ) :
    coleHopf a v g x=∫t in (0:ℝ)..1,tiltedGaussianMean g v x (t*a) := by
  let X : ℝ→ℝ := fun z=>g (x+z)
  let F := cgf X (gaussianReal 0 v)
  have hset := gaussian_integrableExpSet_linearGrowth g hg hm v x
  have hmem (b : ℝ) : b∈interior (integrableExpSet X (gaussianReal 0 v)) := by
    change b∈interior (integrableExpSet (fun z=>g (x+z)) (gaussianReal 0 v))
    rw [hset,interior_univ]; exact mem_univ _
  have hF : ContDiff ℝ ⊤ F := by
    apply contDiff_iff_contDiffAt.mpr
    intro b
    exact (analyticAt_cgf (hmem b)).contDiffAt
  have he (b : ℝ) : deriv F b=tiltedGaussianMean g v x b := by
    exact deriv_cgf (hmem b)
  have hc : Continuous (deriv F) := hF.continuous_deriv (by norm_num)
  have hd (t : ℝ) : HasDerivAt (fun t=>F (t*a)) (a*deriv F (t*a)) t := by
    have hi : HasDerivAt (fun t:ℝ=>t*a) a t := by simpa using (hasDerivAt_id t).mul_const a
    simpa only [Function.comp_def,mul_comm] using
      (hF.differentiable (by norm_num) (t*a)).hasDerivAt.comp t hi
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _=>hd t) ((continuous_const.mul (hc.comp (continuous_id.mul continuous_const))).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul,one_mul,zero_mul] at hint
  have hf0 : F 0=0 := cgf_zero
  rw [hf0,sub_zero] at hint
  by_cases ha : a=0
  · subst a
    simp only [coleHopf_zero,mul_zero]
    rw [←he 0]
    simp only [intervalIntegral.integral_const,sub_zero,one_smul]
    simpa [F,X] using (deriv_cgf_zero (hmem 0)).symm
  · rw [coleHopf_of_ne ha]
    change (1/a)*F a=_
    rw [←hint]
    simp_rw [←he]
    field_simp

theorem coleHopf_centered_integral (g : ℝ→ℝ) (hg : HasLinearGrowth g)
    (hm : Measurable g) (v : ℝ≥0) (x a : ℝ) :
    coleHopf a v g x-g x=
      ∫t in (0:ℝ)..1,
        (∫z,(g (x+z)-g x)*Real.exp ((t*a)*(g (x+z)-g x)) ∂gaussianReal 0 v)/
        (∫z,Real.exp ((t*a)*(g (x+z)-g x)) ∂gaussianReal 0 v) := by
  have h := coleHopf_eq_integral_tiltedMean (fun y=>g y+(-g x))
    (hg.add_const _) (hm.add_const _) v x a
  rw [coleHopf_add_const hg hm] at h
  simpa only [tiltedGaussianMean,sub_eq_add_neg] using h

end DepthPaper
