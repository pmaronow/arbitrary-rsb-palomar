module

public import DepthPaper.ScaledLogCoshTerminal
public import DepthPaper.CandidateTopSolution

@[expose] public section


/-! Exact Gaussian temperature–mass covariance, including a zero mass
level and zero variance. This is an equality of the actual Cole–Hopf
integrals, rather than a formal PDE change of variables. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace DepthPaper
open ColeHopfFoundation.ProbabilityTheory
set_option maxSynthPendingDepth 64

theorem integral_gaussian_field_scaling (m : ℝ) (v : ℝ≥0) (f : ℝ→ℝ)
    (hf : Measurable f) (x : ℝ) :
    (∫z,f (m*x+z) ∂gaussianReal 0 (NNReal.mk (m^2) (sq_nonneg m)*v))=
      ∫z,f (m*(x+z)) ∂gaussianReal 0 v := by
  have hmap : (gaussianReal 0 v).map (fun z=>m*z)=
      gaussianReal 0 (NNReal.mk (m^2) (sq_nonneg m)*v) := by
    simpa only [mul_zero] using gaussianReal_map_const_mul (μ:=0) (v:=v) m
  rw [←hmap,integral_map (f:=fun z:ℝ=>f (m*x+z)) (φ:=fun z:ℝ=>m*z)
    (by fun_prop) (hf.comp (by fun_prop)).aestronglyMeasurable]
  apply integral_congr_ae
  exact .of_forall fun z=>congrArg f (by ring)

theorem coleHopf_temperature_mass_scaling (m : ℝ) (hm : m≠0) (a : ℝ) (v : ℝ≥0)
    (h : ℝ→ℝ) (hh : Measurable h) (x : ℝ) :
    coleHopf (m*a) v (fun y=>m⁻¹*h (m*y)) x=
      m⁻¹*coleHopf a (NNReal.mk (m^2) (sq_nonneg m)*v) h (m*x) := by
  by_cases ha : a=0
  · subst a
    simp only [mul_zero,coleHopf_zero]
    rw [integral_const_mul,integral_gaussian_field_scaling m v h hh x]
  · rw [coleHopf_of_ne (mul_ne_zero hm ha),coleHopf_of_ne ha]
    have he (z:ℝ) : (m*a)*(m⁻¹*h (m*(x+z)))=a*h (m*(x+z)) := by
      field_simp
    simp_rw [he]
    rw [←integral_gaussian_field_scaling m v (fun y=>Real.exp (a*h y))
      (Real.measurable_exp.comp (measurable_const.mul hh)) x]
    field_simp

end DepthPaper
