module

public import DepthPaper.FinitePressureCalculus
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section


/-! Genuine differentiation under the Gaussian expectation and the exact
finite entropy-pressure identity. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace DepthPaper
open FourPapersCommon OverlapPaper
set_option maxHeartbeats 1000000

def expectedScaledPressure (ξ : AdmissibleEvenMixture) (n : ℕ) (b : ℝ) : ℝ :=
  ∫ g : Disorder n,finitePressureObservable g b ∂disorderLaw ξ n

def expectedScaledResponse (ξ : AdmissibleEvenMixture) (n : ℕ) (b : ℝ) : ℝ :=
  ∫ g : Disorder n,finitePressureResponse g b ∂disorderLaw ξ n

theorem integrable_pressure_response_bound (ξ : AdmissibleEvenMixture) (n : ℕ) :
    Integrable (fun g : Disorder n=>‖g‖/(n : ℝ)) (disorderLaw ξ n) :=
  (show Integrable (id : Disorder n→Disorder n) (disorderLaw ξ n) from IsGaussian.integrable_id).norm.div_const _

theorem integrable_finitePressureResponse (ξ : AdmissibleEvenMixture) (n : ℕ) (b : ℝ) :
    Integrable (fun g : Disorder n=>finitePressureResponse g b) (disorderLaw ξ n) :=
  (integrable_pressure_response_bound ξ n).mono'
    (continuous_finitePressureResponse_slice b).aestronglyMeasurable
    (.of_forall fun g=>norm_finitePressureResponse_le g b)

theorem hasDerivAt_expectedScaledPressure (ξ : AdmissibleEvenMixture) (n : ℕ) (b : ℝ) :
    HasDerivAt (expectedScaledPressure ξ n) (expectedScaledResponse ξ n b) b := by
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := disorderLaw ξ n)
    (F := fun a g=>finitePressureObservable g a) (F' := fun a g=>finitePressureResponse g a)
    (bound := fun g=>‖g‖/(n : ℝ)) (s := univ) (by simp)
    (.of_forall fun a=>(continuous_finitePressureObservable_slice a).aestronglyMeasurable)
    (integrable_finitePressureObservable ξ n b)
    (continuous_finitePressureResponse_slice b).aestronglyMeasurable
    (.of_forall fun g a _=>norm_finitePressureResponse_le g a)
    (integrable_pressure_response_bound ξ n)
    (.of_forall fun g a _=>hasDerivAt_finitePressureObservable g a)).2

theorem convexOn_expectedScaledPressure (ξ : AdmissibleEvenMixture) (n : ℕ) :
    ConvexOn ℝ univ (expectedScaledPressure ξ n) := by
  refine ⟨convex_univ,?_⟩
  intro x hx y hy a b ha hb hab
  change (∫ g : Disorder n,finitePressureObservable g (a*x+b*y) ∂disorderLaw ξ n) ≤
    a*(∫ g : Disorder n,finitePressureObservable g x ∂disorderLaw ξ n)+
    b*(∫ g : Disorder n,finitePressureObservable g y ∂disorderLaw ξ n)
  calc
    _ ≤ ∫ g : Disorder n,a*finitePressureObservable g x+b*finitePressureObservable g y ∂disorderLaw ξ n :=
      integral_mono (integrable_finitePressureObservable ξ n _)
        (((integrable_finitePressureObservable ξ n x).const_mul a).add
          ((integrable_finitePressureObservable ξ n y).const_mul b))
        (fun g=>(convexOn_finitePressureObservable g).2 hx hy ha hb hab)
    _ = _ := by
      rw [integral_add ((integrable_finitePressureObservable ξ n x).const_mul a)
        ((integrable_finitePressureObservable ξ n y).const_mul b),integral_const_mul,integral_const_mul]

theorem expectedEntropyDensity_eq_pressure_sub_response (ξ : AdmissibleEvenMixture) (n : ℕ) :
    expectedEntropyDensity ξ n=expectedScaledPressure ξ n 1-expectedScaledResponse ξ n 1 := by
  have HE : (∫ g : Disorder n,gibbsEntropy g ∂disorderLaw ξ n)=
      (∫ g : Disorder n,Real.log (partitionFunction 0 g) ∂disorderLaw ξ n)-
      ∫ g : Disorder n,∑ σ,gibbsWeight 0 g σ*g σ ∂disorderLaw ξ n := by
    calc
      _ = ∫ g : Disorder n,Real.log (partitionFunction 0 g)-∑ σ,gibbsWeight 0 g σ*g σ ∂disorderLaw ξ n :=
        integral_congr_ae (.of_forall fun g=>gibbsEntropy_eq_log_partition_sub_energy g)
      _ = _ := integral_sub (integrable_log_partitionFunction ξ 0)
        (integrable_finsetSum _ (fun σ _=>integrable_gibbs_energy ξ σ))
  unfold expectedEntropyDensity expectedScaledPressure expectedScaledResponse finitePressureObservable finitePressureResponse freeEnergy
  simp only [one_smul]
  rw [integral_div,integral_div,←sub_div,HE]

theorem expectedEntropyDensity_eq_pressure_sub_deriv (ξ : AdmissibleEvenMixture) (n : ℕ) :
    expectedEntropyDensity ξ n=expectedScaledPressure ξ n 1-deriv (expectedScaledPressure ξ n) 1 := by
  rw [(hasDerivAt_expectedScaledPressure ξ n 1).deriv]
  exact expectedEntropyDensity_eq_pressure_sub_response ξ n

end DepthPaper
