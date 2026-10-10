module

public import DepthPaper.RevisedAtomicControlComparison
public import DepthPaper.RevisedVariationRegularity
public import Paper.ParisiControlEnvelope
public import DepthPaper.RevisedControlOriginalClock

@[expose] public section

/-! The actual log-cosh Taylor remainder in the revised strengthened
first-variation inequality. The development applies to every probability
measure, hence in particular to the finite atomic measures in the paper. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace DepthPaper.RevisedCovariance
open FourPapersCommon Paper
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 64

def logCoshTaylorRemainder (x i : ℝ) : ℝ :=
  Real.log (Real.cosh (x+i))-Real.log (Real.cosh x)-Real.tanh x*i

theorem logCoshTaylorRemainder_nonneg (x i : ℝ) : 0≤logCoshTaylorRemainder x i := by
  by_cases hi : i=0
  · simp [logCoshTaylorRemainder,hi]
  · rcases lt_or_gt_of_ne hi with hi|hi
    · have hs := strictConvexOn_logCosh.convexOn.slope_le_of_hasDerivAt
        (x:=x+i) (y:=x) (mem_univ _) (mem_univ _) (by linarith) (hasDerivAt_log_cosh x)
      rw [slope_def_field] at hs
      have hh := (div_le_iff₀ (by linarith : 0<x-(x+i))).mp hs
      unfold logCoshTaylorRemainder
      nlinarith
    · have hs := strictConvexOn_logCosh.convexOn.le_slope_of_hasDerivAt
        (x:=x) (y:=x+i) (mem_univ _) (mem_univ _) (by linarith) (hasDerivAt_log_cosh x)
      rw [slope_def_field] at hs
      have hh := (le_div_iff₀ (by linarith : 0<x+i-x)).mp hs
      unfold logCoshTaylorRemainder
      nlinarith

def normalizedSharpEndpoint (Ξ : RevisedCovariance) (μ : ParisiMeasure)
    (sample : BrownianSample) : ℝ :=
  mixedBeta Ξ.toEvenMixture*canonicalBrownian 1 sample+
    parisiControlDrift (mixedBeta Ξ.toEvenMixture) (mixedMeasure Ξ.toEvenMixture μ)
      (selectedParisiFeedbackControl (mixedBeta Ξ.toEvenMixture) 0
        (mixedMeasure Ξ.toEvenMixture μ)) sample

def normalizedSharpDrift (Ξ : RevisedCovariance) (μ ν : ParisiMeasure)
    (sample : BrownianSample) : ℝ :=
  parisiControlDrift (mixedBeta Ξ.toEvenMixture) (mixedMeasure Ξ.toEvenMixture ν)
      (selectedParisiFeedbackControl (mixedBeta Ξ.toEvenMixture) 0
        (mixedMeasure Ξ.toEvenMixture μ)) sample-
    parisiControlDrift (mixedBeta Ξ.toEvenMixture) (mixedMeasure Ξ.toEvenMixture μ)
      (selectedParisiFeedbackControl (mixedBeta Ξ.toEvenMixture) 0
        (mixedMeasure Ξ.toEvenMixture μ)) sample

def normalizedSharpRemainder (Ξ : RevisedCovariance) (μ ν : ParisiMeasure)
    (sample : BrownianSample) : ℝ :=
  logCoshTaylorRemainder (normalizedSharpEndpoint Ξ μ sample) (normalizedSharpDrift Ξ μ ν sample)

def fixedControlLinearVariation (Ξ : RevisedCovariance) (μ ν : ParisiMeasure) : ℝ :=
  (∫sample,parisiAffineControlDerivative (mixedBeta Ξ.toEvenMixture) 0 (canonicalBrownian 1)
    (selectedParisiFeedbackControl (mixedBeta Ξ.toEvenMixture) 0
      (mixedMeasure Ξ.toEvenMixture μ)) (mixedMeasure Ξ.toEvenMixture μ)
        (mixedMeasure Ξ.toEvenMixture ν) 0 sample ∂canonicalBrownianMeasure)-
    (fixedControlCorrection Ξ ν-fixedControlCorrection Ξ μ)/2

/-- The linear expectation identity is derived by uniqueness of the
genuine mixture derivative. Its control-envelope and first-variation
derivatives are already proved for the actual stochastic feedback. -/
theorem fixedControlLinearVariation_eq (Ξ : RevisedCovariance) (μ ν : ParisiMeasure) :
    fixedControlLinearVariation Ξ μ ν=
      -((∫q : Overlap,firstVariation Ξ μ q ∂(ν : Measure Overlap))-
        (∫q : Overlap,firstVariation Ξ μ q ∂(μ : Measure Overlap))) := by
  let β := mixedBeta Ξ.toEvenMixture
  let ρ := mixedMeasure Ξ.toEvenMixture μ
  let σ := mixedMeasure Ξ.toEvenMixture ν
  have hd := hasDerivWithinAt_parisiPotential_mix_control_right β 0
    (mixedBeta_ne_zero Ξ.toEvenMixture) ρ σ
  have hp : HasDerivWithinAt (fun t=>potential Ξ (parisiMix μ ν t) 0 0)
      (∫sample,parisiAffineControlDerivative β 0 (canonicalBrownian 1)
        (selectedParisiFeedbackControl β 0 ρ) ρ σ 0 sample ∂canonicalBrownianMeasure)
      (Ioi (0 : ℝ)) 0 := by
    apply hd.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds (show (0 : ℝ)<1 by norm_num)).filter_mono
          (nhdsWithin_le_nhds (s:=Ioi (0 : ℝ)) (a:=0))] with t ht ht₁
      simp only [potential,mixedPotential,Ξ.toEvenMixture.clock_zero,
        mixedMeasure_mix Ξ.toEvenMixture μ ν t ⟨ht.le,ht₁.le⟩,β,ρ,σ]
    · simp only [potential,mixedPotential,Ξ.toEvenMixture.clock_zero,parisiMix_zero,β,ρ]
  have hc := hasDerivWithinAt_of_affine_mixing
    (weightedCDFIntegral_mix (fun q=>q*Ξ.second q)
      (continuous_id.mul Ξ.continuous_second).continuousOn μ ν)
  have hactual := ((hasDerivAt_const (0 : ℝ) (Real.log 2)).hasDerivWithinAt.add hp).sub
    (hc.div_const 2)
  have hsame : HasDerivWithinAt (fun t=>parisiFunctional Ξ (parisiMix μ ν t))
      (fixedControlLinearVariation Ξ μ ν) (Ioi (0 : ℝ)) 0 := by
    convert hactual using 1
    · funext t
      rw [parisiFunctional_eq]
      simp only [weightedCDFIntegral,Pi.add_apply,Pi.sub_apply]
      ring
    · dsimp only [fixedControlLinearVariation,fixedControlCorrection,β,ρ,σ,weightedCDFIntegral]
      ring
  exact UniqueDiffWithinAt.eq_deriv (Ioi (0 : ℝ)) (uniqueDiffWithinAt_Ioi 0)
    hsame (hasDerivWithinAt_parisiFunctional_mix Ξ μ ν)

theorem normalizedSharpRemainder_eq_affine_payoff (Ξ : RevisedCovariance)
    (μ ν : ParisiMeasure) (sample : BrownianSample) :
    normalizedSharpRemainder Ξ μ ν sample=
      parisiAffineControlPayoff (mixedBeta Ξ.toEvenMixture) 0 (canonicalBrownian 1)
        (selectedParisiFeedbackControl (mixedBeta Ξ.toEvenMixture) 0
          (mixedMeasure Ξ.toEvenMixture μ)) (mixedMeasure Ξ.toEvenMixture μ)
            (mixedMeasure Ξ.toEvenMixture ν) 1 sample-
      parisiAffineControlPayoff (mixedBeta Ξ.toEvenMixture) 0 (canonicalBrownian 1)
        (selectedParisiFeedbackControl (mixedBeta Ξ.toEvenMixture) 0
          (mixedMeasure Ξ.toEvenMixture μ)) (mixedMeasure Ξ.toEvenMixture μ)
            (mixedMeasure Ξ.toEvenMixture ν) 0 sample-
      parisiAffineControlDerivative (mixedBeta Ξ.toEvenMixture) 0 (canonicalBrownian 1)
        (selectedParisiFeedbackControl (mixedBeta Ξ.toEvenMixture) 0
          (mixedMeasure Ξ.toEvenMixture μ)) (mixedMeasure Ξ.toEvenMixture μ)
            (mixedMeasure Ξ.toEvenMixture ν) 0 sample := by
  simp only [normalizedSharpRemainder,normalizedSharpEndpoint,normalizedSharpDrift,
    logCoshTaylorRemainder,parisiAffineControlPayoff,parisiAffineControlDerivative,
    zero_add,zero_mul,add_zero,one_mul]
  ring

theorem integrable_normalizedSharpRemainder (Ξ : RevisedCovariance)
    (μ ν : ParisiMeasure) : Integrable (normalizedSharpRemainder Ξ μ ν) canonicalBrownianMeasure := by
  have hA := isParisiAdmissibleControl_selectedParisiFeedbackControl
    (mixedBeta Ξ.toEvenMixture) 0 (mixedMeasure Ξ.toEvenMixture μ)
  have hi (t : ℝ) := integrable_parisiAffineControlPayoff canonicalBrownianMeasure
    (mixedBeta Ξ.toEvenMixture) 0 (canonicalBrownian 1) (measurable_canonicalBrownian 1)
    integrable_hjb_canonicalBrownian_one _ hA.measurable hA.bounded
    (mixedMeasure Ξ.toEvenMixture μ) (mixedMeasure Ξ.toEvenMixture ν) t
  have hd := integrable_parisiAffineControlDerivative canonicalBrownianMeasure
    (mixedBeta Ξ.toEvenMixture) 0 (canonicalBrownian 1) (measurable_canonicalBrownian 1)
    _ hA.measurable hA.bounded (mixedMeasure Ξ.toEvenMixture μ)
    (mixedMeasure Ξ.toEvenMixture ν) 0
  exact ((hi 1).sub (hi 0)).sub hd |>.congr (.of_forall fun sample=>
    (normalizedSharpRemainder_eq_affine_payoff Ξ μ ν sample).symm)

theorem integral_normalizedSharpRemainder_nonneg (Ξ : RevisedCovariance)
    (μ ν : ParisiMeasure) : 0≤∫sample,normalizedSharpRemainder Ξ μ ν sample
      ∂canonicalBrownianMeasure := by
  apply integral_nonneg
  intro sample
  exact logCoshTaylorRemainder_nonneg _ _

theorem integral_normalizedSharpRemainder_eq (Ξ : RevisedCovariance)
    (μ ν : ParisiMeasure) :
    (∫sample,normalizedSharpRemainder Ξ μ ν sample ∂canonicalBrownianMeasure)=
      fixedControlExpectation Ξ μ ν 1-fixedControlExpectation Ξ μ ν 0-
        (∫sample,parisiAffineControlDerivative (mixedBeta Ξ.toEvenMixture) 0 (canonicalBrownian 1)
          (selectedParisiFeedbackControl (mixedBeta Ξ.toEvenMixture) 0
            (mixedMeasure Ξ.toEvenMixture μ)) (mixedMeasure Ξ.toEvenMixture μ)
              (mixedMeasure Ξ.toEvenMixture ν) 0 sample ∂canonicalBrownianMeasure) := by
  have hA := isParisiAdmissibleControl_selectedParisiFeedbackControl
    (mixedBeta Ξ.toEvenMixture) 0 (mixedMeasure Ξ.toEvenMixture μ)
  have hi (t : ℝ) := integrable_parisiAffineControlPayoff canonicalBrownianMeasure
    (mixedBeta Ξ.toEvenMixture) 0 (canonicalBrownian 1) (measurable_canonicalBrownian 1)
    integrable_hjb_canonicalBrownian_one _ hA.measurable hA.bounded
    (mixedMeasure Ξ.toEvenMixture μ) (mixedMeasure Ξ.toEvenMixture ν) t
  have hd := integrable_parisiAffineControlDerivative canonicalBrownianMeasure
    (mixedBeta Ξ.toEvenMixture) 0 (canonicalBrownian 1) (measurable_canonicalBrownian 1)
    _ hA.measurable hA.bounded (mixedMeasure Ξ.toEvenMixture μ)
    (mixedMeasure Ξ.toEvenMixture ν) 0
  calc
    _ = ∫sample,parisiAffineControlPayoff (mixedBeta Ξ.toEvenMixture) 0 (canonicalBrownian 1)
          (selectedParisiFeedbackControl (mixedBeta Ξ.toEvenMixture) 0
            (mixedMeasure Ξ.toEvenMixture μ)) (mixedMeasure Ξ.toEvenMixture μ)
              (mixedMeasure Ξ.toEvenMixture ν) 1 sample-
        parisiAffineControlPayoff (mixedBeta Ξ.toEvenMixture) 0 (canonicalBrownian 1)
          (selectedParisiFeedbackControl (mixedBeta Ξ.toEvenMixture) 0
            (mixedMeasure Ξ.toEvenMixture μ)) (mixedMeasure Ξ.toEvenMixture μ)
              (mixedMeasure Ξ.toEvenMixture ν) 0 sample-
        parisiAffineControlDerivative (mixedBeta Ξ.toEvenMixture) 0 (canonicalBrownian 1)
          (selectedParisiFeedbackControl (mixedBeta Ξ.toEvenMixture) 0
            (mixedMeasure Ξ.toEvenMixture μ)) (mixedMeasure Ξ.toEvenMixture μ)
              (mixedMeasure Ξ.toEvenMixture ν) 0 sample ∂canonicalBrownianMeasure :=
      integral_congr_ae (.of_forall fun sample=>normalizedSharpRemainder_eq_affine_payoff Ξ μ ν sample)
    _ = _ := by
      have hsub := integral_sub ((hi 1).sub (hi 0)) hd
      simp only [Pi.sub_apply] at hsub
      rw [hsub]
      have hsub₀ := integral_sub (hi 1) (hi 0)
      rw [hsub₀]
      rfl

theorem sharp_first_variation_normalized (Ξ : RevisedCovariance)
    (μ ν : ParisiMeasure) :
    -((∫q : Overlap,firstVariation Ξ μ q ∂(ν : Measure Overlap))-
      (∫q : Overlap,firstVariation Ξ μ q ∂(μ : Measure Overlap)))+
      (∫sample,normalizedSharpRemainder Ξ μ ν sample ∂canonicalBrownianMeasure) ≤
        parisiFunctional Ξ ν-parisiFunctional Ξ μ := by
  have hbound := fixedControlComparison_le Ξ μ ν ν 1 1
    (fun q _=>by simp only [div_one,one_mul];ring)
    (fun q _=>by simp only [div_one,one_mul];ring)
  have hzero := fixedControlComparison_zero Ξ μ ν 1
  have hremainder := integral_normalizedSharpRemainder_eq Ξ μ ν
  have hlinear := fixedControlLinearVariation_eq Ξ μ ν
  have hid : fixedControlComparison Ξ μ ν 1 1-parisiFunctional Ξ μ=
      fixedControlLinearVariation Ξ μ ν+
        ∫sample,normalizedSharpRemainder Ξ μ ν sample ∂canonicalBrownianMeasure := by
    rw [←hzero,hremainder]
    simp only [fixedControlComparison,fixedControlLinearVariation,div_one,zero_div,
      one_mul,zero_mul,add_zero]
    ring
  rw [hlinear] at hid
  linarith

/-- The manuscript's drift increment in its original overlap clock. -/
def sharpFirstVariationDrift (Ξ : RevisedCovariance) (μ ν : ParisiMeasure)
    (sample : BrownianSample) : ℝ :=
  ∫q in (0 : ℝ)..1,Ξ.second q*(parisiCDF ν q-parisiCDF μ q)*
    gradient Ξ μ q (optimalState Ξ μ sample q)

def sharpFirstVariationRemainder (Ξ : RevisedCovariance) (μ ν : ParisiMeasure)
    (sample : BrownianSample) : ℝ :=
  logCoshTaylorRemainder (optimalState Ξ μ sample 1) (sharpFirstVariationDrift Ξ μ ν sample)

theorem sharpFirstVariationDrift_eq_normalized (Ξ : RevisedCovariance)
    (μ ν : ParisiMeasure) (sample : BrownianSample) :
    sharpFirstVariationDrift Ξ μ ν sample=normalizedSharpDrift Ξ μ ν sample :=
  integral_cdf_difference_gradient_eq_controlDrift Ξ μ ν sample

theorem sharpFirstVariationRemainder_eq_normalized (Ξ : RevisedCovariance)
    (μ ν : ParisiMeasure) :
    sharpFirstVariationRemainder Ξ μ ν=normalizedSharpRemainder Ξ μ ν := by
  funext sample
  unfold sharpFirstVariationRemainder normalizedSharpRemainder
  rw [sharpFirstVariationDrift_eq_normalized,optimalState_terminal_eq_controlDrift]
  rfl

theorem integrable_sharpFirstVariationRemainder (Ξ : RevisedCovariance)
    (μ ν : ParisiMeasure) :
    Integrable (sharpFirstVariationRemainder Ξ μ ν) canonicalBrownianMeasure := by
  rw [sharpFirstVariationRemainder_eq_normalized]
  exact integrable_normalizedSharpRemainder Ξ μ ν

/-- Revised Lemma `lem:sharp-first-variation`, proved for all genuine Parisi
probability measures. The remainder uses the actual original-clock optimal
diffusion and the exact original-clock drift increment, and is integrable
and nonnegative. -/
theorem sharp_first_variation (Ξ : RevisedCovariance) (μ ν : ParisiMeasure) :
    (-((∫q : Overlap,firstVariation Ξ μ q ∂(ν : Measure Overlap))-
      (∫q : Overlap,firstVariation Ξ μ q ∂(μ : Measure Overlap)))+
      (∫sample,sharpFirstVariationRemainder Ξ μ ν sample ∂canonicalBrownianMeasure) ≤
        parisiFunctional Ξ ν-parisiFunctional Ξ μ) ∧
    0≤∫sample,sharpFirstVariationRemainder Ξ μ ν sample ∂canonicalBrownianMeasure := by
  rw [sharpFirstVariationRemainder_eq_normalized]
  exact ⟨sharp_first_variation_normalized Ξ μ ν,integral_normalizedSharpRemainder_nonneg Ξ μ ν⟩

end DepthPaper.RevisedCovariance
