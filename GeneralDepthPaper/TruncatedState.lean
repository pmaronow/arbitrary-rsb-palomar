module

public import GeneralDepthPaper.TruncatedData
public import FourPapersCommon.ClockedAdditiveState

@[expose] public section


/-! The actual optimal diffusion for the literal truncated covariance and
finite recursion. Its state, adaptation, martingale and variable bracket
characteristics come from the constructed integral-Picard solution. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus
open scoped Topology NNReal ENNReal BoundedContinuousFunction
namespace GeneralDepthPaper
open FourPapersCommon Paper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64
namespace TruncatedParisiData

def rateData {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) : NonnegativeRate where
  rate := fun t => d.covarianceField 2 t
  continuous_rate := (d.continuous_covarianceField 2).comp NNReal.continuous_coe
  nonneg := fun t => d.covarianceField_nonneg t

def driftData {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) : AdditiveDriftData where
  coefficient := fun t => d.covarianceField 2 t*d.coefficient t
  gradient := fun t x => d.spatialField 0 (t,x)
  radius := ‖d.covarianceJet 2‖₊
  gradientLip := ‖truncatedPotentialFamily d.parameter‖₊
  coefficient_measurable := (d.continuous_covarianceField 2).measurable.mul
    (measurable_truncatedCoefficient d.parameter)
  coefficient_bound := fun t => by
    rw [norm_mul]
    have h := norm_truncatedCoefficient_le_one d.parameter d.node_strictMono.monotone d.level_mem t
    exact (mul_le_mul (d.norm_covarianceField_le 2 t) h (norm_nonneg _) (norm_nonneg _)).trans_eq
      (by simp only [mul_one,coe_nnnorm])
  gradient_continuous := (d.spatialField 0).continuous
  gradient_bound := fun t x => ((d.spatialField 0).norm_coe_le_norm (t,x)).trans d.spatialField_zero_bound
  gradient_lipschitz := fun t => lipschitzWith_truncatedSpatialField_zero d.qc_pos.le d.parameter t

def state {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) (t : ℝ≥0) : BrownianSample → ℝ :=
  clockedItoState d.driftData d.rateData 0 qc d.qc_pos.le t

def stateDrift {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) (t : ℝ≥0) : BrownianSample → ℝ :=
  clockedItoDrift d.driftData d.rateData 0 qc d.qc_pos.le t

def Gamma {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) (t : ℝ) : ℝ :=
  ∫ω,(d.spatialField 0 (t,d.state t.toNNReal ω))^2 ∂canonicalBrownianMeasure

def Gamma2 {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) (t : ℝ) : ℝ :=
  ∫ω,(d.spatialField 1 (t,d.state t.toNNReal ω))^2 ∂canonicalBrownianMeasure

def firstVariation {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) (q : ℝ) : ℝ :=
  (1/2:ℝ)*∫t in (0:ℝ)..q,d.covarianceField 2 t*(d.Gamma t-t)

theorem state_characteristics {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) :
    BoundedDriftVariableItoCharacteristics canonicalBrownianMeasure
      (timeChangedBrownianFiltration (rateClock d.rateData) (monotone_rateClock d.rateData))
      d.state d.stateDrift (timeChangedBrownian (rateClock d.rateData)) (rateVolatility d.rateData) :=
  boundedDriftVariableItoCharacteristics_clockedItoState d.driftData d.rateData 0 qc d.qc_pos.le

theorem state_initial {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) (ω : BrownianSample) :
    d.state 0 ω = 0 := clockedItoState_zero d.driftData d.rateData 0 qc d.qc_pos.le ω

theorem state_integral_equation {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc)
    (t : ℝ≥0) (ht : (t:ℝ) ≤ qc) (ω : BrownianSample) :
    d.state t ω = timeChangedBrownian (rateClock d.rateData) t ω+
      ∫s in (0:ℝ)..(t:ℝ),d.covarianceField 2 s*d.coefficient s*
        d.spatialField 0 (s,d.state s.toNNReal ω) := by
  rw [state,clockedItoState_eq d.driftData d.rateData 0 qc d.qc_pos.le ht]
  have he := clockedStateReal_integral_equation d.driftData d.rateData 0 qc d.qc_pos.le ω
    (t := t) ⟨t.coe_nonneg,ht⟩
  rw [he]
  simp only [zero_add,rateNoiseReal,Real.toNNReal_coe,driftData]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le t.coe_nonneg] at hs
  have hsT : (s.toNNReal:ℝ) ≤ qc := by rw [Real.coe_toNNReal _ hs.1]; exact hs.2.trans ht
  simp only [state,clockedItoState_eq d.driftData d.rateData 0 qc d.qc_pos.le hsT,
    Real.coe_toNNReal _ hs.1]
  rfl

theorem continuous_state {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) (ω : BrownianSample) :
    Continuous (fun t => d.state t ω) :=
  continuous_clockedItoState d.driftData d.rateData 0 qc d.qc_pos.le ω

theorem measurable_state {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) :
    Measurable (Function.uncurry d.state) :=
  measurable_clockedItoState d.driftData d.rateData 0 qc d.qc_pos.le

theorem stronglyAdapted_state {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) :
    StronglyAdapted (timeChangedBrownianFiltration (rateClock d.rateData) (monotone_rateClock d.rateData))
      d.state := stronglyAdapted_clockedItoState d.driftData d.rateData 0 qc d.qc_pos.le

end TruncatedParisiData
end GeneralDepthPaper
