module

public import GeneralDepthPaper.TruncatedItoTest
public import GeneralDepthPaper.VariableItoIncrement

@[expose] public section


/-! Exact cancellation of the actual optimal-drift generator on a cropped
truncated cell. The squared-gradient source is the genuine covariance rate
times the squared actual Hessian. -/
noncomputable section
open Set Filter MeasureTheory StochasticCalculus
open scoped Topology NNReal BoundedContinuousFunction
namespace GeneralDepthPaper
open FourPapersCommon Paper FRSB
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

theorem variableItoGenerator_square {Ω : Type*} (X d : ℝ≥0 → Ω → ℝ) (σ : ℝ≥0 → ℝ)
    (f : ℝ → ℝ → ℝ) (ht : ∀x,Differentiable ℝ (fun s => f s x))
    (hx : ∀s,ContDiff ℝ 2 (f s)) (s : ℝ) (ω : Ω) :
    variableItoGenerator X d σ (itoSquareTest f) s ω =
      2*f s (X s.toNNReal ω)*variableItoGenerator X d σ f s ω+
        (σ s.toNNReal)^2*(itoSpaceDerivative f s (X s.toNNReal ω))^2 := by
  unfold variableItoGenerator
  rw [itoSquareTest_timeDerivative f ht,
    itoSquareTest_spaceDerivative f (fun t => (hx t).differentiable (by norm_num)),
    itoSquareTest_spaceSecondDerivative f hx]
  ring

namespace TruncatedParisiData

theorem stateDrift_eq {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc)
    (s : ℝ) (hs : s ∈ Icc (0:ℝ) qc) (ω : BrownianSample) :
    d.stateDrift s.toNNReal ω = d.covarianceField 2 s*d.coefficient s*
      d.spatialField 0 (s,d.state s.toNNReal ω) := by
  have hsT : (s.toNNReal:ℝ) ≤ qc := by rw [Real.coe_toNNReal _ hs.1]; exact hs.2
  simp [stateDrift,clockedItoDrift,hsT,hs.2,driftData,Real.coe_toNNReal _ hs.1,state]

theorem rateVolatility_sq_real {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc)
    (s : ℝ) (hs : 0 ≤ s) : (rateVolatility d.rateData s.toNNReal)^2 = d.covarianceField 2 s := by
  rw [rateVolatility_sq]
  simp only [rateData,Real.coe_toNNReal _ hs]

theorem cappedGradient_generator_zero {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc)
    (i : Fin (r+1)) (l b : ℝ) (hl : (d.node i.castSucc:ℝ) < l)
    (hlb : l ≤ b) (hb : b < (d.node i.succ:ℝ)) (s : ℝ) (hs : s ∈ Icc l b)
    (ω : BrownianSample) :
    variableItoGenerator d.state d.stateDrift (rateVolatility d.rateData)
      (d.cappedGradient i l b) s ω = 0 := by
  have hscell : s ∈ Ioo (d.node i.castSucc:ℝ) (d.node i.succ:ℝ) :=
    ⟨hl.trans_le hs.1,hs.2.trans_lt hb⟩
  have hscc : s ∈ Icc (0:ℝ) qc :=
    ⟨(d.node i.castSucc).property.1.trans hscell.1.le,
      hscell.2.le.trans (d.node i.succ).property.2⟩
  have ht := interiorCappedTest_timeDerivative d.gradient (d.gradientTimeSource i)
    (d.node i.castSucc) l b (d.node i.succ) hl hlb hb
    (fun t ht x => d.hasDerivAt_gradient_time i t x ht) s (d.state s.toNNReal ω)
  change itoTimeDerivative (d.cappedGradient i l b) s (d.state s.toNNReal ω) = _ at ht
  unfold variableItoGenerator
  rw [ht,d.cappedGradient_spaceDerivative,d.cappedGradient_spaceSecondDerivative,
    interiorTimeCap_eq _ _ _ _ _ hs,interiorTimeCapD_eq _ _ _ _ _ hs,
    mul_one,d.stateDrift_eq s hscc ω,d.rateVolatility_sq_real s hscc.1]
  rw [show d.coefficient s = d.level i from
    truncatedCoefficient_eq_level d.parameter d.node_strictMono.monotone s i ⟨hscell.1.le,hscell.2⟩]
  unfold gradientTimeSource
  ring

theorem cappedGradient_square_generator {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc)
    (i : Fin (r+1)) (l b : ℝ) (hl : (d.node i.castSucc:ℝ) < l)
    (hlb : l ≤ b) (hb : b < (d.node i.succ:ℝ)) (s : ℝ) (hs : s ∈ Icc l b)
    (ω : BrownianSample) :
    variableItoGenerator d.state d.stateDrift (rateVolatility d.rateData)
      (itoSquareTest (d.cappedGradient i l b)) s ω =
        d.covarianceField 2 s*(d.spatialField 1 (s,d.state s.toNNReal ω))^2 := by
  obtain ⟨hf,ht,hx,hdt,hdx,hdxx⟩ := d.cappedGradient_regular i l b hl hlb hb
  rw [variableItoGenerator_square _ _ _ _ ht hx,
    d.cappedGradient_generator_zero i l b hl hlb hb s hs ω,mul_zero,zero_add,
    d.cappedGradient_spaceDerivative,interiorTimeCap_eq _ _ _ _ _ hs]
  exact congrArg (fun c => c*(d.spatialField 1 (s,d.state s.toNNReal ω))^2)
    (d.rateVolatility_sq_real s ((d.node i.castSucc).property.1.trans (hl.le.trans hs.1)))

end TruncatedParisiData
end GeneralDepthPaper
