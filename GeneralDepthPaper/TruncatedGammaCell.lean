module

public import GeneralDepthPaper.TruncatedItoBounds

@[expose] public section


/-! Exact overlap evolution on each cropped finite cell, proved for the
constructed diffusion by the centered variable-volatility Itô identity. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus
open scoped Topology NNReal BoundedContinuousFunction
namespace GeneralDepthPaper
open FourPapersCommon Paper FRSB
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

theorem measurable_process_eval {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (hX : Measurable (Function.uncurry X)) (t : ℝ≥0) :
    Measurable (X t) :=
  hX.comp (show Measurable (fun ω : Ω => (t,ω)) from
    measurable_const.prodMk measurable_id)

namespace TruncatedParisiData

theorem Gamma_sub_eq_integral_cell_interior {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc)
    (i : Fin (r+1)) (a b : ℝ≥0) (ha : (d.node i.castSucc:ℝ) < a)
    (hab : a ≤ b) (hb : (b:ℝ) < (d.node i.succ:ℝ)) :
    d.Gamma b-d.Gamma a = ∫s in (a:ℝ)..(b:ℝ),d.covarianceField 2 s*d.Gamma2 s := by
  let g := d.cappedGradient i a b
  let f := itoSquareTest g
  let source := variableItoGenerator d.state d.stateDrift (rateVolatility d.rateData) f
  let K := ‖truncatedPotentialFamily d.parameter‖
  have habR : (a:ℝ) ≤ b := NNReal.coe_le_coe.mpr hab
  obtain ⟨hg,hgt,hgx,hgdt,hgdx,hgdxx⟩ := d.cappedGradient_regular i a b ha habR hb
  have hf := continuous_itoSquareTest g hg
  have hft := differentiable_itoSquareTest_time g hgt
  have hfx := contDiff_itoSquareTest_spatial g hgx
  have hfdt := continuous_itoSquareTest_timeDerivative g hg hgt hgdt
  have hfdx := continuous_itoSquareTest_spaceDerivative g hg
    (fun s => (hgx s).differentiable (by norm_num)) hgdx
  have hfdxx := continuous_itoSquareTest_spaceSecondDerivative g hg hgx hgdx hgdxx
  have hsource : Measurable (Function.uncurry source) :=
    measurable_variableItoGenerator _ _ _ _ d.measurable_state d.state_characteristics.measurable_drift
      d.state_characteristics.continuous_volatility hfdt hfdx hfdxx
  have hB : ∀s ω,‖source s ω‖ ≤ ‖d.covarianceJet 2‖*(K^2+9*K) :=
    fun s ω => d.norm_cappedGradient_square_generator_le i a b ha habR hb s ω
  have hdxB : ∀s∈Icc (0:ℝ) (b:ℝ),∀x,‖itoSpaceDerivative f s x‖ ≤ (2*‖truncatedPotentialFamily d.parameter‖₊:ℝ≥0) := by
    intro s _ x
    apply norm_itoSquareTest_spaceDerivative_le g
      (fun s => (hgx s).differentiable (by norm_num)) (R := 1) (K := K)
      (fun t y => d.norm_cappedGradient_le_one i a b t y) ?_ s x |>.trans_eq ?_
    · intro t y
      rw [d.cappedGradient_spaceDerivative]
      exact d.norm_spatialField_le 1 _
    · simp only [NNReal.coe_mul,NNReal.coe_ofNat,coe_nnnorm,mul_one]
      rfl
  have hi : ∀t∈Icc (0:ℝ≥0) b,Integrable (fun ω => f t (d.state t ω)) canonicalBrownianMeasure := by
    intro t _
    have hX : Measurable (d.state t) :=
      measurable_process_eval d.state d.measurable_state t
    apply (integrable_const (1:ℝ)).mono'
      (hf.measurable.comp (measurable_const.prodMk hX)).aestronglyMeasurable
    exact .of_forall fun ω => by
      change ‖f t (d.state t ω)‖ ≤ 1
      rw [show f t (d.state t ω) = g t (d.state t ω)^2 from rfl,norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (d.norm_cappedGradient_le_one i a b t _)
  have he := variable_ito_expectation_increment d.state_characteristics f hf hft hfx hfdt hfdx hfdxx
    a b hab (2*‖truncatedPotentialFamily d.parameter‖₊) hdxB source hsource
    (‖d.covarianceJet 2‖*(K^2+9*K)) hB (fun _ _ _ => rfl) hi
  have hΓ (t : ℝ≥0) (ht : (t:ℝ) ∈ Icc (a:ℝ) (b:ℝ)) :
      (∫ω,f t (d.state t ω) ∂canonicalBrownianMeasure) = d.Gamma t := by
    apply integral_congr_ae
    exact .of_forall fun ω => by
      unfold f g itoSquareTest cappedGradient interiorCappedTest gradient
      rw [interiorTimeCap_eq _ _ _ _ _ ht]
      simp only [Real.toNNReal_coe]
  rw [hΓ a ⟨le_rfl,habR⟩,hΓ b ⟨habR,le_rfl⟩] at he
  rw [he]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le habR] at hs
  have hpoint : ∀ω,source s ω = d.covarianceField 2 s*(d.spatialField 1 (s,d.state s.toNNReal ω))^2 :=
    d.cappedGradient_square_generator i a b ha habR hb s hs
  change (∫ω,source s ω ∂canonicalBrownianMeasure) = d.covarianceField 2 s*d.Gamma2 s
  rw [integral_congr_ae (.of_forall hpoint),integral_const_mul]
  rfl

end TruncatedParisiData
end GeneralDepthPaper
