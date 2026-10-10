module

public import GeneralDepthPaper.TruncatedItoGenerator

@[expose] public section


/-! All domination and measurability obligations for the actual capped
squared-gradient Itô identity, derived from the prescribed three bounded jets. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus
open scoped Topology NNReal BoundedContinuousFunction
namespace GeneralDepthPaper
open FourPapersCommon Paper FRSB
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

theorem measurable_variableItoGenerator {Ω : Type*} [MeasurableSpace Ω]
    (X d : ℝ≥0 → Ω → ℝ) (σ : ℝ≥0 → ℝ) (f : ℝ → ℝ → ℝ)
    (hX : Measurable (Function.uncurry X)) (hd : Measurable (Function.uncurry d))
    (hσ : Continuous σ)
    (ht : Continuous (fun p : ℝ×ℝ => itoTimeDerivative f p.1 p.2))
    (hx : Continuous (fun p : ℝ×ℝ => itoSpaceDerivative f p.1 p.2))
    (hxx : Continuous (fun p : ℝ×ℝ => itoSpaceSecondDerivative f p.1 p.2)) :
    Measurable (Function.uncurry (variableItoGenerator X d σ f)) := by
  have hm : Measurable (fun p : ℝ×Ω => (p.1.toNNReal,p.2)) :=
    (measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd
  have hXp : Measurable (fun p : ℝ×Ω => (p.1,X p.1.toNNReal p.2)) :=
    measurable_fst.prodMk (hX.comp hm)
  exact ((ht.measurable.comp hXp).add ((hx.measurable.comp hXp).mul (hd.comp hm))).add
    (((hxx.measurable.comp hXp).const_mul (1/2:ℝ)).mul
      (((hσ.measurable.comp measurable_real_toNNReal).comp measurable_fst).pow_const 2))

namespace TruncatedParisiData

theorem norm_spatialField_le {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc)
    (j : Fin 3) (p : ℝ×ℝ) : ‖d.spatialField j p‖ ≤ ‖truncatedPotentialFamily d.parameter‖ :=
  ((d.spatialField j).norm_coe_le_norm p).trans
    (norm_truncatedSpatialField_le d.qc_pos.le d.parameter j)

theorem norm_gradientTimeSource_le {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc)
    (i : Fin (r+1)) (t x : ℝ) :
    ‖d.gradientTimeSource i t x‖ ≤ 3*‖d.covarianceJet 2‖*‖truncatedPotentialFamily d.parameter‖ := by
  let K := ‖truncatedPotentialFamily d.parameter‖
  let R := ‖d.covarianceJet 2‖
  have hK : 0 ≤ K := norm_nonneg _
  have hR : 0 ≤ R := norm_nonneg _
  have hB := ((d.spatialField 0).norm_coe_le_norm (t,x)).trans d.spatialField_zero_bound
  have hC := d.norm_spatialField_le 1 (t,x)
  have hD := d.norm_spatialField_le 2 (t,x)
  have ha : ‖d.level i‖ ≤ 1 := by rw [Real.norm_of_nonneg (d.level_mem i).1]; exact (d.level_mem i).2
  have hprod : ‖2*d.level i*d.spatialField 0 (t,x)*d.spatialField 1 (t,x)‖ ≤ 2*K := by
    simp only [norm_mul,show ‖(2:ℝ)‖ = 2 by norm_num]
    calc
      _ ≤ 2*1*1*K := by gcongr
      _ = _ := by ring
  have hsum := (norm_add_le (d.spatialField 2 (t,x))
    (2*d.level i*d.spatialField 0 (t,x)*d.spatialField 1 (t,x))).trans (add_le_add hD hprod)
  rw [gradientTimeSource,norm_mul,norm_div,norm_neg,show ‖(2:ℝ)‖ = 2 by norm_num]
  calc
    _ ≤ R/2*(K+2*K) := mul_le_mul (div_le_div_of_nonneg_right (d.norm_covarianceField_le 2 t) (by norm_num))
      hsum (norm_nonneg _) (by positivity)
    _ ≤ 3*R*K := by nlinarith

theorem norm_cappedGradient_le_one {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc)
    (i : Fin (r+1)) (l b t x : ℝ) : ‖d.cappedGradient i l b t x‖ ≤ 1 :=
  ((d.spatialField 0).norm_coe_le_norm _).trans d.spatialField_zero_bound

theorem norm_cappedGradient_timeDerivative_le {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc)
    (i : Fin (r+1)) (l b : ℝ) (hl : (d.node i.castSucc:ℝ) < l)
    (hlb : l ≤ b) (hb : b < (d.node i.succ:ℝ)) (t x : ℝ) :
    ‖itoTimeDerivative (d.cappedGradient i l b) t x‖ ≤
      3*‖d.covarianceJet 2‖*‖truncatedPotentialFamily d.parameter‖ := by
  rw [show itoTimeDerivative (d.cappedGradient i l b) t x =
      d.gradientTimeSource i (interiorTimeCap (d.node i.castSucc) l b (d.node i.succ) t) x*
        interiorTimeCapD (d.node i.castSucc) l b (d.node i.succ) t from
      interiorCappedTest_timeDerivative d.gradient (d.gradientTimeSource i) _ _ _ _ hl hlb hb
        (fun t ht x => d.hasDerivAt_gradient_time i t x ht) t x,norm_mul]
  exact (mul_le_mul (d.norm_gradientTimeSource_le i _ x)
    (norm_interiorTimeCapD_le_one _ _ _ _ t hl hb) (norm_nonneg _) (by positivity)).trans_eq (mul_one _)

theorem norm_cappedGradient_square_generator_le {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc)
    (i : Fin (r+1)) (l b : ℝ) (hl : (d.node i.castSucc:ℝ) < l)
    (hlb : l ≤ b) (hb : b < (d.node i.succ:ℝ)) (t : ℝ) (ω : BrownianSample) :
    ‖variableItoGenerator d.state d.stateDrift (rateVolatility d.rateData)
        (itoSquareTest (d.cappedGradient i l b)) t ω‖ ≤
      ‖d.covarianceJet 2‖*(‖truncatedPotentialFamily d.parameter‖^2+
        9*‖truncatedPotentialFamily d.parameter‖) := by
  let K := ‖truncatedPotentialFamily d.parameter‖
  let R := ‖d.covarianceJet 2‖
  let x := d.state t.toNNReal ω
  have hK : 0 ≤ K := norm_nonneg _
  have hR : 0 ≤ R := norm_nonneg _
  obtain ⟨hf,ht,hx,hdt,hdx,hdxx⟩ := d.cappedGradient_regular i l b hl hlb hb
  have hB := d.norm_cappedGradient_le_one i l b t x
  have hT := d.norm_cappedGradient_timeDerivative_le i l b hl hlb hb t x
  have hC : ‖itoSpaceDerivative (d.cappedGradient i l b) t x‖ ≤ K := by
    rw [d.cappedGradient_spaceDerivative]; exact d.norm_spatialField_le 1 _
  have hD : ‖itoSpaceSecondDerivative (d.cappedGradient i l b) t x‖ ≤ K := by
    rw [d.cappedGradient_spaceSecondDerivative]; exact d.norm_spatialField_le 2 _
  have hμ : ‖d.stateDrift t.toNNReal ω‖ ≤ R :=
    norm_clockedItoDrift_le d.driftData d.rateData 0 qc d.qc_pos.le _ _
  have hσ : ‖(rateVolatility d.rateData t.toNNReal)^2‖ ≤ R := by
    rw [rateVolatility_sq,Real.norm_of_nonneg (d.rateData.nonneg _)]
    simpa only [rateData,Real.norm_of_nonneg (d.covarianceField_nonneg t.toNNReal)] using
      d.norm_covarianceField_le 2 t.toNNReal
  have htime : ‖itoTimeDerivative (itoSquareTest (d.cappedGradient i l b)) t x‖ ≤ 6*R*K := by
    rw [itoSquareTest_timeDerivative _ ht,norm_mul,norm_mul,show ‖(2:ℝ)‖ = 2 by norm_num]
    calc
      _ ≤ 2*1*(3*R*K) := by gcongr
      _ = _ := by ring
  have hspace : ‖itoSpaceDerivative (itoSquareTest (d.cappedGradient i l b)) t x‖ ≤ 2*K := by
    rw [itoSquareTest_spaceDerivative _ (fun t => (hx t).differentiable (by norm_num)),
      norm_mul,norm_mul,show ‖(2:ℝ)‖ = 2 by norm_num]
    calc
      _ ≤ 2*1*K := by gcongr
      _ = _ := by ring
  have hsecond : ‖itoSpaceSecondDerivative (itoSquareTest (d.cappedGradient i l b)) t x‖ ≤ 2*K^2+2*K := by
    rw [itoSquareTest_spaceSecondDerivative _ hx]
    apply (norm_add_le _ _).trans
    simp only [norm_mul,norm_pow,show ‖(2:ℝ)‖ = 2 by norm_num]
    calc
      _ ≤ 2*K^2+2*1*K := by gcongr
      _ = _ := by ring
  unfold variableItoGenerator
  change ‖itoTimeDerivative _ t x+itoSpaceDerivative _ t x*d.stateDrift t.toNNReal ω+
    (1/2:ℝ)*itoSpaceSecondDerivative _ t x*(rateVolatility d.rateData t.toNNReal)^2‖ ≤ R*(K^2+9*K)
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  simp only [norm_mul,show ‖(1/2:ℝ)‖ = 1/2 by norm_num]
  calc
    _ ≤ 6*R*K+(2*K)*R+((1/2)*(2*K^2+2*K))*R := by gcongr
    _ = _ := by ring

end TruncatedParisiData
end GeneralDepthPaper
