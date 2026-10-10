module

public import GeneralDepthPaper.TemperatureMassPotential
public import GeneralDepthPaper.TruncatedAtomicData
public import FourPapersCommon.ClockedMoments
public import FourPapersCommon.BrownianClockRescaling

@[expose] public section


/-! The actual bounded-drift diffusion of the temperature–mass-scaled
problem. Positive lower mass is arbitrary; it is not restricted to one. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus
open scoped Topology NNReal ENNReal
namespace GeneralDepthPaper
open FourPapersCommon Paper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem continuous_temperatureMassProjection :
    Continuous (fun t:ℝ=>(projIcc 0 1 (by norm_num) t:ℝ)) :=
  continuous_subtype_val.comp continuous_projIcc

def temperatureMassDriftData (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (m : ℝ) (hm : 0 < m) : AdditiveDriftData where
  coefficient := fun t=>m*Ξ.second (projIcc 0 1 (by norm_num) t)*
    parisiCDF μ (projIcc 0 1 (by norm_num) t)
  gradient := fun t x=>temperatureMassGradient Ξ μ m (projIcc 0 1 (by norm_num) t) x
  radius := NNReal.mk (m*‖covarianceJetMap Ξ 2‖) (mul_nonneg hm.le (norm_nonneg _))
  gradientLip := m.toNNReal
  coefficient_measurable :=
    (measurable_const.mul ((Ξ.continuous_second.comp continuous_temperatureMassProjection).measurable)).mul
      ((Paper.parisiCDF_monotone μ).measurable.comp continuous_temperatureMassProjection.measurable)
  coefficient_bound := fun t=>by
    rw [norm_mul,norm_mul,Real.norm_eq_abs,abs_of_pos hm]
    have hX : ‖Ξ.second (projIcc 0 1 (by norm_num) t)‖≤‖covarianceJetMap Ξ 2‖ := by
      simpa only [covarianceJetMap_two] using
        (covarianceJetMap Ξ 2).norm_coe_le_norm (projIcc 0 1 (by norm_num) t)
    have hM : ‖Paper.parisiCDF μ (projIcc 0 1 (by norm_num) t)‖≤1 := by
      rw [Real.norm_eq_abs,abs_of_nonneg (Paper.parisiCDF_nonneg _ _)]
      exact Paper.parisiCDF_le_one _ _
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hX hm.le) hM
      (norm_nonneg _) (mul_nonneg hm.le (norm_nonneg _))).trans_eq (mul_one _)
  gradient_continuous := by
    let Ψ:=(temperatureCovarianceFamily Ξ).covariance m
    change Continuous (fun p:ℝ×ℝ=>Paper.parisiGradient (mixedBeta Ψ.toEvenMixture)
      (mixedMeasure Ψ.toEvenMixture μ) (Ψ.toEvenMixture.clock (projIcc 0 1 (by norm_num) p.1),m*p.2))
    simp only [AdmissibleCovariance.toEvenMixture_clock]
    exact (Paper.continuous_parisiGradient _ _).comp
      ((Ψ.continuous_clock.comp (continuous_temperatureMassProjection.comp continuous_fst)).prodMk
        (continuous_const.mul continuous_snd))
  gradient_bound := fun t x=>norm_gradient_le_one _ μ _ _
  gradient_lipschitz := fun t=>by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    let Ψ:=(temperatureCovarianceFamily Ξ).covariance m
    have H:=(Paper.lipschitzWith_parisiGradient (mixedBeta Ψ.toEvenMixture)
      (mixedBeta_ne_zero Ψ.toEvenMixture) (mixedMeasure Ψ.toEvenMixture μ)
      (Ψ.toEvenMixture.clock (projIcc 0 1 (by norm_num) t))).dist_le_mul (m*x) (m*y)
    simp only [NNReal.coe_one,one_mul,dist_eq_norm] at H
    rw [←mul_sub,norm_mul] at H
    simp only [Real.norm_eq_abs,abs_of_pos hm] at H
    change dist (temperatureMassGradient Ξ μ m (projIcc 0 1 (by norm_num) t) x)
      (temperatureMassGradient Ξ μ m (projIcc 0 1 (by norm_num) t) y)≤(m.toNNReal:ℝ)*dist x y
    rw [Real.coe_toNNReal _ hm.le]
    simpa only [dist_eq_norm,Real.norm_eq_abs,temperatureMassGradient,gradient,mixedGradient,Ψ] using H

def covarianceRateData (Ξ : AdmissibleCovariance) : NonnegativeRate where
  rate := fun t=>Ξ.second (projIcc 0 1 (by norm_num) (t:ℝ))
  continuous_rate := (Ξ.continuous_second.comp continuous_temperatureMassProjection).comp NNReal.continuous_coe
  nonneg := fun t=>Ξ.second_nonneg (projIcc _ _ _ (t:ℝ)).property.1

theorem covarianceRateData_clock (Ξ : AdmissibleCovariance) (q : ℝ≥0) (hq : (q:ℝ)≤1) :
    (rateClock (covarianceRateData Ξ) q:ℝ)=Ξ.first q := by
  change (∫s in (0:ℝ)..(q:ℝ),Ξ.second (projIcc 0 1 (by norm_num) (s.toNNReal:ℝ)))=Ξ.first q
  have he : (∫s in (0:ℝ)..(q:ℝ),Ξ.second (projIcc 0 1 (by norm_num) (s.toNNReal:ℝ)))=
      ∫s in (0:ℝ)..(q:ℝ),Ξ.second s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le q.coe_nonneg] at hs
    change Ξ.second (projIcc 0 1 (by norm_num) (s.toNNReal:ℝ))=Ξ.second s
    rw [Real.coe_toNNReal _ hs.1,projIcc_of_mem (by norm_num : (0:ℝ)≤1) ⟨hs.1,hs.2.trans hq⟩]
  rw [he,intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _=>Ξ.hasDerivAt_first s) (Ξ.continuous_second.intervalIntegrable _ _),Ξ.first_zero,sub_zero]

def temperatureMassState (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) (m : ℝ) (hm : 0 < m)
    (t : ℝ≥0) : BrownianSample→ℝ :=
  clockedItoState (temperatureMassDriftData Ξ μ m hm) (covarianceRateData Ξ) 0 1 (by norm_num) t

theorem temperatureMassState_characteristics (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (m : ℝ) (hm : 0 < m) :
    BoundedDriftVariableItoCharacteristics canonicalBrownianMeasure
      (timeChangedBrownianFiltration (rateClock (covarianceRateData Ξ))
        (monotone_rateClock (covarianceRateData Ξ)))
      (temperatureMassState Ξ μ m hm)
      (clockedItoDrift (temperatureMassDriftData Ξ μ m hm) (covarianceRateData Ξ) 0 1 (by norm_num))
      (timeChangedBrownian (rateClock (covarianceRateData Ξ))) (rateVolatility (covarianceRateData Ξ)) :=
  boundedDriftVariableItoCharacteristics_clockedItoState _ _ _ _ _

theorem temperatureMassState_integral_equation (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (m : ℝ) (hm : 0 < m) (q : ℝ≥0) (hq : (q:ℝ)≤1) (ω : BrownianSample) :
    temperatureMassState Ξ μ m hm q ω=canonicalBrownian (Ξ.first q).toNNReal ω+
      ∫s in (0:ℝ)..(q:ℝ),Ξ.second s*m*parisiCDF μ s*
        temperatureMassGradient Ξ μ m s (temperatureMassState Ξ μ m hm s.toNNReal ω) := by
  rw [temperatureMassState,clockedItoState_eq _ _ _ _ _ hq]
  have H:=clockedStateReal_integral_equation (temperatureMassDriftData Ξ μ m hm)
    (covarianceRateData Ξ) 0 1 (by norm_num) ω ⟨q.coe_nonneg,hq⟩
  rw [H]
  simp only [zero_add,rateNoiseReal,Real.toNNReal_coe,timeChangedBrownian]
  have hclock : rateClock (covarianceRateData Ξ) q=(Ξ.first q).toNNReal := by
    apply NNReal.coe_injective
    rw [covarianceRateData_clock Ξ q hq,Real.coe_toNNReal _ (Ξ.first_nonneg q.coe_nonneg)]
  rw [hclock]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le q.coe_nonneg] at hs
  have hsU : s∈Icc (0:ℝ) 1:=⟨hs.1,hs.2.trans hq⟩
  simp only [temperatureMassDriftData,projIcc_of_mem (by norm_num : (0:ℝ)≤1) hsU,
    temperatureMassState,clockedItoState_eq _ _ _ _ _
      (show (s.toNNReal:ℝ)≤1 by rw [Real.coe_toNNReal _ hs.1]; exact hsU.2),
    Real.coe_toNNReal _ hs.1]
  ring

end GeneralDepthPaper
