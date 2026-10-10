module

public import GeneralDepthPaper.TemperatureMassState

@[expose] public section


/-! A genuine whole-path law identifies the actual lower diffusion with
m⁻¹ times the selected diffusion of m²Ξ. Brownian rescaling and pathwise
integral uniqueness discharge the probabilistic change of variables. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GeneralDepthPaper
open FourPapersCommon Paper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

def covarianceBrownianClock (Ξ : AdmissibleCovariance) : C(TruncatedClockDomain 1,ℝ≥0) :=
  ⟨fun q=>(Ξ.first q).toNNReal,
    continuous_real_toNNReal.comp (Ξ.continuous_first.comp continuous_subtype_val)⟩

def temperatureMassNoiseScale (Ξ : AdmissibleCovariance) (m : ℝ) : ℝ :=
  mixedBeta ((temperatureCovarianceFamily Ξ).covariance m).toEvenMixture/m

theorem temperatureMassNoiseScale_ne (Ξ : AdmissibleCovariance) (m : ℝ) (hm : 0 < m) :
    temperatureMassNoiseScale Ξ m≠0 := div_ne_zero (mixedBeta_ne_zero _) hm.ne'

theorem temperatureMassNoiseScale_sq (Ξ : AdmissibleCovariance) (m : ℝ) (hm : 0 < m) :
    temperatureMassNoiseScale Ξ m^2=Ξ.first 1 := by
  rw [temperatureMassNoiseScale,div_pow,mixedBeta_sq,
    AdmissibleCovariance.toEvenMixture_variance,AdmissibleCovariance.variance,
    temperatureCovarianceFamily_covariance Ξ m hm.ne',Ξ.temperatureScale_first]
  field_simp

def temperatureMassOptimalPath (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) (m : ℝ)
    (ω : BrownianSample) : C(TruncatedClockDomain 1,ℝ) :=
  ⟨fun q=>m⁻¹*optimalState ((temperatureCovarianceFamily Ξ).covariance m) μ ω q,by
    let Ψ:=(temperatureCovarianceFamily Ξ).covariance m
    change Continuous (fun q:TruncatedClockDomain 1=>m⁻¹*
      Paper.selectedParisiStateReal (mixedBeta Ψ.toEvenMixture) 0 (mixedBeta_ne_zero Ψ.toEvenMixture)
        (mixedMeasure Ψ.toEvenMixture μ) ω (Ψ.toEvenMixture.clock q))
    simp only [AdmissibleCovariance.toEvenMixture_clock]
    exact ((Paper.continuous_selectedParisiStateReal _ _ _ _ ω).comp
      (Ψ.continuous_clock.comp continuous_subtype_val)).const_mul m⁻¹⟩

theorem temperatureMassOptimalNoise_eq_rescaled (Ξ : AdmissibleCovariance) (m : ℝ)
    (hm : 0 < m) (ω : BrownianSample) (q : TruncatedClockDomain 1) :
    m⁻¹*mixedBeta ((temperatureCovarianceFamily Ξ).covariance m).toEvenMixture*
      canonicalBrownian (((temperatureCovarianceFamily Ξ).covariance m).clock q).toNNReal ω=
      rescaledClockBrownianPath (temperatureMassNoiseScale Ξ m) (covarianceBrownianClock Ξ) ω q := by
  have hcoef : m⁻¹*mixedBeta ((temperatureCovarianceFamily Ξ).covariance m).toEvenMixture=
      temperatureMassNoiseScale Ξ m := by
    unfold temperatureMassNoiseScale
    field_simp
  rw [hcoef]
  change _=temperatureMassNoiseScale Ξ m*canonicalBrownian
    ((Ξ.first q).toNNReal/(temperatureMassNoiseScale Ξ m^2).toNNReal) ω
  congr 2
  apply NNReal.coe_injective
  rw [NNReal.coe_div,Real.coe_toNNReal _
      (((temperatureCovarianceFamily Ξ).covariance m).clock_mem_unit q.property).1,
    Real.coe_toNNReal _ (Ξ.first_nonneg q.property.1),
    Real.coe_toNNReal _ (sq_nonneg _),temperatureMassNoiseScale_sq Ξ m hm]
  unfold AdmissibleCovariance.clock AdmissibleCovariance.variance
  rw [temperatureCovarianceFamily_covariance Ξ m hm.ne',Ξ.temperatureScale_first,Ξ.temperatureScale_first]
  field_simp

theorem temperatureMassOptimalPath_eq_additive (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (m : ℝ) (hm : 0 < m) (ω : BrownianSample) :
    temperatureMassOptimalPath Ξ μ m ω=
      additiveStatePath (temperatureMassDriftData Ξ μ m hm) 0 1 (by norm_num)
        (rescaledClockBrownianPath (temperatureMassNoiseScale Ξ m) (covarianceBrownianClock Ξ) ω) := by
  let Ψ:=(temperatureCovarianceFamily Ξ).covariance m
  let d:=temperatureMassDriftData Ξ μ m hm
  let W:=rescaledClockBrownianPath (temperatureMassNoiseScale Ξ m) (covarianceBrownianClock Ξ) ω
  let X:=Paper.parisiNoiseExtension (by norm_num : (0:ℝ)≤1) (temperatureMassOptimalPath Ξ μ m ω)
  have hX:=Paper.continuous_parisiNoiseExtension (by norm_num : (0:ℝ)≤1) (temperatureMassOptimalPath Ξ μ m ω)
  have hx (t:ℝ) (ht:t∈Icc (0:ℝ) 1) : X t=m⁻¹*optimalState Ψ μ ω t := by
    simp only [X,Paper.parisiNoiseExtension,projIcc_of_mem (by norm_num : (0:ℝ)≤1) ht,
      temperatureMassOptimalPath,ContinuousMap.coe_mk,Ψ]
  have heq : ∀t∈Icc (0:ℝ) 1,X t=0+Paper.parisiNoiseExtension (by norm_num : (0:ℝ)≤1) W t+
      ∫s in (0:ℝ)..t,d.coefficient s*d.gradient s (X s) := by
    intro t ht
    have hn : Paper.parisiNoiseExtension (by norm_num : (0:ℝ)≤1) W t=
        m⁻¹*mixedBeta Ψ.toEvenMixture*canonicalBrownian (Ψ.clock t).toNNReal ω := by
      rw [Paper.parisiNoiseExtension,projIcc_of_mem (by norm_num : (0:ℝ)≤1) ht]
      exact (temperatureMassOptimalNoise_eq_rescaled Ξ m hm ω ⟨t,ht⟩).symm
    rw [hx t ht,hn,optimalState_integral_equation Ψ μ ω ht,zero_add,mul_add,
      ←mul_assoc m⁻¹,←intervalIntegral.integral_const_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    have hsU:s∈Icc (0:ℝ) 1:=⟨hs.1,hs.2.trans ht.2⟩
    dsimp only [d,temperatureMassDriftData,temperatureMassGradient]
    rw [projIcc_of_mem (by norm_num : (0:ℝ)≤1) hsU,hx s hsU,
      show m*(m⁻¹*optimalState Ψ μ ω s)=optimalState Ψ μ ω s by field_simp]
    dsimp only [Ψ]
    rw [temperatureCovarianceFamily_covariance Ξ m hm.ne',Ξ.temperatureScale_second]
    field_simp
  have hu:=additiveStateReal_unique d 0 1 (by norm_num)
    (Paper.parisiNoiseExtension (by norm_num : (0:ℝ)≤1) W)
    (Paper.continuous_parisiNoiseExtension (by norm_num : (0:ℝ)≤1) W) X hX heq
  ext q
  rw [additiveStatePath_apply]
  exact (show X q=temperatureMassOptimalPath Ξ μ m ω q by
    simp only [X,Paper.parisiNoiseExtension,projIcc_val]).symm.trans (hu q.property)

def temperatureMassStatePath (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) (m : ℝ) (hm : 0 < m)
    (ω : BrownianSample) : C(TruncatedClockDomain 1,ℝ) :=
  ⟨fun q=>temperatureMassState Ξ μ m hm (q:ℝ).toNNReal ω,
    (continuous_clockedItoState _ _ _ _ _ ω).comp
      (continuous_real_toNNReal.comp continuous_subtype_val)⟩

theorem temperatureMassStatePath_eq_additive (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (m : ℝ) (hm : 0 < m) (ω : BrownianSample) :
    temperatureMassStatePath Ξ μ m hm ω=
      additiveStatePath (temperatureMassDriftData Ξ μ m hm) 0 1 (by norm_num)
        (clockBrownianPath (covarianceBrownianClock Ξ) ω) := by
  have hnoise : rateNoisePath (covarianceRateData Ξ) 1 ω=clockBrownianPath (covarianceBrownianClock Ξ) ω := by
    ext q
    change canonicalBrownian (rateClock (covarianceRateData Ξ) (q:ℝ).toNNReal) ω=
      canonicalBrownian (Ξ.first q).toNNReal ω
    congr 1
    apply NNReal.coe_injective
    rw [covarianceRateData_clock Ξ _ (by simpa only [Real.coe_toNNReal _ q.property.1] using q.property.2),
      Real.coe_toNNReal _ q.property.1,Real.coe_toNNReal _ (Ξ.first_nonneg q.property.1)]
  ext q
  change clockedItoState _ _ _ _ _ (q:ℝ).toNNReal ω=_
  rw [clockedItoState_eq _ _ _ _ _ (by simpa only [Real.coe_toNNReal _ q.property.1] using q.property.2),
    Real.coe_toNNReal _ q.property.1,clockedStateReal_eq_path,hnoise]

theorem temperature_mass_state_path_law (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (m : ℝ) (hm : 0 < m) :
    canonicalBrownianMeasure.map (temperatureMassStatePath Ξ μ m hm)=
      canonicalBrownianMeasure.map (temperatureMassOptimalPath Ξ μ m) := by
  have hL:=clockBrownianPath_rescaling_law (temperatureMassNoiseScale Ξ m)
    (temperatureMassNoiseScale_ne Ξ m hm) (covarianceBrownianClock Ξ)
  rw [show temperatureMassStatePath Ξ μ m hm=(fun ω=>additiveStatePath (temperatureMassDriftData Ξ μ m hm)
    0 1 (by norm_num) (clockBrownianPath (covarianceBrownianClock Ξ) ω)) from
      funext (temperatureMassStatePath_eq_additive Ξ μ m hm),
    show temperatureMassOptimalPath Ξ μ m=(fun ω=>additiveStatePath (temperatureMassDriftData Ξ μ m hm)
      0 1 (by norm_num) (rescaledClockBrownianPath (temperatureMassNoiseScale Ξ m) (covarianceBrownianClock Ξ) ω))
      from funext (temperatureMassOptimalPath_eq_additive Ξ μ m hm)]
  have hh:=congrArg (fun ν:Measure C(TruncatedClockDomain 1,ℝ)=>
    ν.map (additiveStatePath (temperatureMassDriftData Ξ μ m hm) 0 1 (by norm_num))) hL
  rw [Measure.map_map (measurable_additiveStatePath _ _ _ _) (measurable_clockBrownianPath _),
    Measure.map_map (measurable_additiveStatePath _ _ _ _) (measurable_rescaledClockBrownianPath _ _)] at hh
  simpa only [Function.comp_def] using hh

end GeneralDepthPaper
