module

public import GeneralDepthPaper.TemperatureMassStateLaw

@[expose] public section


/-! Actual diffusion expectations and first variation under the temperature–
mass change of variables. Whole-path law equality is proved, not supplied. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GeneralDepthPaper
open FourPapersCommon Paper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem measurable_temperatureMassStatePath (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (m : ℝ) (hm : 0 < m) : Measurable (temperatureMassStatePath Ξ μ m hm) := by
  rw [show temperatureMassStatePath Ξ μ m hm=(fun ω=>additiveStatePath (temperatureMassDriftData Ξ μ m hm)
    0 1 (by norm_num) (clockBrownianPath (covarianceBrownianClock Ξ) ω)) from
      funext (temperatureMassStatePath_eq_additive Ξ μ m hm)]
  exact (measurable_additiveStatePath _ _ _ _).comp (measurable_clockBrownianPath _)

theorem measurable_temperatureMassOptimalPath (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (m : ℝ) (hm : 0 < m) : Measurable (temperatureMassOptimalPath Ξ μ m) := by
  rw [show temperatureMassOptimalPath Ξ μ m=(fun ω=>additiveStatePath (temperatureMassDriftData Ξ μ m hm)
    0 1 (by norm_num) (rescaledClockBrownianPath (temperatureMassNoiseScale Ξ m) (covarianceBrownianClock Ξ) ω))
      from funext (temperatureMassOptimalPath_eq_additive Ξ μ m hm)]
  exact (measurable_additiveStatePath _ _ _ _).comp (measurable_rescaledClockBrownianPath _ _)

def temperatureMassGamma (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) (m : ℝ) (hm : 0 < m)
    (q : ℝ) : ℝ :=
  ∫ω,temperatureMassGradient Ξ μ m q (temperatureMassState Ξ μ m hm q.toNNReal ω)^2
    ∂canonicalBrownianMeasure

theorem temperature_mass_Gamma (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (m : ℝ) (hm : 0 < m) {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    temperatureMassGamma Ξ μ m hm q=Gamma ((temperatureCovarianceFamily Ξ).covariance m) μ q := by
  let qI:TruncatedClockDomain 1:=⟨q,hq⟩
  let F:C(TruncatedClockDomain 1,ℝ)→ℝ:=fun w=>
    (temperatureMassDriftData Ξ μ m hm).gradient q (w qI)^2
  have hF : Continuous F := by
    exact ((temperatureMassDriftData Ξ μ m hm).gradient_continuous.comp
      (continuous_const.prodMk (continuous_eval_const qI))).pow 2
  have he:=congrArg (fun ν:Measure C(TruncatedClockDomain 1,ℝ)=>∫w,F w ∂ν)
    (temperature_mass_state_path_law Ξ μ m hm)
  rw [integral_map (measurable_temperatureMassStatePath Ξ μ m hm).aemeasurable hF.aestronglyMeasurable,
    integral_map (measurable_temperatureMassOptimalPath Ξ μ m hm).aemeasurable hF.aestronglyMeasurable] at he
  dsimp only [F,temperatureMassDriftData,Function.comp_def] at he
  rw [projIcc_of_mem (by norm_num : (0:ℝ)≤1) hq] at he
  change temperatureMassGamma Ξ μ m hm q=
    ∫ω,temperatureMassGradient Ξ μ m q
      (m⁻¹*optimalState ((temperatureCovarianceFamily Ξ).covariance m) μ ω q)^2
        ∂canonicalBrownianMeasure at he
  rw [he]
  change (∫ω,gradient ((temperatureCovarianceFamily Ξ).covariance m) μ q
    (m*(m⁻¹*optimalState ((temperatureCovarianceFamily Ξ).covariance m) μ ω q))^2
      ∂canonicalBrownianMeasure)=_
  simp_rw [show ∀y:ℝ,m*(m⁻¹*y)=y from fun y=>by field_simp]
  rfl

theorem temperature_mass_firstVariation (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (m : ℝ) (hm : 0 < m) {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    (1/2:ℝ)*(∫s in (0:ℝ)..q,Ξ.second s*(temperatureMassGamma Ξ μ m hm s-s))=
      (m^2)⁻¹*firstVariation ((temperatureCovarianceFamily Ξ).covariance m) μ q := by
  rw [firstVariation_eq]
  have he : (∫s in (0:ℝ)..q,
      ((temperatureCovarianceFamily Ξ).covariance m).second s*
        (Gamma ((temperatureCovarianceFamily Ξ).covariance m) μ s-s))=
      m^2*∫s in (0:ℝ)..q,Ξ.second s*(temperatureMassGamma Ξ μ m hm s-s) := by
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hq.1] at hs
    change ((temperatureCovarianceFamily Ξ).covariance m).second s*
      (Gamma ((temperatureCovarianceFamily Ξ).covariance m) μ s-s)=
      m^2*(Ξ.second s*(temperatureMassGamma Ξ μ m hm s-s))
    rw [temperature_mass_Gamma Ξ μ m hm ⟨hs.1,hs.2.trans hq.2⟩]
    rw [temperatureCovarianceFamily_covariance Ξ m hm.ne',Ξ.temperatureScale_second,
      ]
    ring
  rw [he]
  field_simp

end GeneralDepthPaper
