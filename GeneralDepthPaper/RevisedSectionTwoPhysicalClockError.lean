module

public import GeneralDepthPaper.RevisedSectionTwoPhysicalClockTransport

@[expose] public section

/-! Exact deterministic errors when a physical-volatility left step is
compared with the same normalized covariance-clock noise. The bound uses
monotonicity and includes a zero origin volatility. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus
open scoped Topology NNReal ENNReal InnerProductSpace
namespace GeneralDepthPaper
open FourPapersCommon
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 64

/-- Error in one physical-clock cell, as an actual deterministic `L²` function. -/
def sectionTwoPhysicalClockCellError (Ξ : AdmissibleCovariance) (a b : Overlap) :
    Lp ℝ 2 nonnegativeLebesgueMeasure :=
  Real.sqrt (Ξ.second a) •
    (sectionTwoPhysicalBrownianKernelLp Ξ b-sectionTwoPhysicalBrownianKernelLp Ξ a)-
  mixedBeta Ξ.toEvenMixture •
    (intervalIndicator (sectionTwoBrownianTime Ξ b)-intervalIndicator (sectionTwoBrownianTime Ξ a))

theorem norm_sq_sectionTwoPhysicalBrownianKernelLp_sub (Ξ : AdmissibleCovariance)
    (a b : Overlap) (hab : a ≤ b) :
    ‖sectionTwoPhysicalBrownianKernelLp Ξ b-sectionTwoPhysicalBrownianKernelLp Ξ a‖^2=
      (b:ℝ)-(a:ℝ) := by
  rw [norm_sub_sq_real,norm_sq_sectionTwoPhysicalBrownianKernelLp,
    norm_sq_sectionTwoPhysicalBrownianKernelLp,inner_sectionTwoPhysicalBrownianKernelLp,
    min_eq_right (show (a:ℝ) ≤ (b:ℝ) from hab)]
  ring

theorem inner_sectionTwoPhysicalBrownianKernelLp_sub_original_driver
    (Ξ : AdmissibleCovariance) (a b : Overlap) (hab : a ≤ b) :
    ⟪sectionTwoPhysicalBrownianKernelLp Ξ b-sectionTwoPhysicalBrownianKernelLp Ξ a,
      mixedBeta Ξ.toEvenMixture •
        (intervalIndicator (sectionTwoBrownianTime Ξ b)-intervalIndicator (sectionTwoBrownianTime Ξ a))⟫_ℝ=
      ∫u in (a:ℝ)..(b:ℝ),Real.sqrt (Ξ.second u) := by
  rw [smul_sub,inner_sub_left,inner_sub_right,inner_sub_right]
  simp only [inner_sectionTwoPhysicalBrownianKernelLp_original_driver,
    min_self,min_eq_left (show (a:ℝ) ≤ (b:ℝ) from hab),
    min_eq_right (show (a:ℝ) ≤ (b:ℝ) from hab)]
  simp only [sub_self,sub_zero]
  exact intervalIntegral.integral_interval_sub_left
    (Ξ.continuous_second.sqrt.intervalIntegrable _ _)
    (Ξ.continuous_second.sqrt.intervalIntegrable _ _)

theorem norm_sq_sectionTwo_original_driver_sub (Ξ : AdmissibleCovariance)
    (a b : Overlap) (hab : a ≤ b) :
    ‖mixedBeta Ξ.toEvenMixture •
      (intervalIndicator (sectionTwoBrownianTime Ξ b)-intervalIndicator (sectionTwoBrownianTime Ξ a))‖^2=
      ∫u in (a:ℝ)..(b:ℝ),(Real.sqrt (Ξ.second u))^2 := by
  have hclock : sectionTwoBrownianTime Ξ a ≤ sectionTwoBrownianTime Ξ b := by
    change (Ξ.clock a).toNNReal ≤ (Ξ.clock b).toNNReal
    exact Real.toNNReal_le_toNNReal (Ξ.clock_strictMonoOn.monotoneOn a.property.1 b.property.1 hab)
  have hβ : (mixedBeta Ξ.toEvenMixture)^2=Ξ.variance := by
    rw [mixedBeta_sq,AdmissibleCovariance.toEvenMixture_variance]
  have hnorm : ‖intervalIndicator (sectionTwoBrownianTime Ξ b)-
      intervalIndicator (sectionTwoBrownianTime Ξ a)‖^2=
      ((sectionTwoBrownianTime Ξ b):ℝ)-(sectionTwoBrownianTime Ξ a) := by
    rw [norm_sub_sq_real,←real_inner_self_eq_norm_sq,←real_inner_self_eq_norm_sq,
      inner_intervalIndicator,inner_intervalIndicator,inner_intervalIndicator,
      min_self,min_self,min_eq_right (show ((sectionTwoBrownianTime Ξ a):ℝ) ≤
        ((sectionTwoBrownianTime Ξ b):ℝ) from hclock)]
    ring
  have hintegral : (∫u in (a:ℝ)..(b:ℝ),(Real.sqrt (Ξ.second u))^2)=
      Ξ.first b-Ξ.first a := by
    calc
      _ = ∫u in (a:ℝ)..(b:ℝ),Ξ.second u := by
        apply intervalIntegral.integral_congr_Ioo_of_le hab
        intro u hu
        exact Real.sq_sqrt (Ξ.second_pos (lt_of_le_of_lt a.property.1 hu.1)).le
      _ = _ := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun u _=>Ξ.hasDerivAt_first u) (Ξ.continuous_second.intervalIntegrable _ _)
  rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,hnorm,hβ,hintegral]
  rw [show ((sectionTwoBrownianTime Ξ b):ℝ)=Ξ.clock b from
      Real.coe_toNNReal _ (Ξ.clock_mem_unit b.property).1,
    show ((sectionTwoBrownianTime Ξ a):ℝ)=Ξ.clock a from
      Real.coe_toNNReal _ (Ξ.clock_mem_unit a.property).1]
  unfold AdmissibleCovariance.clock
  field_simp [Ξ.variance_pos.ne']

/-- The exact one-cell mean-square error under the physical clock. -/
theorem norm_sq_sectionTwoPhysicalClockCellError (Ξ : AdmissibleCovariance)
    (a b : Overlap) (hab : a ≤ b) :
    ‖sectionTwoPhysicalClockCellError Ξ a b‖^2=
      ∫u in (a:ℝ)..(b:ℝ),(Real.sqrt (Ξ.second a)-Real.sqrt (Ξ.second u))^2 := by
  have hs : IntervalIntegrable (fun u=>Real.sqrt (Ξ.second u)) volume (a:ℝ) b :=
    Ξ.continuous_second.sqrt.intervalIntegrable _ _
  have hs2 : IntervalIntegrable (fun u=>(Real.sqrt (Ξ.second u))^2) volume (a:ℝ) b :=
    (Ξ.continuous_second.sqrt.pow 2).intervalIntegrable _ _
  have hconst : IntervalIntegrable (fun _ : ℝ=>(Real.sqrt (Ξ.second a))^2) volume (a:ℝ) b :=
    intervalIntegrable_const
  have he : (∫u in (a:ℝ)..(b:ℝ),(Real.sqrt (Ξ.second a)-Real.sqrt (Ξ.second u))^2)=
      (Real.sqrt (Ξ.second a))^2*((b:ℝ)-(a:ℝ))-
      2*Real.sqrt (Ξ.second a)*(∫u in (a:ℝ)..(b:ℝ),Real.sqrt (Ξ.second u))+
      (∫u in (a:ℝ)..(b:ℝ),(Real.sqrt (Ξ.second u))^2) := by
    calc
      _ = ∫u in (a:ℝ)..(b:ℝ),(Real.sqrt (Ξ.second a))^2-
          (2*Real.sqrt (Ξ.second a))*Real.sqrt (Ξ.second u)+(Real.sqrt (Ξ.second u))^2 := by
        apply intervalIntegral.integral_congr
        intro u _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add (hconst.sub (hs.const_mul _)) hs2,
          intervalIntegral.integral_sub hconst (hs.const_mul _),
          intervalIntegral.integral_const_mul,intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
  rw [sectionTwoPhysicalClockCellError,norm_sub_sq_real,
    real_inner_smul_left,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,
    norm_sq_sectionTwoPhysicalBrownianKernelLp_sub Ξ a b hab,
    inner_sectionTwoPhysicalBrownianKernelLp_sub_original_driver Ξ a b hab,
    norm_sq_sectionTwo_original_driver_sub Ξ a b hab,he]
  ring


theorem sqrt_second_monotone_unit (Ξ : AdmissibleCovariance) (a b : Overlap)
    (hab : a ≤ b) : Real.sqrt (Ξ.second a) ≤ Real.sqrt (Ξ.second b) := by
  have h := physicalVolatility_monotone Ξ
    (Real.toNNReal_le_toNNReal (show (a:ℝ) ≤ (b:ℝ) from hab))
  simpa only [physicalVolatility_eq,Real.coe_toNNReal _ a.property.1,
    Real.coe_toNNReal _ b.property.1] using h

/-- A sharp monotone-volatility bound for each deterministic physical cell. -/
theorem norm_sectionTwoPhysicalClockCellError_le (Ξ : AdmissibleCovariance)
    (a b : Overlap) (hab : a ≤ b) :
    ‖sectionTwoPhysicalClockCellError Ξ a b‖ ≤
      (Real.sqrt (Ξ.second b)-Real.sqrt (Ξ.second a))*Real.sqrt ((b:ℝ)-(a:ℝ)) := by
  have hσ := sqrt_second_monotone_unit Ξ a b hab
  have hσdiff : 0 ≤ Real.sqrt (Ξ.second b)-Real.sqrt (Ξ.second a) := sub_nonneg.mpr hσ
  have htime : 0 ≤ (b:ℝ)-(a:ℝ) := sub_nonneg.mpr hab
  have hf : IntervalIntegrable
      (fun u=>(Real.sqrt (Ξ.second a)-Real.sqrt (Ξ.second u))^2) volume (a:ℝ) b :=
    ((continuous_const.sub Ξ.continuous_second.sqrt).pow 2).intervalIntegrable _ _
  have he : ‖sectionTwoPhysicalClockCellError Ξ a b‖^2 ≤
      ((b:ℝ)-(a:ℝ))*(Real.sqrt (Ξ.second b)-Real.sqrt (Ξ.second a))^2 := by
    rw [norm_sq_sectionTwoPhysicalClockCellError Ξ a b hab]
    calc
      _ ≤ ∫u in (a:ℝ)..(b:ℝ),(Real.sqrt (Ξ.second b)-Real.sqrt (Ξ.second a))^2 := by
        apply intervalIntegral.integral_mono_on hab hf intervalIntegrable_const
        intro u hu
        let uo : Overlap := ⟨u,⟨a.property.1.trans hu.1,hu.2.trans b.property.2⟩⟩
        have hsa := sqrt_second_monotone_unit Ξ a uo hu.1
        have hsb := sqrt_second_monotone_unit Ξ uo b hu.2
        rw [sub_sq_comm]
        exact pow_le_pow_left₀ (sub_nonneg.mpr hsa) (sub_le_sub_right hsb _) 2
      _ = _ := by rw [intervalIntegral.integral_const]; rfl
  have hright : 0 ≤ (Real.sqrt (Ξ.second b)-Real.sqrt (Ξ.second a))*
      Real.sqrt ((b:ℝ)-(a:ℝ)) := mul_nonneg hσdiff (Real.sqrt_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) hright).mp
  rw [mul_pow,Real.sq_sqrt htime,mul_comm]
  exact he

end GeneralDepthPaper
