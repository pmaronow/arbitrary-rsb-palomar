module

public import GeneralDepthPaper.RevisedSectionTwoPartition
public import GeneralDepthPaper.TemperatureMassMoments
public import GeneralDepthPaper.TemperatureMassUnique

@[expose] public section

/-! Appendix A.7 with an independently constructed lower SDE solution driven
by the same actual Brownian sample and original normalized covariance clock
as the upper optimal state. Its moments equal the actual truncated-data
moments, proved through pathwise uniqueness and the existing Brownian
rescaling law. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GeneralDepthPaper
open FourPapersCommon Paper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

theorem revised_temperatureMassNoiseScale_eq_beta (Ξ : AdmissibleCovariance)
    (m : ℝ) (hm : 0 < m) : temperatureMassNoiseScale Ξ m = mixedBeta Ξ.toEvenMixture := by
  have hs := temperatureMassNoiseScale_sq Ξ m hm
  have hb := mixedBeta_sq Ξ.toEvenMixture
  rw [AdmissibleCovariance.toEvenMixture_variance,AdmissibleCovariance.variance] at hb
  have hp : 0 < temperatureMassNoiseScale Ξ m :=
    div_pos (mixedBeta_pos _) hm
  have hbpos := mixedBeta_pos Ξ.toEvenMixture
  nlinarith

def sectionTwoOriginalNoiseReal (Ξ : AdmissibleCovariance) (sample : BrownianSample) : ℝ → ℝ :=
  Paper.parisiNoiseExtension (by norm_num : (0:ℝ) ≤ 1)
    (rescaledClockBrownianPath (mixedBeta Ξ.toEvenMixture) (covarianceBrownianClock Ξ) sample)

@[fun_prop] theorem continuous_sectionTwoOriginalNoiseReal
    (Ξ : AdmissibleCovariance) (sample : BrownianSample) :
    Continuous (sectionTwoOriginalNoiseReal Ξ sample) :=
  Paper.continuous_parisiNoiseExtension _ _

/-- The lower solution, constructed from the literal lower data and the
original-clock Brownian driver shared with the upper optimal diffusion. -/
def sectionTwoCommonNoiseState {r : ℕ} {qc : ℝ}
    (d : TruncatedParisiData r qc) (Ξ : AdmissibleCovariance) (sample : BrownianSample) : ℝ → ℝ :=
  additiveStateReal d.driftData 0 qc d.qc_pos.le (sectionTwoOriginalNoiseReal Ξ sample)
    (continuous_sectionTwoOriginalNoiseReal Ξ sample)

section LowerData
variable (Ξ : AdmissibleCovariance) (ν : ParisiMeasure)
  (m : ℝ) (hm : m∈Ioc (0:ℝ) 1) (qc : ℝ) (hc : qc∈Ioc (0:ℝ) 1)
  {r : ℕ} (node : Fin (r+2)→TruncatedClockDomain qc)
  (hn : StrictMono node) (h0 : (node 0:ℝ)=0)
  (hlast : (node (Fin.last (r+1)):ℝ)=qc)
  (hCDF : ∀i:Fin (r+1),∀s∈Ico (node i.castSucc:ℝ) (node i.succ:ℝ),
    Paper.parisiCDF ν s=Paper.parisiCDF ν (node i.castSucc))
  (hs : ∀s∈FRSB.parisiSupport ν,s≤qc)

local notation "D" => sectionTwoLowerData Ξ ν m hm qc hc node hn h0 hlast

theorem revised_sectionTwo_rateClock (q : ℝ≥0) (hq : (q:ℝ) ≤ qc) :
    rateClock (D).rateData q = (Ξ.first q).toNNReal := by
  have hd : dist (rateClock (D).rateData q) (rateClock (covarianceRateData Ξ) q) ≤ 0 := by
    have H := rateClock_dist_le_of_rate_bound (D).rateData (covarianceRateData Ξ) hc.1.le
      (le_refl (0:ℝ)) (fun s hs => ?_) q hq
    · simpa using H
    · change ‖(D).covarianceField 2 (s.toNNReal:ℝ)-
        Ξ.second (projIcc 0 1 (by norm_num) (s.toNNReal:ℝ))‖ ≤ 0
      rw [Real.coe_toNNReal _ hs.1,
        sectionTwoLowerData_covarianceField_two Ξ ν m hm qc hc node hn h0 hlast s hs,
        projIcc_of_mem (by norm_num : (0:ℝ)≤1) ⟨hs.1,hs.2.trans hc.2⟩]
      simp
  have he := dist_eq_zero.mp (le_antisymm hd (dist_nonneg))
  rw [he]
  apply NNReal.coe_injective
  rw [covarianceRateData_clock Ξ q (hq.trans hc.2),
    Real.coe_toNNReal _ (Ξ.first_nonneg q.coe_nonneg)]

include hCDF hs

/-- The old variance-clock realization of the independently constructed
truncated diffusion is exactly the general lower SDE realization. -/
theorem revised_sectionTwo_state_eq_temperatureMassState (sample : BrownianSample)
    (q : ℝ) (hq : q∈Icc (0:ℝ) qc) :
    (D).state q.toNNReal sample = temperatureMassState Ξ ν m hm.1 q.toNNReal sample := by
  let X : ℝ → ℝ := fun t => (D).state t.toNNReal sample
  have hX : Continuous X := ((D).continuous_state sample).comp continuous_real_toNNReal
  have heq : ∀t∈Icc (0:ℝ) qc, X t=canonicalBrownian (Ξ.first t).toNNReal sample+
      ∫s in (0:ℝ)..t,Ξ.second s*m*parisiCDF ν s*temperatureMassGradient Ξ ν m s (X s) := by
    intro t ht
    have H := (D).state_integral_equation t.toNNReal
      (by rw [Real.coe_toNNReal _ ht.1]; exact ht.2) sample
    rw [Real.coe_toNNReal _ ht.1] at H
    dsimp only [X]
    rw [H]
    simp only [timeChangedBrownian,
      revised_sectionTwo_rateClock Ξ ν m hm qc hc node hn h0 hlast t.toNNReal
        (by rw [Real.coe_toNNReal _ ht.1]; exact ht.2),
      Real.coe_toNNReal _ ht.1]
    congr 1
    apply intervalIntegral.integral_congr_Ioo_of_le ht.1
    intro s hs'
    dsimp only
    have hsu : s∈Icc (0:ℝ) qc := ⟨hs'.1.le,hs'.2.le.trans ht.2⟩
    rw [sectionTwoLowerData_covarianceField_two Ξ ν m hm qc hc node hn h0 hlast s hsu,
      sectionTwoLowerData_coefficient Ξ ν m hm qc hc node hn h0 hlast hCDF s
        ⟨hs'.1.le,hs'.2.trans_le ht.2⟩,
      sectionTwoLowerData_spatialField_zero Ξ ν m hm qc hc node hn h0 hlast hCDF hs s hsu]
    ring
  exact temperatureMassState_unique Ξ ν m hm.1 qc ⟨hc.1.le,hc.2⟩ sample X hX heq q hq

/-- Pointwise same-driver identity, including every endpoint and every
Brownian sample. The lower state is independently solved from its drift. -/
theorem revised_sectionTwo_common_driver_scaling (sample : BrownianSample)
    (q : ℝ) (hq : q∈Icc (0:ℝ) qc) :
    sectionTwoCommonNoiseState D Ξ sample q =
      m⁻¹*optimalState (Ξ.temperatureScale m hm.1.ne') ν sample q := by
  let X := Paper.parisiNoiseExtension (by norm_num : (0:ℝ)≤1)
    (temperatureMassOptimalPath Ξ ν m sample)
  have hX : Continuous X := Paper.continuous_parisiNoiseExtension _ _
  have hx (t : ℝ) (ht : t∈Icc (0:ℝ) qc) :
      X t=m⁻¹*optimalState ((temperatureCovarianceFamily Ξ).covariance m) ν sample t := by
    simp only [X,Paper.parisiNoiseExtension,projIcc_of_mem (by norm_num : (0:ℝ)≤1)
      ⟨ht.1,ht.2.trans hc.2⟩,temperatureMassOptimalPath,ContinuousMap.coe_mk]
  have heq : ∀t∈Icc (0:ℝ) qc, X t=0+sectionTwoOriginalNoiseReal Ξ sample t+
      ∫s in (0:ℝ)..t,(D).driftData.coefficient s*(D).driftData.gradient s (X s) := by
    intro t ht
    have hn0 : sectionTwoOriginalNoiseReal Ξ sample t=
        m⁻¹*mixedBeta ((temperatureCovarianceFamily Ξ).covariance m).toEvenMixture*
          canonicalBrownian (((temperatureCovarianceFamily Ξ).covariance m).clock t).toNNReal sample := by
      unfold sectionTwoOriginalNoiseReal
      rw [Paper.parisiNoiseExtension,projIcc_of_mem (by norm_num : (0:ℝ)≤1) ⟨ht.1,ht.2.trans hc.2⟩]
      rw [←revised_temperatureMassNoiseScale_eq_beta Ξ m hm.1]
      exact (temperatureMassOptimalNoise_eq_rescaled Ξ m hm.1 sample
        ⟨t,ht.1,ht.2.trans hc.2⟩).symm
    rw [hx t ht,hn0,zero_add,optimalState_integral_equation _ ν sample ⟨ht.1,ht.2.trans hc.2⟩,
      mul_add,←mul_assoc m⁻¹,←intervalIntegral.integral_const_mul]
    congr 1
    apply intervalIntegral.integral_congr_Ioo_of_le ht.1
    intro s hs'
    dsimp only
    have hsu : s∈Icc (0:ℝ) qc := ⟨hs'.1.le,hs'.2.le.trans ht.2⟩
    dsimp only [TruncatedParisiData.driftData]
    rw [sectionTwoLowerData_covarianceField_two Ξ ν m hm qc hc node hn h0 hlast s hsu,
      sectionTwoLowerData_coefficient Ξ ν m hm qc hc node hn h0 hlast hCDF s
        ⟨hs'.1.le,hs'.2.trans_le ht.2⟩,
      sectionTwoLowerData_spatialField_zero Ξ ν m hm qc hc node hn h0 hlast hCDF hs s hsu,
      hx s hsu]
    unfold temperatureMassGradient
    rw [show m*(m⁻¹*optimalState ((temperatureCovarianceFamily Ξ).covariance m) ν sample s)=
      optimalState ((temperatureCovarianceFamily Ξ).covariance m) ν sample s by field_simp [hm.1.ne']]
    rw [temperatureCovarianceFamily_covariance Ξ m hm.1.ne',Ξ.temperatureScale_second]
    field_simp [hm.1.ne']
  have hu := additiveStateReal_unique (D).driftData 0 qc hc.1.le
    (sectionTwoOriginalNoiseReal Ξ sample) (continuous_sectionTwoOriginalNoiseReal Ξ sample) X hX heq
  rw [←temperatureCovarianceFamily_covariance Ξ m hm.1.ne']
  exact (hu hq).symm.trans (hx q hq)

/-- Lemma A.7's exact path and observable formulas for the actual finite
lower recursion, rather than merely equality in distribution. -/
theorem revised_temperature_mass_diffusion :
    (∀sample q, q∈Icc (0:ℝ) qc → sectionTwoCommonNoiseState D Ξ sample q =
      m⁻¹*optimalState (Ξ.temperatureScale m hm.1.ne') ν sample q) ∧
    (∀q∈Icc (0:ℝ) qc, (D).Gamma q=Gamma (Ξ.temperatureScale m hm.1.ne') ν q) ∧
    (∀q∈Icc (0:ℝ) qc, (D).firstVariation q=(m^2)⁻¹*firstVariation (Ξ.temperatureScale m hm.1.ne') ν q) := by
  have hgamma (q : ℝ) (hq : q∈Icc (0:ℝ) qc) :
      (D).Gamma q=temperatureMassGamma Ξ ν m hm.1 q := by
    unfold TruncatedParisiData.Gamma temperatureMassGamma
    apply integral_congr_ae
    exact .of_forall fun sample => by
      dsimp only
      rw [sectionTwoLowerData_spatialField_zero Ξ ν m hm qc hc node hn h0 hlast hCDF hs q hq,
        revised_sectionTwo_state_eq_temperatureMassState Ξ ν m hm qc hc node hn h0 hlast hCDF hs sample q hq]
  refine ⟨fun sample q hq => revised_sectionTwo_common_driver_scaling Ξ ν m hm qc hc node hn h0 hlast hCDF hs sample q hq,
    fun q hq => ?_,fun q hq => ?_⟩
  · rw [hgamma q hq,temperature_mass_Gamma Ξ ν m hm.1 ⟨hq.1,hq.2.trans hc.2⟩,
      temperatureCovarianceFamily_covariance Ξ m hm.1.ne']
  · have he : (D).firstVariation q=(1/2:ℝ)*∫s in (0:ℝ)..q,
        Ξ.second s*(temperatureMassGamma Ξ ν m hm.1 s-s) := by
      unfold TruncatedParisiData.firstVariation
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs'
      dsimp only
      rw [uIcc_of_le hq.1] at hs'
      have hsu : s∈Icc (0:ℝ) qc := ⟨hs'.1,hs'.2.trans hq.2⟩
      rw [sectionTwoLowerData_covarianceField_two Ξ ν m hm qc hc node hn h0 hlast s hsu,hgamma s hsu]
    rw [he,temperature_mass_firstVariation Ξ ν m hm.1 ⟨hq.1,hq.2.trans hc.2⟩,
      temperatureCovarianceFamily_covariance Ξ m hm.1.ne']

end LowerData
/-- Literal finite-atomic source scope of A.7. The finite CDF partition is
constructed from the actual measure, and no supplied grid or diffusion law
hypothesis appears in this final statement. -/
theorem revised_temperature_mass_diffusion_finite_atomic
    (Ξ : AdmissibleCovariance) (ν : ParisiMeasure)
    (hν : (ν:Measure Overlap).support.Finite)
    (m : ℝ) (hm : m∈Ioc (0:ℝ) 1) (qc : ℝ) (hc : qc∈Ioc (0:ℝ) 1)
    (hs : ∀s∈FRSB.parisiSupport ν,s<qc) :
    let d := sectionTwoAtomicLowerData Ξ ν hν m hm qc hc (fun s hs' => (hs s hs').le)
    (∀sample q, q∈Icc (0:ℝ) qc → sectionTwoCommonNoiseState d Ξ sample q =
      m⁻¹*optimalState (Ξ.temperatureScale m hm.1.ne') ν sample q) ∧
    (∀q∈Icc (0:ℝ) qc, d.Gamma q=Gamma (Ξ.temperatureScale m hm.1.ne') ν q) ∧
    (∀q∈Icc (0:ℝ) qc, d.firstVariation q=(m^2)⁻¹*firstVariation (Ξ.temperatureScale m hm.1.ne') ν q) := by
  let p := Classical.choice (exists_sectionTwoFinitePartition ν hν qc hc.1
    (fun s hs' => (hs s hs').le))
  exact revised_temperature_mass_diffusion Ξ ν m hm qc hc p.node p.strictMono p.zero p.last
    p.cdf_cell (fun s hs' => (hs s hs').le)

end GeneralDepthPaper
