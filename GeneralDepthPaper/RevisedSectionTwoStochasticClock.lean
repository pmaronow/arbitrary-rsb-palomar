module

public import GeneralDepthPaper.RevisedSectionTwoStochasticGluing
public import FourPapersCommon.TimeChangedBrownian

@[expose] public section

/-! The actual finite-support Hessian stochastic representation in the
normalized variance clock. The driving process in physical coordinates is
`J(q)=sqrt(Ξ'(1))*B(Ξ'(q)/Ξ'(1))`. This module proves its concrete Hessian
left-sum representation. The subsequent `RevisedSectionTwoPhysicalBrownian`
and `RevisedSectionTwoPhysicalBrownianGluing` modules reconstruct the
physical-time standard Brownian driver and prove the literal
`sqrt(Ξ''(q)) dB(q)` representation. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus Paper
open scoped Topology NNReal ENNReal
namespace GeneralDepthPaper
open FourPapersCommon SpinGlass.Targets
set_option maxHeartbeats 1000000

theorem exists_sectionTwoOverlapAtVarianceTime (Ξ : AdmissibleCovariance) (v : Overlap) :
    ∃ q : Overlap, Ξ.clock q=(v:ℝ) := by
  obtain ⟨q,hq,he⟩:=intermediate_value_Icc (show (0:ℝ) ≤ 1 by norm_num)
    Ξ.continuous_clock.continuousOn (by simpa only [Ξ.clock_zero,Ξ.clock_one] using v.property)
  exact ⟨⟨q,hq⟩,he⟩

/-- The uniquely determined physical overlap at a normalized variance time. -/
def sectionTwoOverlapAtVarianceTime (Ξ : AdmissibleCovariance) (v : Overlap) : Overlap :=
  Classical.choose (exists_sectionTwoOverlapAtVarianceTime Ξ v)

theorem sectionTwoOverlapAtVarianceTime_clock (Ξ : AdmissibleCovariance) (v : Overlap) :
    Ξ.clock (sectionTwoOverlapAtVarianceTime Ξ v)=(v:ℝ) :=
  Classical.choose_spec (exists_sectionTwoOverlapAtVarianceTime Ξ v)

theorem sectionTwoOverlapAtVarianceTime_unique (Ξ : AdmissibleCovariance) (v q : Overlap)
    (hq : Ξ.clock q=(v:ℝ)) : sectionTwoOverlapAtVarianceTime Ξ v=q := by
  apply Subtype.ext
  exact Ξ.clock_strictMonoOn.injOn
    (sectionTwoOverlapAtVarianceTime Ξ v).property.1 q.property.1
    ((sectionTwoOverlapAtVarianceTime_clock Ξ v).trans hq.symm)

/-- The actual Gaussian martingale driver expressed in physical overlap
coordinates; its deterministic variance is `Ξ'(q)`. -/
def sectionTwoClockDriver (Ξ : AdmissibleCovariance) (q : Overlap)
    (sample : Paper.BrownianSample) : ℝ :=
  mixedBeta Ξ.toEvenMixture*Paper.canonicalBrownian (sectionTwoBrownianTime Ξ q) sample

theorem sectionTwoClockDriver_variance (Ξ : AdmissibleCovariance) (q : Overlap) :
    (mixedBeta Ξ.toEvenMixture)^2*(sectionTwoBrownianTime Ξ q:ℝ)=Ξ.first q := by
  rw [mixedBeta_sq,sectionTwoBrownianTime,
    Real.coe_toNNReal _ (Ξ.clock_mem_unit q.property).1,
    AdmissibleCovariance.toEvenMixture_variance,AdmissibleCovariance.clock]
  exact mul_div_cancel₀ _ Ξ.variance_pos.ne'

def sectionTwoExtendedBrownianClock (Ξ : AdmissibleCovariance) (t : ℝ≥0) : ℝ≥0 :=
  (Ξ.clock t).toNNReal

def sectionTwoExtendedClockDriver (Ξ : AdmissibleCovariance) (t : ℝ≥0)
    (sample : Paper.BrownianSample) : ℝ :=
  mixedBeta Ξ.toEvenMixture*Paper.canonicalBrownian (sectionTwoExtendedBrownianClock Ξ t) sample

/-- The actual clock driver has bracket `Ξ'`, with convergence of concrete
squared-increment sums. This is the stochastic basis of the clock form. -/
theorem sectionTwoExtendedClockDriver_quadraticVariation (Ξ : AdmissibleCovariance) :
    HasQuadraticVariationBeforeStopProcessInProbability (sectionTwoExtendedClockDriver Ξ)
      (fun t _ => Ξ.first t) Paper.canonicalBrownianMeasure := by
  let A:=sectionTwoExtendedBrownianClock Ξ
  have hA0 : A 0=0 := by simp [A,sectionTwoExtendedBrownianClock]
  have hAc : Continuous A := continuous_real_toNNReal.comp
    (Ξ.continuous_clock.comp NNReal.continuous_coe)
  have hAm : Monotone A := fun s t hst => Real.toNNReal_mono
    (Ξ.clock_strictMonoOn.monotoneOn s.property t.property (NNReal.coe_le_coe.mpr hst))
  have hqv:=(quadraticVariationBeforeStop_timeChangedBrownian A hA0 hAc hAm).const_mul
    (mixedBeta Ξ.toEvenMixture)
  have hval (t:ℝ≥0) : (mixedBeta Ξ.toEvenMixture)^2*(A t:ℝ)=Ξ.first t := by
    rw [mixedBeta_sq,AdmissibleCovariance.toEvenMixture_variance]
    change Ξ.variance*((Ξ.clock t).toNNReal:ℝ)=Ξ.first t
    have hclock : 0 ≤ Ξ.clock t := div_nonneg (Ξ.first_nonneg t.property) Ξ.variance_pos.le
    have he : ((Ξ.clock t).toNNReal:ℝ)=Ξ.clock t := Real.coe_toNNReal _ hclock
    rw [he,AdmissibleCovariance.clock]
    exact mul_div_cancel₀ _ Ξ.variance_pos.ne'
  change HasQuadraticVariationBeforeStopProcessInProbability
    (fun t sample => mixedBeta Ξ.toEvenMixture*timeChangedBrownian A t sample)
    (fun t _ => Ξ.first t) Paper.canonicalBrownianMeasure
  simpa only [hval] using hqv

theorem sectionTwoClockDriver_eq_normalized (Ξ : AdmissibleCovariance) (v : Overlap)
    (sample : Paper.BrownianSample) :
    sectionTwoClockDriver Ξ (sectionTwoOverlapAtVarianceTime Ξ v) sample=
      mixedBeta Ξ.toEvenMixture*Paper.canonicalBrownian (v:ℝ).toNNReal sample := by
  rw [sectionTwoClockDriver,sectionTwoBrownianTime,sectionTwoOverlapAtVarianceTime_clock]

/-- The integrand is the actual spatial Hessian at the actual selected
diffusion, expressed at normalized variance time. -/
def sectionTwoVarianceHessian (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (v : ℝ≥0) (sample : Paper.BrownianSample) : ℝ :=
  Paper.parisiHessian (mixedBeta Ξ.toEvenMixture) (mixedMeasure Ξ.toEvenMixture μ)
    (v,Paper.selectedParisiItoState (mixedBeta Ξ.toEvenMixture) 0
      (mixedBeta_ne_zero Ξ.toEvenMixture) (mixedMeasure Ξ.toEvenMixture μ) v sample)

theorem sectionTwoVarianceHessian_eq_actual (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (q : Overlap) (sample : Paper.BrownianSample) :
    sectionTwoVarianceHessian Ξ μ (sectionTwoBrownianTime Ξ q) sample=
      hessian Ξ μ q (optimalState Ξ μ sample q) := by
  have hq:=Ξ.clock_mem_unit q.property
  have hnn : (sectionTwoBrownianTime Ξ q:ℝ)=Ξ.clock q := Real.coe_toNNReal _ hq.1
  simp only [sectionTwoVarianceHessian,hessian,optimalState,mixedHessian,mixedState,
    AdmissibleCovariance.toEvenMixture_clock]
  rw [Paper.selectedParisiItoState_eq _ _ _ _ (by rw [hnn];exact hq.2) sample,hnn]

theorem sectionTwoVarianceHessian_eq_physical (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (v : Overlap) (sample : Paper.BrownianSample) :
    sectionTwoVarianceHessian Ξ μ (v:ℝ).toNNReal sample=
      hessian Ξ μ (sectionTwoOverlapAtVarianceTime Ξ v)
        (optimalState Ξ μ sample (sectionTwoOverlapAtVarianceTime Ξ v)) := by
  convert sectionTwoVarianceHessian_eq_actual Ξ μ (sectionTwoOverlapAtVarianceTime Ξ v) sample using 1
  rw [sectionTwoBrownianTime,sectionTwoOverlapAtVarianceTime_clock]

/-- Each normalized-time stochastic left summand is exactly its actual
Hessian/physical-clock-driver summand, on the same sample path. -/
theorem sectionTwoVarianceHessian_summand_eq_physical (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) (u v : Overlap) (sample : Paper.BrownianSample) :
    sectionTwoVarianceHessian Ξ μ (u:ℝ).toNNReal sample*
      (mixedBeta Ξ.toEvenMixture*(Paper.canonicalBrownian (v:ℝ).toNNReal sample-
        Paper.canonicalBrownian (u:ℝ).toNNReal sample))=
    hessian Ξ μ (sectionTwoOverlapAtVarianceTime Ξ u)
      (optimalState Ξ μ sample (sectionTwoOverlapAtVarianceTime Ξ u))*
      (sectionTwoClockDriver Ξ (sectionTwoOverlapAtVarianceTime Ξ v) sample-
        sectionTwoClockDriver Ξ (sectionTwoOverlapAtVarianceTime Ξ u) sample) := by
  rw [sectionTwoVarianceHessian_eq_physical,sectionTwoClockDriver_eq_normalized,
    sectionTwoClockDriver_eq_normalized]
  ring

/-- The integrand in the finite-cell sums is literally the actual Hessian
along the selected state of the actual clock-pushed probability law. -/
theorem sectionTwoFiniteCell_integrand_eq_actual (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) (hμ : (μ:Measure Overlap).support.Finite)
    (l v : ℝ≥0) (sample : Paper.BrownianSample) :
    Paper.parisiHessian (mixedBeta Ξ.toEvenMixture)
      (Paper.parisiSchemeMeasure (sectionTwoMixedFiniteScheme Ξ μ hμ))
      ((l:ℝ)+v,Paper.selectedParisiItoState (mixedBeta Ξ.toEvenMixture) 0
        (mixedBeta_ne_zero Ξ.toEvenMixture)
        (Paper.parisiSchemeMeasure (sectionTwoMixedFiniteScheme Ξ μ hμ)) (l+v) sample)=
    sectionTwoVarianceHessian Ξ μ (l+v) sample := by
  rw [sectionTwoMixedFiniteScheme_represents]
  rfl

theorem sectionTwoFiniteCell_driver_increment (Ξ : AdmissibleCovariance)
    (l u v : ℝ≥0) (sample : Paper.BrownianSample) :
    Paper.canonicalDiracShiftMartingale (mixedBeta Ξ.toEvenMixture) l v sample-
      Paper.canonicalDiracShiftMartingale (mixedBeta Ξ.toEvenMixture) l u sample=
    mixedBeta Ξ.toEvenMixture*(Paper.canonicalBrownian (l+v) sample-
      Paper.canonicalBrownian (l+u) sample) := by
  unfold Paper.canonicalDiracShiftMartingale
  ring

/-- Concrete actual-Hessian left sums, joined across the finite atomic
CDF cells after cropping their endpoints. -/
def sectionTwoHessianClockLeftSums (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (hμ : (μ:Measure Overlap).support.Finite) (q : Overlap) (n j : ℕ) : Paper.BrownianSample → ℝ :=
  finiteSchemeHessianLeftSums (mixedBeta Ξ.toEvenMixture) 0 (mixedBeta_ne_zero Ξ.toEvenMixture)
    (sectionTwoMixedFiniteScheme Ξ μ hμ) (sectionTwoBrownianTime Ξ q) n j

def sectionTwoHessianClockInnerLimit (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (hμ : (μ:Measure Overlap).support.Finite) (q : Overlap) (n : ℕ) : Paper.BrownianSample → ℝ :=
  stochasticProbabilityLimit Paper.canonicalBrownianMeasure
    (fun j => sectionTwoHessianClockLeftSums Ξ μ hμ q n j)

/-- The actual finite-support Hessian integral against the variance-clock
driver, constructed only from its stochastic left sums and their limits. -/
def sectionTwoHessianClockIntegral (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (hμ : (μ:Measure Overlap).support.Finite) (q : Overlap) : Paper.BrownianSample → ℝ :=
  stochasticProbabilityLimit Paper.canonicalBrownianMeasure
    (fun n => sectionTwoHessianClockInnerLimit Ξ μ hμ q n)

theorem sectionTwoHessianClockLeftSums_tendsto (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (hμ : (μ:Measure Overlap).support.Finite) (q : Overlap) (n : ℕ) :
    TendstoInMeasure Paper.canonicalBrownianMeasure
      (fun j => sectionTwoHessianClockLeftSums Ξ μ hμ q n j) atTop
      (sectionTwoHessianClockInnerLimit Ξ μ hμ q n) := by
  apply stochasticProbabilityLimit_tendsto
  exact ⟨_,finiteSchemeHessianLeftSums_tendsto _ _ _ _ _
    (by rw [sectionTwoBrownianTime,Real.coe_toNNReal _ (Ξ.clock_mem_unit q.property).1]
        exact (Ξ.clock_mem_unit q.property).2) n⟩

theorem sectionTwoHessianClockInnerLimit_tendsto (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (hμ : (μ:Measure Overlap).support.Finite) (q : Overlap) :
    TendstoInMeasure Paper.canonicalBrownianMeasure
      (fun n => sectionTwoHessianClockInnerLimit Ξ μ hμ q n) atTop
      (sectionTwoGradientProcess Ξ μ q) := by
  have hconv:=finiteSchemeHessianInnerLimit_tendsto (mixedBeta Ξ.toEvenMixture) 0
    (mixedBeta_ne_zero Ξ.toEvenMixture) (sectionTwoMixedFiniteScheme Ξ μ hμ)
    (sectionTwoBrownianTime Ξ q)
    (by rw [sectionTwoBrownianTime,Real.coe_toNNReal _ (Ξ.clock_mem_unit q.property).1]
        exact (Ξ.clock_mem_unit q.property).2)
  apply TendstoInMeasure.congr_right _ hconv
  exact .of_forall fun sample => by
    rw [sectionTwoMixedFiniteScheme_represents]
    dsimp only
    have heq:=congrFun (sectionTwoGradientProcess_eq_selected Ξ μ q) sample
    have he0:=congrFun (sectionTwoGradientProcess_eq_selected Ξ μ ⟨0,by norm_num⟩) sample
    simp only [sectionTwoBrownianTime,Ξ.clock_zero,Real.toNNReal_zero] at he0
    rw [←heq,←he0,sectionTwoGradientProcess_zero,sub_zero]

theorem sectionTwoHessianClockIntegral_eq (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (hμ : (μ:Measure Overlap).support.Finite) (q : Overlap) :
    sectionTwoHessianClockIntegral Ξ μ hμ q =ᵐ[Paper.canonicalBrownianMeasure]
      sectionTwoGradientProcess Ξ μ q :=
  stochasticProbabilityLimit_eq (sectionTwoHessianClockInnerLimit_tendsto Ξ μ hμ q)

theorem sectionTwoHessianClockIntegral_aestronglyMeasurable (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) (hμ : (μ:Measure Overlap).support.Finite) (q : Overlap) :
    AEStronglyMeasurable (sectionTwoHessianClockIntegral Ξ μ hμ q) Paper.canonicalBrownianMeasure :=
  (measurable_sectionTwoGradientProcess_fixed Ξ μ q).aestronglyMeasurable.congr
    (sectionTwoHessianClockIntegral_eq Ξ μ hμ q).symm

/-- The actual continuous gradient is a continuous modification of the
constructed probability-limit integral. No uncountable intersection of
pointwise almost-sure events is asserted. -/
theorem sectionTwoHessianClockIntegral_continuous_modification (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) (hμ : (μ:Measure Overlap).support.Finite) :
    (∀ sample, Continuous (fun q => sectionTwoGradientProcess Ξ μ q sample)) ∧
    (∀ q, sectionTwoHessianClockIntegral Ξ μ hμ q =ᵐ[Paper.canonicalBrownianMeasure]
      sectionTwoGradientProcess Ξ μ q) :=
  ⟨continuous_sectionTwoGradientProcess_path Ξ μ,sectionTwoHessianClockIntegral_eq Ξ μ hμ⟩

/-- The finite-support clock form of the stochastic clause in Lemma 2.2.
Both convergence steps and identification of the actual process are proved.
No stochastic-integral representation is included among the hypotheses. -/
theorem revised_lemma_2_2_finite_atomic_clock_stochastic (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) (hμ : (μ:Measure Overlap).support.Finite) :
    (∀ q n, TendstoInMeasure Paper.canonicalBrownianMeasure
      (fun j => sectionTwoHessianClockLeftSums Ξ μ hμ q n j) atTop
      (sectionTwoHessianClockInnerLimit Ξ μ hμ q n)) ∧
    (∀ q, TendstoInMeasure Paper.canonicalBrownianMeasure
      (fun n => sectionTwoHessianClockInnerLimit Ξ μ hμ q n) atTop
      (sectionTwoGradientProcess Ξ μ q)) ∧
    (∀ q, sectionTwoHessianClockIntegral Ξ μ hμ q =ᵐ[Paper.canonicalBrownianMeasure]
      sectionTwoGradientProcess Ξ μ q) :=
  ⟨sectionTwoHessianClockLeftSums_tendsto Ξ μ hμ,
    sectionTwoHessianClockInnerLimit_tendsto Ξ μ hμ,
    sectionTwoHessianClockIntegral_eq Ξ μ hμ⟩

end GeneralDepthPaper
