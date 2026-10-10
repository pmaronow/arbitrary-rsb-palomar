module

public import GeneralDepthPaper.RevisedSectionTwoPhysicalClockInverse
public import FourPapersCommon.MixedClockDynamics
public import StochasticCalculus.WienerIntegral

@[expose] public section

/-! The inverse-clock deterministic kernels that reconstruct a physical
Brownian motion from the actual normalized covariance-clock driver.
All change-of-variable identities include a zero covariance rate at the
origin; no positive lower bound on the volatility is imposed. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus
open scoped Topology NNReal ENNReal InnerProductSpace
namespace GeneralDepthPaper
open FourPapersCommon
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 64

def sectionTwoPhysicalInverseReal (Ξ : AdmissibleCovariance) (v : ℝ) : ℝ :=
  sectionTwoOverlapAtVarianceTime Ξ ⟨projIcc 0 1 (by norm_num) v,
    (projIcc 0 1 (by norm_num) v).property⟩

theorem sectionTwoPhysicalInverseReal_mem (Ξ : AdmissibleCovariance) (v : ℝ) :
    sectionTwoPhysicalInverseReal Ξ v∈Icc (0:ℝ) 1 :=
  (sectionTwoOverlapAtVarianceTime Ξ _).property

theorem sectionTwoPhysicalInverseReal_clock (Ξ : AdmissibleCovariance)
    (q : Overlap) : sectionTwoPhysicalInverseReal Ξ (Ξ.clock q)=(q:ℝ) := by
  have hc := Ξ.clock_mem_unit q.property
  have hp : (⟨projIcc 0 1 (by norm_num) (Ξ.clock q),
      (projIcc 0 1 (by norm_num) (Ξ.clock q)).property⟩:Overlap)=⟨Ξ.clock q,hc⟩ := by
    apply Subtype.ext
    exact congrArg Subtype.val (projIcc_of_mem (by norm_num : (0:ℝ)≤1) hc)
  unfold sectionTwoPhysicalInverseReal
  rw [hp,sectionTwoOverlapAtVarianceTime_unique Ξ ⟨Ξ.clock q,hc⟩ q rfl]

def sectionTwoPhysicalBrownianKernelReal (Ξ : AdmissibleCovariance) (q : Overlap)
    (v : ℝ) : ℝ :=
  if v∈Ioc (0:ℝ) (Ξ.clock q) then
    mixedBeta Ξ.toEvenMixture / Real.sqrt (Ξ.second (sectionTwoPhysicalInverseReal Ξ v))
  else 0

def sectionTwoPhysicalBrownianKernel (Ξ : AdmissibleCovariance) (q : Overlap)
    (v : ℝ≥0) : ℝ := sectionTwoPhysicalBrownianKernelReal Ξ q v

theorem sectionTwoPhysicalBrownianKernelReal_clock (Ξ : AdmissibleCovariance)
    (q s : Overlap) (hs : 0<(s:ℝ)) (hsq : s≤q) :
    sectionTwoPhysicalBrownianKernelReal Ξ q (Ξ.clock s)=
      mixedBeta Ξ.toEvenMixture / Real.sqrt (Ξ.second s) := by
  have ha : 0<Ξ.clock s := by
    rw [←Ξ.clock_zero]
    exact Ξ.clock_strictMonoOn (by norm_num) s.property.1 hs
  have hb : Ξ.clock s≤Ξ.clock q :=
    Ξ.clock_strictMonoOn.monotoneOn s.property.1 q.property.1 (show (s:ℝ)≤q from hsq)
  rw [sectionTwoPhysicalBrownianKernelReal,ite_eq_left ⟨ha,hb⟩,
    sectionTwoPhysicalInverseReal_clock]

theorem sectionTwoPhysicalBrownianKernel_cancellation (Ξ : AdmissibleCovariance)
    (q s : Overlap) (hs : 0<(s:ℝ)) (hsq : s≤q) :
    sectionTwoPhysicalBrownianKernelReal Ξ q (Ξ.clock s)*Real.sqrt (Ξ.second s)=
      mixedBeta Ξ.toEvenMixture := by
  rw [sectionTwoPhysicalBrownianKernelReal_clock Ξ q s hs hsq]
  exact div_mul_cancel₀ _ (Real.sqrt_pos.mpr (Ξ.second_pos hs)).ne'

theorem sectionTwoPhysicalBrownianKernel_sq_change_of_variables
    (Ξ : AdmissibleCovariance) (q : Overlap) (h : ℝ→ℝ) :
    (∫v in (0:ℝ)..Ξ.clock q,
      (sectionTwoPhysicalBrownianKernelReal Ξ q v)^2*h (sectionTwoPhysicalInverseReal Ξ v))=
      ∫s in (0:ℝ)..(q:ℝ),h s := by
  let g : ℝ→ℝ := fun v => (sectionTwoPhysicalBrownianKernelReal Ξ q v)^2*
    h (sectionTwoPhysicalInverseReal Ξ v)
  have he := integral_mixedClock_substitution Ξ.toEvenMixture g q.property
  simp only [AdmissibleCovariance.toEvenMixture_clock,
    AdmissibleCovariance.toEvenMixture_second,AdmissibleCovariance.toEvenMixture_variance] at he
  rw [←he]
  apply intervalIntegral.integral_congr_Ioo_of_le q.property.1
  intro s hs
  have hsu : s∈Icc (0:ℝ) 1 := ⟨hs.1.le,hs.2.le.trans q.property.2⟩
  let so : Overlap := ⟨s,hsu⟩
  have hb : mixedBeta Ξ.toEvenMixture^2=Ξ.variance := by
    rw [mixedBeta_sq,AdmissibleCovariance.toEvenMixture_variance]
  have hsec : 0<Ξ.second s := Ξ.second_pos hs.1
  dsimp only [g]
  rw [show sectionTwoPhysicalBrownianKernelReal Ξ q (Ξ.clock s)=
      mixedBeta Ξ.toEvenMixture / Real.sqrt (Ξ.second s) from
    sectionTwoPhysicalBrownianKernelReal_clock Ξ q so hs.1 (show so≤q from hs.2.le),
    show sectionTwoPhysicalInverseReal Ξ (Ξ.clock s)=s from
      sectionTwoPhysicalInverseReal_clock Ξ so,
    div_pow,Real.sq_sqrt hsec.le,hb]
  field_simp [hsec.ne',Ξ.variance_pos.ne']

theorem sectionTwoPhysicalBrownianKernel_integral_transport
    (Ξ : AdmissibleCovariance) (q : Overlap) (h : ℝ→ℝ) :
    (∫v,(sectionTwoPhysicalBrownianKernel Ξ q v)^2*
      h (sectionTwoPhysicalInverseReal Ξ v) ∂nonnegativeLebesgueMeasure)=
      ∫s in (0:ℝ)..(q:ℝ),h s := by
  let a := sectionTwoBrownianTime Ξ q
  have ha : (a:ℝ)=Ξ.clock q := Real.coe_toNNReal _ (Ξ.clock_mem_unit q.property).1
  let f : ℝ≥0→ℝ := fun v => (sectionTwoPhysicalBrownianKernel Ξ q v)^2*
    h (sectionTwoPhysicalInverseReal Ξ v)
  have hsupp : f=(Ioc 0 a).indicator f := by
    funext v
    by_cases hv : v∈Ioc 0 a
    · simp [hv]
    · have hv' : ¬(v:ℝ)∈Ioc (0:ℝ) (Ξ.clock q) := by
        simpa only [mem_Ioc,←ha,NNReal.coe_pos,NNReal.coe_le_coe] using hv
      rw [Set.indicator_of_notMem hv]
      change (if (v:ℝ)∈Ioc (0:ℝ) (Ξ.clock q) then
        mixedBeta Ξ.toEvenMixture / Real.sqrt (Ξ.second (sectionTwoPhysicalInverseReal Ξ v))
        else 0)^2*h (sectionTwoPhysicalInverseReal Ξ v)=0
      rw [ite_eq_right hv']
      simp
  change (∫v,f v ∂nonnegativeLebesgueMeasure)=_
  rw [hsupp,integral_indicator measurableSet_Ioc]
  rw [integral_nonnegative_Ioc_eq_real_Icc (fun v (_:Unit)=>f v) a ()]
  have he : (∫s in Icc (0:ℝ) (a:ℝ),f s.toNNReal)=
      ∫s in (0:ℝ)..(a:ℝ),(sectionTwoPhysicalBrownianKernelReal Ξ q s)^2*
        h (sectionTwoPhysicalInverseReal Ξ s) := by
    rw [intervalIntegral.integral_of_le a.coe_nonneg,←integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    simp only [f,sectionTwoPhysicalBrownianKernel,Real.coe_toNNReal _ hs.1]
  rw [he,ha]
  exact sectionTwoPhysicalBrownianKernel_sq_change_of_variables Ξ q h

theorem integral_sq_sectionTwoPhysicalBrownianKernel (Ξ : AdmissibleCovariance) (q : Overlap) :
    (∫v,(sectionTwoPhysicalBrownianKernel Ξ q v)^2 ∂nonnegativeLebesgueMeasure)=(q:ℝ) := by
  simpa using sectionTwoPhysicalBrownianKernel_integral_transport Ξ q (fun _=>1)


theorem continuous_sectionTwoPhysicalInverseReal (Ξ : AdmissibleCovariance) :
    Continuous (sectionTwoPhysicalInverseReal Ξ) := by
  exact continuous_subtype_val.comp
    ((continuous_sectionTwoOverlapAtVarianceTime Ξ).comp (continuous_projIcc (h := by norm_num)))

theorem measurable_sectionTwoPhysicalBrownianKernel (Ξ : AdmissibleCovariance)
    (q : Overlap) : Measurable (sectionTwoPhysicalBrownianKernel Ξ q) := by
  have hm : Measurable (sectionTwoPhysicalBrownianKernelReal Ξ q) :=
    Measurable.ite measurableSet_Ioc
      (measurable_const.div ((Ξ.continuous_second.comp
        (continuous_sectionTwoPhysicalInverseReal Ξ)).sqrt.measurable)) measurable_const
  exact hm.comp NNReal.continuous_coe.measurable

theorem sectionTwoPhysicalBrownianKernel_zero (Ξ : AdmissibleCovariance)
    (q : Overlap) (hq : (q:ℝ)=0) : sectionTwoPhysicalBrownianKernel Ξ q=0 := by
  have ha : Ξ.clock q=0 := by rw [hq,Ξ.clock_zero]
  funext v
  simp [sectionTwoPhysicalBrownianKernel,sectionTwoPhysicalBrownianKernelReal,ha]

theorem memLp_sectionTwoPhysicalBrownianKernel (Ξ : AdmissibleCovariance)
    (q : Overlap) : MemLp (sectionTwoPhysicalBrownianKernel Ξ q) 2
      nonnegativeLebesgueMeasure := by
  by_cases hq : (q:ℝ)=0
  · rw [sectionTwoPhysicalBrownianKernel_zero Ξ q hq]
    exact MemLp.zero
  · apply (memLp_two_iff_integrable_sq
      (measurable_sectionTwoPhysicalBrownianKernel Ξ q).aestronglyMeasurable).mpr
    apply Integrable.of_integral_ne_zero
    rw [integral_sq_sectionTwoPhysicalBrownianKernel]
    exact hq

/-- The actual inverse-clock kernel as an element of deterministic `L²`. -/
def sectionTwoPhysicalBrownianKernelLp (Ξ : AdmissibleCovariance) (q : Overlap) :
    Lp ℝ 2 nonnegativeLebesgueMeasure :=
  (memLp_sectionTwoPhysicalBrownianKernel Ξ q).toLp (sectionTwoPhysicalBrownianKernel Ξ q)

theorem coeFn_sectionTwoPhysicalBrownianKernelLp (Ξ : AdmissibleCovariance) (q : Overlap) :
    (sectionTwoPhysicalBrownianKernelLp Ξ q : ℝ≥0→ℝ)=ᵐ[nonnegativeLebesgueMeasure]
      sectionTwoPhysicalBrownianKernel Ξ q := MemLp.coeFn_toLp _

theorem norm_sq_sectionTwoPhysicalBrownianKernelLp (Ξ : AdmissibleCovariance) (q : Overlap) :
    ‖sectionTwoPhysicalBrownianKernelLp Ξ q‖^2=(q:ℝ) := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  calc
    _ = ∫v,(sectionTwoPhysicalBrownianKernel Ξ q v)^2 ∂nonnegativeLebesgueMeasure := by
      apply integral_congr_ae
      filter_upwards [coeFn_sectionTwoPhysicalBrownianKernelLp Ξ q] with v hv
      simp [hv,pow_two]
    _ = _ := integral_sq_sectionTwoPhysicalBrownianKernel Ξ q


theorem sectionTwoClock_min (Ξ : AdmissibleCovariance) (s t : Overlap) :
    Ξ.clock (min (s:ℝ) (t:ℝ))=min (Ξ.clock s) (Ξ.clock t) := by
  rcases le_total s t with h|h
  · rw [min_eq_left (show (s:ℝ)≤(t:ℝ) from h),min_eq_left
      (Ξ.clock_strictMonoOn.monotoneOn s.property.1 t.property.1 h)]
  · rw [min_eq_right (show (t:ℝ)≤(s:ℝ) from h),min_eq_right
      (Ξ.clock_strictMonoOn.monotoneOn t.property.1 s.property.1 h)]

theorem sectionTwoPhysicalBrownianKernel_mul (Ξ : AdmissibleCovariance)
    (s t : Overlap) (v : ℝ≥0) :
    sectionTwoPhysicalBrownianKernel Ξ s v*sectionTwoPhysicalBrownianKernel Ξ t v=
      (sectionTwoPhysicalBrownianKernel Ξ (min s t) v)^2 := by
  rcases le_total s t with h|h
  · rw [min_eq_left h]
    by_cases hs : (v:ℝ)∈Ioc (0:ℝ) (Ξ.clock s)
    · have ht : (v:ℝ)∈Ioc (0:ℝ) (Ξ.clock t) := ⟨hs.1,hs.2.trans
        (Ξ.clock_strictMonoOn.monotoneOn s.property.1 t.property.1 h)⟩
      simp [sectionTwoPhysicalBrownianKernel,sectionTwoPhysicalBrownianKernelReal,hs,ht,pow_two]
    · simp [sectionTwoPhysicalBrownianKernel,sectionTwoPhysicalBrownianKernelReal,hs]
  · rw [min_eq_right h]
    by_cases ht : (v:ℝ)∈Ioc (0:ℝ) (Ξ.clock t)
    · have hs : (v:ℝ)∈Ioc (0:ℝ) (Ξ.clock s) := ⟨ht.1,ht.2.trans
        (Ξ.clock_strictMonoOn.monotoneOn t.property.1 s.property.1 h)⟩
      simp [sectionTwoPhysicalBrownianKernel,sectionTwoPhysicalBrownianKernelReal,hs,ht,pow_two]
    · simp [sectionTwoPhysicalBrownianKernel,sectionTwoPhysicalBrownianKernelReal,ht]

theorem inner_sectionTwoPhysicalBrownianKernelLp (Ξ : AdmissibleCovariance)
    (s t : Overlap) :
    ⟪sectionTwoPhysicalBrownianKernelLp Ξ s,sectionTwoPhysicalBrownianKernelLp Ξ t⟫_ℝ=
      min (s:ℝ) (t:ℝ) := by
  rw [L2.inner_def]
  calc
    _ = ∫v,(sectionTwoPhysicalBrownianKernel Ξ (min s t) v)^2
        ∂nonnegativeLebesgueMeasure := by
      apply integral_congr_ae
      filter_upwards [coeFn_sectionTwoPhysicalBrownianKernelLp Ξ s,
        coeFn_sectionTwoPhysicalBrownianKernelLp Ξ t] with v hs ht
      rw [Real.inner_apply,hs,ht,sectionTwoPhysicalBrownianKernel_mul]
    _ = _ := by simpa using integral_sq_sectionTwoPhysicalBrownianKernel Ξ (min s t)

theorem sectionTwoPhysicalBrownianKernel_support_unit (Ξ : AdmissibleCovariance)
    (q : Overlap) (v : ℝ≥0) (hv : 1<(v:ℝ)) : sectionTwoPhysicalBrownianKernel Ξ q v=0 := by
  have hn : ¬(v:ℝ)∈Ioc (0:ℝ) (Ξ.clock q) := by
    intro h
    exact (not_le_of_gt hv) (h.2.trans (Ξ.clock_mem_unit q.property).2)
  exact ite_eq_right hn

/-- Physical kernels use only the original driver's normalized times at most one. -/
theorem inner_sectionTwoPhysicalBrownianKernelLp_tail (Ξ : AdmissibleCovariance)
    (q : Overlap) (t : ℝ≥0) (ht : 1≤t) :
    ⟪sectionTwoPhysicalBrownianKernelLp Ξ q,intervalIndicator t-intervalIndicator 1⟫_ℝ=0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [coeFn_sectionTwoPhysicalBrownianKernelLp Ξ q,
    Lp.coeFn_sub (intervalIndicator t) (intervalIndicator 1),
    (show (intervalIndicator t : ℝ≥0→ℝ)=ᵐ[nonnegativeLebesgueMeasure]
      (Ioc 0 t).indicator (fun _=>1) from indicatorConstLp_coeFn),
    (show (intervalIndicator 1 : ℝ≥0→ℝ)=ᵐ[nonnegativeLebesgueMeasure]
      (Ioc 0 (1:ℝ≥0)).indicator (fun _=>1) from indicatorConstLp_coeFn)]
      with v hK hsub htI h1I
  rw [Real.inner_apply,hK,hsub]
  simp only [Pi.sub_apply,Pi.zero_apply]
  rw [htI,h1I]
  by_cases hv : v≤1
  · by_cases hv0 : 0<v
    · simp [Set.indicator_of_mem (show v∈Ioc 0 t from ⟨hv0,hv.trans ht⟩),
        Set.indicator_of_mem (show v∈Ioc 0 (1:ℝ≥0) from ⟨hv0,hv⟩)]
    · simp [Set.indicator_of_notMem (show v∉Ioc 0 t from fun h=>hv0 h.1),
        Set.indicator_of_notMem (show v∉Ioc 0 (1:ℝ≥0) from fun h=>hv0 h.1)]
  · rw [sectionTwoPhysicalBrownianKernel_support_unit Ξ q v (by exact_mod_cast lt_of_not_ge hv)]
    simp


theorem sectionTwoPhysicalInverseReal_clock_value (Ξ : AdmissibleCovariance)
    (v : ℝ) (hv : v∈Icc (0:ℝ) 1) : Ξ.clock (sectionTwoPhysicalInverseReal Ξ v)=v := by
  unfold sectionTwoPhysicalInverseReal
  rw [sectionTwoOverlapAtVarianceTime_clock]
  exact congrArg Subtype.val (projIcc_of_mem (by norm_num : (0:ℝ)≤1) hv)

theorem sectionTwoPhysicalInverseReal_pos (Ξ : AdmissibleCovariance)
    (v : ℝ) (hv : v∈Ioc (0:ℝ) 1) : 0<sectionTwoPhysicalInverseReal Ξ v := by
  by_contra hn
  have h0 : sectionTwoPhysicalInverseReal Ξ v=0 :=
    le_antisymm (le_of_not_gt hn) (sectionTwoPhysicalInverseReal_mem Ξ v).1
  have hc := sectionTwoPhysicalInverseReal_clock_value Ξ v ⟨hv.1.le,hv.2⟩
  rw [h0,Ξ.clock_zero] at hc
  exact hv.1.ne' hc.symm

/-- Exact pointwise cancellation of the inverse-clock kernel with physical
volatility. The zero-rate origin is excluded only by the indicator itself. -/
theorem sectionTwoPhysicalBrownianKernel_volatility (Ξ : AdmissibleCovariance)
    (q : Overlap) (v : ℝ≥0) :
    sectionTwoPhysicalBrownianKernel Ξ q v *
        Real.sqrt (Ξ.second (sectionTwoPhysicalInverseReal Ξ v))=
      mixedBeta Ξ.toEvenMixture *
        (Ioc 0 (sectionTwoBrownianTime Ξ q)).indicator (fun _=>1) v := by
  have ha : ((sectionTwoBrownianTime Ξ q):ℝ)=Ξ.clock q :=
    Real.coe_toNNReal _ (Ξ.clock_mem_unit q.property).1
  by_cases hv : v∈Ioc 0 (sectionTwoBrownianTime Ξ q)
  · have hv' : (v:ℝ)∈Ioc (0:ℝ) (Ξ.clock q) := by
      simpa only [mem_Ioc,←ha,NNReal.coe_pos,NNReal.coe_le_coe] using hv
    have hp := sectionTwoPhysicalInverseReal_pos Ξ v
      ⟨hv'.1,hv'.2.trans (Ξ.clock_mem_unit q.property).2⟩
    rw [sectionTwoPhysicalBrownianKernel,sectionTwoPhysicalBrownianKernelReal,
      ite_eq_left hv',Set.indicator_of_mem hv]
    simpa using div_mul_cancel₀ (mixedBeta Ξ.toEvenMixture)
      (Real.sqrt_pos.mpr (Ξ.second_pos hp)).ne'
  · have hv' : ¬(v:ℝ)∈Ioc (0:ℝ) (Ξ.clock q) := by
      simpa only [mem_Ioc,←ha,NNReal.coe_pos,NNReal.coe_le_coe] using hv
    rw [sectionTwoPhysicalBrownianKernel,sectionTwoPhysicalBrownianKernelReal,
      ite_eq_right hv',Set.indicator_of_notMem hv]
    simp

theorem sectionTwoPhysicalBrownianKernel_product_integral_transport
    (Ξ : AdmissibleCovariance) (s t : Overlap) (h : ℝ→ℝ) :
    (∫v,sectionTwoPhysicalBrownianKernel Ξ s v*sectionTwoPhysicalBrownianKernel Ξ t v*
      h (sectionTwoPhysicalInverseReal Ξ v) ∂nonnegativeLebesgueMeasure)=
      ∫u in (0:ℝ)..min (s:ℝ) (t:ℝ),h u := by
  simp_rw [sectionTwoPhysicalBrownianKernel_mul]
  exact sectionTwoPhysicalBrownianKernel_integral_transport Ξ (min s t) h

/-- Cross pairing with the original covariance-clock driver. This identifies
its deterministic Wiener integral after reconstructing the physical Brownian
motion, rather than merely matching its covariance. -/
theorem inner_sectionTwoPhysicalBrownianKernelLp_original_driver
    (Ξ : AdmissibleCovariance) (s q : Overlap) :
    ⟪sectionTwoPhysicalBrownianKernelLp Ξ s,
      mixedBeta Ξ.toEvenMixture • intervalIndicator (sectionTwoBrownianTime Ξ q)⟫_ℝ=
      ∫u in (0:ℝ)..min (s:ℝ) (q:ℝ),Real.sqrt (Ξ.second u) := by
  rw [L2.inner_def]
  calc
    _ = ∫v,sectionTwoPhysicalBrownianKernel Ξ s v*sectionTwoPhysicalBrownianKernel Ξ q v*
          Real.sqrt (Ξ.second (sectionTwoPhysicalInverseReal Ξ v))
          ∂nonnegativeLebesgueMeasure := by
      apply integral_congr_ae
      filter_upwards [coeFn_sectionTwoPhysicalBrownianKernelLp Ξ s,
        Lp.coeFn_smul (mixedBeta Ξ.toEvenMixture) (intervalIndicator (sectionTwoBrownianTime Ξ q)),
        (show (intervalIndicator (sectionTwoBrownianTime Ξ q) : ℝ≥0→ℝ)=ᵐ[nonnegativeLebesgueMeasure]
          (Ioc 0 (sectionTwoBrownianTime Ξ q)).indicator (fun _=>1)
          from indicatorConstLp_coeFn)] with v hK hsm hI
      rw [Real.inner_apply,hK,hsm]
      simp only [Pi.smul_apply,smul_eq_mul]
      rw [hI]
      rw [←sectionTwoPhysicalBrownianKernel_volatility Ξ q v]
      ring
    _ = _ := sectionTwoPhysicalBrownianKernel_product_integral_transport Ξ s q
      (fun u=>Real.sqrt (Ξ.second u))

end GeneralDepthPaper
