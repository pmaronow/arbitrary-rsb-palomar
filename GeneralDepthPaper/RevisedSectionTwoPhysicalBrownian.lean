module

public import GeneralDepthPaper.RevisedSectionTwoPhysicalClockTransport
public import FourPapersCommon.WienerKernelTransport
public import FourPapersCommon.WienerPastIndependence
public import FourPapersCommon.WienerPastMeasurability

@[expose] public section

/-! A physical-time standard Brownian motion reconstructed on the original
canonical probability space. Its deterministic square-root-volatility Wiener
integral is proved equal to the original covariance-clock driver. The kernel
construction includes quadratic covariances and zero volatility at the origin. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus Paper
open scoped Topology NNReal ENNReal InnerProductSpace
namespace GeneralDepthPaper
open FourPapersCommon
set_option maxHeartbeats 1500000

/-- Physical inverse-clock kernels, extended after physical time one by
untouched original Brownian increments. -/
def sectionTwoPhysicalBrownianKernelFamily (Ξ : AdmissibleCovariance)
    (t : ℝ≥0) : Lp ℝ 2 nonnegativeLebesgueMeasure :=
  unitWienerKernelExtension (sectionTwoPhysicalBrownianKernelLp Ξ) t

theorem sectionTwoPhysicalBrownianKernelFamily_gram (Ξ : AdmissibleCovariance)
    (s t : ℝ≥0) :
    ⟪sectionTwoPhysicalBrownianKernelFamily Ξ s,
      sectionTwoPhysicalBrownianKernelFamily Ξ t⟫_ℝ = (min s t : ℝ) :=
  inner_unitWienerKernelExtension _ (inner_sectionTwoPhysicalBrownianKernelLp Ξ)
    (inner_sectionTwoPhysicalBrownianKernelLp_tail Ξ) s t

theorem sectionTwoPhysicalBrownianKernelFamily_unit (Ξ : AdmissibleCovariance)
    (q : Overlap) :
    sectionTwoPhysicalBrownianKernelFamily Ξ q.val.toNNReal =
      sectionTwoPhysicalBrownianKernelLp Ξ q :=
  unitWienerKernelExtension_unit _ q

/-- The reconstructed physical standard Brownian motion is a continuous
modification of the deterministic Wiener-kernel process, on the same sample. -/
def sectionTwoPhysicalBrownian (Ξ : AdmissibleCovariance) :
    ℝ≥0 → BrownianSample → ℝ :=
  wienerBrownianDriver isBrownianReal_canonicalBrownian.toIsPreBrownianReal
    (sectionTwoPhysicalBrownianKernelFamily Ξ) (sectionTwoPhysicalBrownianKernelFamily_gram Ξ)

theorem isBrownianReal_sectionTwoPhysicalBrownian (Ξ : AdmissibleCovariance) :
    IsBrownianReal (sectionTwoPhysicalBrownian Ξ) canonicalBrownianMeasure :=
  isBrownianReal_wienerBrownianDriver _ _ _

theorem sectionTwoPhysicalBrownian_zero (Ξ : AdmissibleCovariance) (sample : BrownianSample) :
    sectionTwoPhysicalBrownian Ξ 0 sample = 0 := wienerBrownianDriver_zero _ _ _ _

theorem measurable_sectionTwoPhysicalBrownian (Ξ : AdmissibleCovariance) (t : ℝ≥0) :
    Measurable (sectionTwoPhysicalBrownian Ξ t) := measurable_wienerBrownianDriver _ _ _ _

theorem continuous_sectionTwoPhysicalBrownian (Ξ : AdmissibleCovariance)
    (sample : BrownianSample) : Continuous (fun t => sectionTwoPhysicalBrownian Ξ t sample) :=
  continuous_wienerBrownianDriver _ _ _ _

theorem sectionTwoPhysicalBrownian_ae_eq_wiener (Ξ : AdmissibleCovariance) (q : Overlap) :
    sectionTwoPhysicalBrownian Ξ q.val.toNNReal =ᵐ[canonicalBrownianMeasure]
      wienerIntegral isBrownianReal_canonicalBrownian.toIsPreBrownianReal
        (sectionTwoPhysicalBrownianKernelLp Ξ q) := by
  simpa only [sectionTwoPhysicalBrownian, sectionTwoPhysicalBrownianKernelFamily_unit] using
    wienerBrownianDriver_ae_eq isBrownianReal_canonicalBrownian.toIsPreBrownianReal
      (sectionTwoPhysicalBrownianKernelFamily Ξ) (sectionTwoPhysicalBrownianKernelFamily_gram Ξ)
      q.val.toNNReal

/-- The literal physical square-root-volatility integrand, cut off at the
requested physical overlap. -/
def sectionTwoPhysicalVolatilityKernel (Ξ : AdmissibleCovariance) (q : Overlap)
    (t : ℝ≥0) : ℝ := (Ioc 0 q.val.toNNReal).indicator (physicalVolatility Ξ) t

theorem memLp_sectionTwoPhysicalVolatilityKernel (Ξ : AdmissibleCovariance) (q : Overlap) :
    MemLp (sectionTwoPhysicalVolatilityKernel Ξ q) 2 nonnegativeLebesgueMeasure := by
  have : IsFiniteMeasure (nonnegativeLebesgueMeasure.restrict (Ioc 0 q.val.toNNReal)) :=
    isFiniteMeasure_restrict.mpr (nonnegativeLebesgueMeasure_Ioc_ne_top _ _)
  apply (memLp_indicator_iff_restrict measurableSet_Ioc).mpr
  apply MemLp.of_bound (continuous_physicalVolatility Ξ).aestronglyMeasurable
    (Real.sqrt (Ξ.second 1))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (physicalVolatility_nonneg Ξ t)]
  apply physicalVolatility_le_one Ξ
  have hq : q.val.toNNReal ≤ 1 := by
    exact_mod_cast (Real.coe_toNNReal _ q.property.1).trans_le q.property.2
  exact ht.2.trans hq

def sectionTwoPhysicalVolatilityKernelLp (Ξ : AdmissibleCovariance) (q : Overlap) :
    Lp ℝ 2 nonnegativeLebesgueMeasure :=
  (memLp_sectionTwoPhysicalVolatilityKernel Ξ q).toLp (sectionTwoPhysicalVolatilityKernel Ξ q)

theorem coeFn_sectionTwoPhysicalVolatilityKernelLp (Ξ : AdmissibleCovariance) (q : Overlap) :
    (sectionTwoPhysicalVolatilityKernelLp Ξ q : ℝ≥0 → ℝ) =ᵐ[nonnegativeLebesgueMeasure]
      sectionTwoPhysicalVolatilityKernel Ξ q := MemLp.coeFn_toLp _

theorem norm_sq_sectionTwoPhysicalVolatilityKernelLp (Ξ : AdmissibleCovariance) (q : Overlap) :
    ‖sectionTwoPhysicalVolatilityKernelLp Ξ q‖ ^ 2 = Ξ.first q := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  calc
    _ = ∫t in Ioc (0 : ℝ≥0) q.val.toNNReal, (physicalVolatility Ξ t)^2
        ∂nonnegativeLebesgueMeasure := by
      rw [← integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      filter_upwards [coeFn_sectionTwoPhysicalVolatilityKernelLp Ξ q] with t ht
      rw [Real.inner_apply, ht]
      by_cases h : t ∈ Ioc 0 q.val.toNNReal <;> simp [sectionTwoPhysicalVolatilityKernel, h, pow_two]
    _ = Ξ.first q := by
      rw [integral_physicalVolatility_sq, Real.coe_toNNReal _ q.property.1]

theorem inner_intervalIndicator_sectionTwoPhysicalVolatilityKernelLp
    (Ξ : AdmissibleCovariance) (q : Overlap) (t : ℝ≥0) :
    ⟪intervalIndicator t, sectionTwoPhysicalVolatilityKernelLp Ξ q⟫_ℝ =
      ∫u in (0 : ℝ)..min (t : ℝ) (q : ℝ), Real.sqrt (Ξ.second u) := by
  rw [L2.inner_def]
  calc
    _ = ∫v in Ioc (0 : ℝ≥0) (min t q.val.toNNReal), physicalVolatility Ξ v
        ∂nonnegativeLebesgueMeasure := by
      rw [← integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      filter_upwards [coeFn_sectionTwoPhysicalVolatilityKernelLp Ξ q,
        (show (intervalIndicator t : ℝ≥0 → ℝ) =ᵐ[nonnegativeLebesgueMeasure]
          (Ioc 0 t).indicator (fun _ => 1) from indicatorConstLp_coeFn)] with v hv hi
      rw [Real.inner_apply, hv, hi]
      simp only [sectionTwoPhysicalVolatilityKernel]
      by_cases h0 : 0 < v <;> by_cases ht : v ≤ t <;>
        by_cases hq : v ≤ q.val.toNNReal <;> simp [h0, ht, hq]
    _ = _ := by
      rw [integral_nonnegative_Ioc_eq_real_Icc
        (fun v (_ : Unit) => physicalVolatility Ξ v) (min t q.val.toNNReal) ()]
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le
        (min t q.val.toNNReal).coe_nonneg]
      rw [NNReal.coe_min, Real.coe_toNNReal _ q.property.1]
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le (le_min t.coe_nonneg q.property.1)] at hu
      simp only [physicalVolatility_eq, Real.coe_toNNReal _ hu.1]

theorem inner_sectionTwoPhysicalBrownianKernelFamily_original_driver
    (Ξ : AdmissibleCovariance) (q : Overlap) (t : ℝ≥0) :
    ⟪sectionTwoPhysicalBrownianKernelFamily Ξ t,
      mixedBeta Ξ.toEvenMixture • intervalIndicator (sectionTwoBrownianTime Ξ q)⟫_ℝ =
      ⟪intervalIndicator t, sectionTwoPhysicalVolatilityKernelLp Ξ q⟫_ℝ := by
  rw [inner_intervalIndicator_sectionTwoPhysicalVolatilityKernelLp]
  have hq : (q : ℝ) ≤ 1 := q.property.2
  have ha : sectionTwoBrownianTime Ξ q ≤ 1 := by
    exact_mod_cast (Real.coe_toNNReal _ (Ξ.clock_mem_unit q.property).1).trans_le
      (Ξ.clock_mem_unit q.property).2
  by_cases ht : t ≤ 1
  · let s : Overlap := ⟨t, t.coe_nonneg, by exact_mod_cast ht⟩
    have he : sectionTwoPhysicalBrownianKernelFamily Ξ t =
        sectionTwoPhysicalBrownianKernelLp Ξ s := by
      rw [sectionTwoPhysicalBrownianKernelFamily, unitWienerKernelExtension, dite_eq_left ht]
    rw [he, inner_sectionTwoPhysicalBrownianKernelLp_original_driver]
  · rw [sectionTwoPhysicalBrownianKernelFamily, unitWienerKernelExtension, dite_eq_right ht,
      inner_add_left, inner_sectionTwoPhysicalBrownianKernelLp_original_driver]
    have htr : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast le_of_not_ge ht
    have htail : ⟪intervalIndicator t - intervalIndicator 1,
        mixedBeta Ξ.toEvenMixture • intervalIndicator (sectionTwoBrownianTime Ξ q)⟫_ℝ = 0 := by
      rw [real_inner_smul_right, inner_sub_left, inner_intervalIndicator, inner_intervalIndicator]
      have har : (sectionTwoBrownianTime Ξ q : ℝ) ≤ 1 := by exact_mod_cast ha
      simp only [NNReal.coe_one, min_eq_right har, min_eq_right (har.trans htr), sub_self, mul_zero]
    rw [htail, add_zero]
    change (∫u in (0 : ℝ)..min 1 (q : ℝ), Real.sqrt (Ξ.second u)) = _
    rw [min_eq_right hq, min_eq_right (hq.trans htr)]

/-- The physical square-root-volatility kernel transports exactly to the
original normalized-clock noise kernel. -/
theorem sectionTwoPhysicalVolatilityKernel_transport (Ξ : AdmissibleCovariance) (q : Overlap) :
    wienerKernelTransport (sectionTwoPhysicalBrownianKernelFamily Ξ)
        (sectionTwoPhysicalBrownianKernelFamily_gram Ξ) (sectionTwoPhysicalVolatilityKernelLp Ξ q) =
      mixedBeta Ξ.toEvenMixture • intervalIndicator (sectionTwoBrownianTime Ξ q) := by
  apply wienerKernelTransport_eq_of_interval_pairings
  · exact inner_sectionTwoPhysicalBrownianKernelFamily_original_driver Ξ q
  · apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq_sectionTwoPhysicalVolatilityKernelLp,
      ← real_inner_self_eq_norm_sq, real_inner_smul_left, real_inner_smul_right,
      inner_intervalIndicator, min_self]
    calc
      mixedBeta Ξ.toEvenMixture *
          (mixedBeta Ξ.toEvenMixture * (sectionTwoBrownianTime Ξ q : ℝ)) =
          (mixedBeta Ξ.toEvenMixture)^2 * (sectionTwoBrownianTime Ξ q : ℝ) := by ring
      _ = Ξ.first q := sectionTwoClockDriver_variance Ξ q

/-- The genuine deterministic Wiener integral of the printed physical
volatility against the independently proved physical Brownian driver. -/
def sectionTwoPhysicalNoiseWienerIntegral (Ξ : AdmissibleCovariance) (q : Overlap) :
    BrownianSample → ℝ :=
  wienerIntegral (isBrownianReal_sectionTwoPhysicalBrownian Ξ).toIsPreBrownianReal
    (sectionTwoPhysicalVolatilityKernelLp Ξ q)

theorem sectionTwoPhysicalNoiseWienerIntegral_ae_eq_clock
    (Ξ : AdmissibleCovariance) (q : Overlap) :
    sectionTwoPhysicalNoiseWienerIntegral Ξ q =ᵐ[canonicalBrownianMeasure]
      sectionTwoClockDriver Ξ q := by
  have he : wienerIntegral (isBrownianReal_sectionTwoPhysicalBrownian Ξ).toIsPreBrownianReal
        (sectionTwoPhysicalVolatilityKernelLp Ξ q) =
      mixedBeta Ξ.toEvenMixture •
        brownianLp isBrownianReal_canonicalBrownian.toIsPreBrownianReal (sectionTwoBrownianTime Ξ q) := by
    rw [show wienerIntegral (isBrownianReal_sectionTwoPhysicalBrownian Ξ).toIsPreBrownianReal
          (sectionTwoPhysicalVolatilityKernelLp Ξ q) =
        wienerIntegral isBrownianReal_canonicalBrownian.toIsPreBrownianReal
          (wienerKernelTransport (sectionTwoPhysicalBrownianKernelFamily Ξ)
            (sectionTwoPhysicalBrownianKernelFamily_gram Ξ) (sectionTwoPhysicalVolatilityKernelLp Ξ q)) from
      wienerIntegral_wienerBrownianDriver _ _ _ _,
      sectionTwoPhysicalVolatilityKernel_transport, map_smul, wienerIntegral_intervalIndicator]
  change ((wienerIntegral (isBrownianReal_sectionTwoPhysicalBrownian Ξ).toIsPreBrownianReal
    (sectionTwoPhysicalVolatilityKernelLp Ξ q) : Lp ℝ 2 canonicalBrownianMeasure) : BrownianSample → ℝ)
    =ᵐ[canonicalBrownianMeasure] sectionTwoClockDriver Ξ q
  rw [he]
  filter_upwards [Lp.coeFn_smul (mixedBeta Ξ.toEvenMixture)
    (brownianLp isBrownianReal_canonicalBrownian.toIsPreBrownianReal (sectionTwoBrownianTime Ξ q)),
    coeFn_brownianLp isBrownianReal_canonicalBrownian.toIsPreBrownianReal (sectionTwoBrownianTime Ξ q)]
    with sample hsm hb
  rw [hsm]
  simpa only [Pi.smul_apply, smul_eq_mul, sectionTwoClockDriver] using
    congrArg (fun x => mixedBeta Ξ.toEvenMixture * x) hb

/-- The original canonical Brownian past, sampled at the actual covariance
clock. This is the past already used to construct the selected diffusion. -/
abbrev sectionTwoPhysicalBrownianPast (Ξ : AdmissibleCovariance) (q : Overlap) :
    MeasurableSpace BrownianSample :=
  Filtration.natural canonicalBrownian (fun t => (measurable_canonicalBrownian t).stronglyMeasurable)
    (sectionTwoBrownianTime Ξ q)

theorem sectionTwoPhysicalBrownianKernelLp_supported (Ξ : AdmissibleCovariance) (q : Overlap) :
    ∀ᵐ v ∂nonnegativeLebesgueMeasure, sectionTwoBrownianTime Ξ q < v →
      sectionTwoPhysicalBrownianKernelLp Ξ q v = 0 := by
  filter_upwards [coeFn_sectionTwoPhysicalBrownianKernelLp Ξ q] with v hv
  intro htime
  rw [hv]
  have ha : (sectionTwoBrownianTime Ξ q : ℝ) = Ξ.clock q :=
    Real.coe_toNNReal _ (Ξ.clock_mem_unit q.property).1
  have hvr : Ξ.clock q < (v : ℝ) := by
    rw [← ha]
    exact_mod_cast htime
  exact ite_eq_right (show (v : ℝ) ∉ Ioc (0 : ℝ) (Ξ.clock q) from
    fun h => (not_le_of_gt hvr) h.2)

/-- Every physical Brownian value is adapted modulo null sets to the same
original clock past as the selected diffusion. The continuous modification
does not require literal strong adaptation to the uncompleted raw past. -/
theorem aestronglyMeasurable_sectionTwoPhysicalBrownian_past
    (Ξ : AdmissibleCovariance) (q : Overlap) :
    AEStronglyMeasurable[sectionTwoPhysicalBrownianPast Ξ q]
      (sectionTwoPhysicalBrownian Ξ q.val.toNNReal) canonicalBrownianMeasure :=
  (aestronglyMeasurable_wienerIntegral_of_supported
    isBrownianReal_canonicalBrownian.toIsPreBrownianReal
    (fun t => (measurable_canonicalBrownian t).stronglyMeasurable)
    (sectionTwoBrownianTime Ξ q) (sectionTwoPhysicalBrownianKernelLp Ξ q)
    (sectionTwoPhysicalBrownianKernelLp_supported Ξ q)).congr
    (sectionTwoPhysicalBrownian_ae_eq_wiener Ξ q).symm

theorem sectionTwoPhysicalBrownian_increment_ae_eq_wiener
    (Ξ : AdmissibleCovariance) (s t : Overlap) :
    sectionTwoPhysicalBrownian Ξ t.val.toNNReal - sectionTwoPhysicalBrownian Ξ s.val.toNNReal
      =ᵐ[canonicalBrownianMeasure]
        wienerIntegral isBrownianReal_canonicalBrownian.toIsPreBrownianReal
          (sectionTwoPhysicalBrownianKernelLp Ξ t - sectionTwoPhysicalBrownianKernelLp Ξ s) := by
  exact ((sectionTwoPhysicalBrownian_ae_eq_wiener Ξ t).sub
    (sectionTwoPhysicalBrownian_ae_eq_wiener Ξ s)).trans (by
      rw [map_sub]
      exact (Lp.coeFn_sub _ _).symm)

theorem inner_sectionTwoPhysicalBrownianKernelLp_increment_past
    (Ξ : AdmissibleCovariance) (s t : Overlap) (hst : s ≤ t)
    (u : ℝ≥0) (hu : u ≤ sectionTwoBrownianTime Ξ s) :
    ⟪sectionTwoPhysicalBrownianKernelLp Ξ t - sectionTwoPhysicalBrownianKernelLp Ξ s,
      intervalIndicator u⟫_ℝ = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [coeFn_sectionTwoPhysicalBrownianKernelLp Ξ t,
    coeFn_sectionTwoPhysicalBrownianKernelLp Ξ s,
    Lp.coeFn_sub (sectionTwoPhysicalBrownianKernelLp Ξ t) (sectionTwoPhysicalBrownianKernelLp Ξ s),
    (show (intervalIndicator u : ℝ≥0 → ℝ) =ᵐ[nonnegativeLebesgueMeasure]
      (Ioc 0 u).indicator (fun _ => 1) from indicatorConstLp_coeFn)] with v ht hs hd hi
  rw [Real.inner_apply, hd]
  simp only [Pi.sub_apply, Pi.zero_apply]
  rw [ht, hs, hi]
  by_cases hv : v ∈ Ioc 0 u
  · have has : (sectionTwoBrownianTime Ξ s : ℝ) = Ξ.clock s :=
      Real.coe_toNNReal _ (Ξ.clock_mem_unit s.property).1
    have hvs : (v : ℝ) ∈ Ioc (0 : ℝ) (Ξ.clock s) := by
      constructor
      · exact_mod_cast hv.1
      · rw [← has]
        exact_mod_cast hv.2.trans hu
    have hvt : (v : ℝ) ∈ Ioc (0 : ℝ) (Ξ.clock t) :=
      ⟨hvs.1, hvs.2.trans (Ξ.clock_strictMonoOn.monotoneOn s.property.1 t.property.1 hst)⟩
    simp only [sectionTwoPhysicalBrownianKernel, sectionTwoPhysicalBrownianKernelReal,
      ite_eq_left hvt, ite_eq_left hvs, sub_self, zero_mul]
  · rw [Set.indicator_of_notMem hv, mul_zero]

/-- The physical standard Brownian increments are independent of the actual
original diffusion past. This is stronger than an unfiltered Brownian law. -/
theorem indep_sectionTwoPhysicalBrownian_increment_past
    (Ξ : AdmissibleCovariance) (s t : Overlap) (hst : s ≤ t) :
    Indep (MeasurableSpace.comap
      (sectionTwoPhysicalBrownian Ξ t.val.toNNReal - sectionTwoPhysicalBrownian Ξ s.val.toNNReal)
      inferInstance) (sectionTwoPhysicalBrownianPast Ξ s) canonicalBrownianMeasure := by
  apply indep_wienerIntegral_natural_congr isBrownianReal_canonicalBrownian.toIsPreBrownianReal
    (fun u => (measurable_canonicalBrownian u).stronglyMeasurable)
    (sectionTwoPhysicalBrownianKernelLp Ξ t - sectionTwoPhysicalBrownianKernelLp Ξ s)
    (sectionTwoBrownianTime Ξ s)
  · exact fun u hu => inner_sectionTwoPhysicalBrownianKernelLp_increment_past Ξ s t hst u hu
  · exact (sectionTwoPhysicalBrownian_increment_ae_eq_wiener Ξ s t).symm

end GeneralDepthPaper
