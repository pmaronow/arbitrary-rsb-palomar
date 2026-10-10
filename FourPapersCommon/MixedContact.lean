module

public import FourPapersCommon.MixedFirstVariation
public import FourPapersCommon.MixedMinimizer
public import FourPapersCommon.WeightedEndpointMinimum

@[expose] public section


/-! Actual scalar contact identities for all admissible even mixtures and
all fields.  The origin proof does not divide by ξ″(0), which may vanish. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Real Filter
open scoped Topology
namespace FourPapersCommon
set_option maxHeartbeats 800000

theorem mixedGamma_lt_one (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : ParisiMeasure) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    mixedGamma ξ h μ q < 1 := by
  have hp := mixedCurvatureMoment2_pos ξ h μ hq
  have hl := mixedCurvatureMoment2_le_one_sub_Gamma ξ h μ hq
  linarith

theorem mixedGradient_mem_Ioo (ξ : AdmissibleEvenMixture) (μ : ParisiMeasure)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (x : ℝ) :
    mixedGradient ξ μ (q, x) ∈ Ioo (-1 : ℝ) 1 := by
  have hp := mixedHessian_pos ξ μ q x hq
  have hl := mixedHessian_add_gradient_sq_le_one ξ μ (q, x)
  constructor <;> nlinarith [sq_nonneg (mixedGradient ξ μ (q, x) + 1),
    sq_nonneg (mixedGradient ξ μ (q, x) - 1)]

theorem continuousOn_mixedFirstVariation (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : ParisiMeasure) : ContinuousOn (mixedFirstVariation ξ h μ) (Icc (0 : ℝ) 1) := by
  have hc : ContinuousOn (fun s => ξ.second s * (mixedGamma ξ h μ s - s))
      (Icc (0 : ℝ) 1) :=
    (ξ.continuousOn_second.mono (by intro s hs; exact ⟨by linarith [hs.1], hs.2⟩)).mul
      ((continuousOn_mixedGamma ξ h μ).sub continuousOn_id)
  have hi : IntegrableOn (fun s => ξ.second s * (mixedGamma ξ h μ s - s))
      (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact hc.integrableOn_compact isCompact_Icc
  have H := intervalIntegral.continuousOn_primitive_interval hi
  rw [uIcc_of_le zero_le_one] at H
  exact H.const_mul (1 / 2 : ℝ)

theorem hasDerivAt_mixedFirstVariation (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : ParisiMeasure) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (mixedFirstVariation ξ h μ)
      ((1 / 2 : ℝ) * ξ.second q * (mixedGamma ξ h μ q - q)) q := by
  have hc : ContinuousOn (fun s => ξ.second s * (mixedGamma ξ h μ s - s))
      (Icc (0 : ℝ) 1) :=
    (ξ.continuousOn_second.mono (by intro s hs; exact ⟨by linarith [hs.1], hs.2⟩)).mul
      ((continuousOn_mixedGamma ξ h μ).sub continuousOn_id)
  have hi : IntervalIntegrable (fun s => ξ.second s * (mixedGamma ξ h μ s - s)) volume 0 q :=
    (hc.mono (Icc_subset_Icc_right hq.2.le)).intervalIntegrable_of_Icc hq.1.le
  have hd := (intervalIntegral.integral_hasDerivAt_right hi
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hc.mono Ioo_subset_Icc_self) q hq)
    (hc.continuousAt (Icc_mem_nhds hq.1 hq.2))).const_mul (1 / 2 : ℝ)
  convert! hd using 1 <;> ring

theorem mixedGamma_eq_zero_of_zero_mem_support (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : ParisiMeasure) (hmin : IsMixedMinimizer ξ h μ)
    (hzero : (⟨0, by norm_num⟩ : Overlap) ∈ (μ : Measure Overlap).support) :
    mixedGamma ξ h μ 0 = 0 := by
  have hmax := (isMixedMinimizer_iff_support_firstVariation_max ξ h μ).mp hmin
  have H := endpointQ_le_of_weighted_minimum (F := fun x => -mixedFirstVariation ξ h μ x)
    (Q := mixedGamma ξ h μ) (w := fun x => (1 / 2 : ℝ) * ξ.second x)
    zero_lt_one (continuousOn_mixedFirstVariation ξ h μ).neg
    ((continuousOn_mixedGamma ξ h μ) 0 (by norm_num))
    (fun x hx => by
      convert (hasDerivAt_mixedFirstVariation ξ h μ hx).neg using 1 <;> ring)
    (fun x hx => mul_pos (by norm_num) (ξ.second_pos ⟨hx.1, hx.2.le⟩))
    (fun x hx => neg_le_neg (hmax _ hzero ⟨x, hx⟩))
  exact le_antisymm H (mixedGamma_nonneg ξ h μ 0)

theorem mixedGamma_eq_overlap_of_support_interior (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : ParisiMeasure) (hmin : IsMixedMinimizer ξ h μ) (q : Overlap)
    (hqs : q ∈ (μ : Measure Overlap).support) (hq : (q : ℝ) ∈ Ioo (0 : ℝ) 1) :
    mixedGamma ξ h μ q = q := by
  have hmax := (isMixedMinimizer_iff_support_firstVariation_max ξ h μ).mp hmin
  have hloc : IsLocalMax (mixedFirstVariation ξ h μ) (q : ℝ) := by
    filter_upwards [Icc_mem_nhds hq.1 hq.2] with x hx
    exact hmax q hqs ⟨x, hx⟩
  have hz := hloc.hasDerivAt_eq_zero (hasDerivAt_mixedFirstVariation ξ h μ hq)
  have hp := ξ.second_pos ⟨hq.1, hq.2.le⟩
  nlinarith

theorem one_not_mem_mixed_minimizer_support (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : ParisiMeasure) (hmin : IsMixedMinimizer ξ h μ) :
    (⟨1, by norm_num⟩ : Overlap) ∉ (μ : Measure Overlap).support := by
  intro hone
  have hmax := (isMixedMinimizer_iff_support_firstVariation_max ξ h μ).mp hmin
  have hmap : MapsTo (fun x : ℝ => 1 - x) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hctsmap : ContinuousOn (fun x : ℝ => 1 - x) (Icc (0 : ℝ) 1) :=
    continuousOn_const.sub continuousOn_id
  have hF : ContinuousOn (fun x => -mixedFirstVariation ξ h μ (1 - x)) (Icc (0 : ℝ) 1) :=
    ((continuousOn_mixedFirstVariation ξ h μ).comp hctsmap hmap).neg
  have hQ : ContinuousOn (fun x => 1 - mixedGamma ξ h μ (1 - x)) (Icc (0 : ℝ) 1) :=
    continuousOn_const.sub ((continuousOn_mixedGamma ξ h μ).comp hctsmap hmap)
  have H := endpointQ_le_of_weighted_minimum
    (F := fun x => -mixedFirstVariation ξ h μ (1 - x))
    (Q := fun x => 1 - mixedGamma ξ h μ (1 - x))
    (w := fun x => (1 / 2 : ℝ) * ξ.second (1 - x)) zero_lt_one hF
    (hQ 0 (by norm_num))
    (fun x hx => by
      have hr : 1 - x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
      have hd := ((hasDerivAt_mixedFirstVariation ξ h μ hr).comp x
        ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x))).neg
      convert! hd using 1 <;> ring)
    (fun x hx => mul_pos (by norm_num) (ξ.second_pos
      ⟨by linarith [hx.2], by linarith [hx.1]⟩))
    (fun x hx => by
      simpa only [sub_zero] using neg_le_neg (hmax _ hone ⟨1 - x, hmap hx⟩))
  have hlt := mixedGamma_lt_one ξ h μ (q := 1) (by norm_num)
  simp only [sub_zero] at H
  linarith

theorem mixedGamma_eq_overlap_of_support (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : ParisiMeasure) (hmin : IsMixedMinimizer ξ h μ) (q : Overlap)
    (hqs : q ∈ (μ : Measure Overlap).support) : mixedGamma ξ h μ q = q := by
  by_cases hq0 : (q : ℝ) = 0
  · have he : q = (⟨0, by norm_num⟩ : Overlap) := Subtype.ext hq0
    rw [he] at hqs ⊢
    exact mixedGamma_eq_zero_of_zero_mem_support ξ h μ hmin hqs
  · have hqpos : 0 < (q : ℝ) := lt_of_le_of_ne q.property.1 (Ne.symm hq0)
    have hq1 : (q : ℝ) < 1 := by
      by_contra H
      have he : q = (⟨1, by norm_num⟩ : Overlap) :=
        Subtype.ext (le_antisymm q.property.2 (le_of_not_gt H))
      exact one_not_mem_mixed_minimizer_support ξ h μ hmin (he ▸ hqs)
    exact mixedGamma_eq_overlap_of_support_interior ξ h μ hmin q hqs ⟨hqpos, hq1⟩

theorem mixedGradient_strictMono (ξ : AdmissibleEvenMixture) (μ : ParisiMeasure)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) : StrictMono (fun x => mixedGradient ξ μ (q, x)) := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(hasDerivAt_mixedGradient_spatial ξ μ q x).deriv]
  exact mixedHessian_pos ξ μ q x hq

theorem field_eq_zero_of_zero_mem_mixed_minimizer_support (ξ : AdmissibleEvenMixture)
    (h : ℝ) (μ : ParisiMeasure) (hmin : IsMixedMinimizer ξ h μ)
    (hzero : (⟨0, by norm_num⟩ : Overlap) ∈ (μ : Measure Overlap).support) : h = 0 := by
  have H := mixedGamma_eq_zero_of_zero_mem_support ξ h μ hmin hzero
  have he : mixedGamma ξ h μ 0 = mixedGradient ξ μ (0, h) ^ 2 := by
    simp only [mixedGamma, mixedState_initial, integral_const, probReal_univ, one_smul]
  rw [he] at H
  have hgrad : mixedGradient ξ μ (0, h) = mixedGradient ξ μ (0, 0) := by
    rw [mixedGradient_at_zero ξ μ 0 (by norm_num)]
    nlinarith [sq_nonneg (mixedGradient ξ μ (0, h))]
  exact (mixedGradient_strictMono ξ μ (q := 0) (by norm_num)).injective hgrad

end FourPapersCommon
