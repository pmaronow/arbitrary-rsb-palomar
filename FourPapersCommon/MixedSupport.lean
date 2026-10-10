module

public import FourPapersCommon.MixedContact
public import FRSB.TerminalOverlap

@[expose] public section


/-! Genuine support endpoints and terminal regions for the mixed functional. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Real Filter
open scoped Topology NNReal ENNReal
namespace FourPapersCommon
set_option maxHeartbeats 800000

theorem mixedMeasure_support_upper (ξ : AdmissibleEvenMixture) (μ : ParisiMeasure)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    (hmax : ∀ x ∈ FRSB.parisiSupport μ, x ≤ q) :
    ∀ x ∈ FRSB.parisiSupport (mixedMeasure ξ μ), x ≤ ξ.clock q := by
  have hae : ∀ᵐ (r : Overlap) ∂(μ : Measure Overlap), ξ.clock (r : ℝ) ≤ ξ.clock q := by
    filter_upwards [(μ : Measure Overlap).support_mem_ae] with r hr
    exact ξ.clock_strictMonoOn.monotoneOn r.property hq (hmax r ⟨r, hr, rfl⟩)
  have ham : ∀ᵐ (r : Overlap) ∂(mixedMeasure ξ μ : Measure Overlap), (r : ℝ) ≤ ξ.clock q := by
    change ∀ᵐ (r : Overlap) ∂(μ.map ξ.unitClock : Measure Overlap), (r : ℝ) ≤ ξ.clock q
    rw [ProbabilityMeasure.toMeasure_map]
    exact (ae_map_iff ξ.continuous_unitClock.measurable.aemeasurable
      (isClosed_le continuous_subtype_val continuous_const).measurableSet).mpr hae
  have hs := (mixedMeasure ξ μ : Measure Overlap).support_subset_of_isClosed
    (isClosed_le continuous_subtype_val continuous_const) ham
  rintro x ⟨r, hr, rfl⟩
  exact hs hr

theorem mixedPotential_terminal_region (ξ : AdmissibleEvenMixture) (μ : ParisiMeasure)
    {q t : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    (hmax : ∀ x ∈ FRSB.parisiSupport μ, x ≤ q) (ht : t ∈ Icc q 1) (x : ℝ) :
    mixedPotential ξ μ (t, x) = Real.log (Real.cosh x) + (ξ.first 1 - ξ.first t) / 2 := by
  have htu : t ∈ Icc (0 : ℝ) 1 := ⟨hq.1.trans ht.1, ht.2⟩
  have H := FRSB.parisiPotential_terminal_region (mixedBeta ξ) (mixedBeta_ne_zero ξ)
    (mixedMeasure ξ μ) (ξ.clock_mem_unitInterval hq) (mixedMeasure_support_upper ξ μ hq hmax)
    ⟨ξ.clock_strictMonoOn.monotoneOn hq htu ht.1, (ξ.clock_mem_unitInterval htu).2⟩ x
  change mixedPotential ξ μ (t, x) = _ at H
  have hv : mixedBeta ξ ^ 2 * (1 - ξ.clock t) = ξ.first 1 - ξ.first t := by
    rw [mixedBeta_sq]
    have hne : ξ.first 1 ≠ 0 := ξ.variance_pos.ne'
    unfold AdmissibleEvenMixture.clock AdmissibleEvenMixture.variance
    field_simp [hne]
  rw [H, hv]

theorem mixedGradient_terminal_region (ξ : AdmissibleEvenMixture) (μ : ParisiMeasure)
    {q t : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    (hmax : ∀ x ∈ FRSB.parisiSupport μ, x ≤ q) (ht : t ∈ Icc q 1) (x : ℝ) :
    mixedGradient ξ μ (t, x) = Real.tanh x := by
  have he : (fun y => mixedPotential ξ μ (t, y)) =
      fun y => Real.log (Real.cosh y) + (ξ.first 1 - ξ.first t) / 2 :=
    funext (mixedPotential_terminal_region ξ μ hq hmax ht)
  have hd := hasDerivAt_mixedPotential_spatial ξ μ t x ⟨hq.1.trans ht.1, ht.2⟩
  rw [he] at hd
  exact hd.unique ((Paper.hasDerivAt_log_cosh x).add_const _)

def mixedSupportMax (μ : ParisiMeasure) : ℝ :=
  Classical.choose ((FRSB.parisiSupport_compact μ).exists_isGreatest (FRSB.parisiSupport_nonempty μ))

theorem mixedSupportMax_isGreatest (μ : ParisiMeasure) :
    IsGreatest (FRSB.parisiSupport μ) (mixedSupportMax μ) :=
  Classical.choose_spec _

theorem mixedSupportMax_mem_unit (μ : ParisiMeasure) : mixedSupportMax μ ∈ Icc (0 : ℝ) 1 :=
  FRSB.parisiSupport_subset μ (mixedSupportMax_isGreatest μ).1

theorem mixedSupportMax_lt_one (ξ : AdmissibleEvenMixture) (h : ℝ) (μ : ParisiMeasure)
    (hmin : IsMixedMinimizer ξ h μ) : mixedSupportMax μ < 1 := by
  have hunit := mixedSupportMax_mem_unit μ
  obtain ⟨r, hr, he⟩ := (mixedSupportMax_isGreatest μ).1
  have hcontact := mixedGamma_eq_overlap_of_support ξ h μ hmin r hr
  have hlt := mixedGamma_lt_one ξ h μ r.property
  rw [he] at hcontact hlt
  linarith

end FourPapersCommon
