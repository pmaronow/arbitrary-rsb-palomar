module

public import GeneralDepthPaper.RevisedSectionTwoStochasticClock
public import GeneralDepthPaper.PhysicalVolatility
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section

/-! Compact inverse-clock regularity for the physical Brownian construction.
The inverse is the actual inverse of the covariance clock, including its
closed endpoints. No derivative bound or nonzero volatility at zero is
required. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace GeneralDepthPaper
open FourPapersCommon

/-- The covariance clock as an equivalence of the closed unit interval. -/
def sectionTwoClockEquiv (Ξ : AdmissibleCovariance) : Overlap ≃ Overlap where
  toFun q := ⟨Ξ.clock q, Ξ.clock_mem_unit q.property⟩
  invFun := sectionTwoOverlapAtVarianceTime Ξ
  left_inv q := sectionTwoOverlapAtVarianceTime_unique Ξ _ q rfl
  right_inv v := Subtype.ext (sectionTwoOverlapAtVarianceTime_clock Ξ v)

theorem continuous_sectionTwoClockEquiv (Ξ : AdmissibleCovariance) :
    Continuous (sectionTwoClockEquiv Ξ) :=
  (Ξ.continuous_clock.comp continuous_subtype_val).subtype_mk _

theorem continuous_sectionTwoOverlapAtVarianceTime (Ξ : AdmissibleCovariance) :
    Continuous (sectionTwoOverlapAtVarianceTime Ξ) := by
  exact (continuous_sectionTwoClockEquiv Ξ).continuous_symm_of_equiv_compact_to_t2

theorem uniformContinuous_sectionTwoOverlapAtVarianceTime (Ξ : AdmissibleCovariance) :
    UniformContinuous (sectionTwoOverlapAtVarianceTime Ξ) := by
  exact CompactSpace.uniformContinuous_of_continuous
    (continuous_sectionTwoOverlapAtVarianceTime Ξ)

theorem measurable_sectionTwoOverlapAtVarianceTime (Ξ : AdmissibleCovariance) :
    Measurable (sectionTwoOverlapAtVarianceTime Ξ) :=
  (continuous_sectionTwoOverlapAtVarianceTime Ξ).measurable

@[simp] theorem sectionTwoOverlapAtVarianceTime_zero (Ξ : AdmissibleCovariance) :
    sectionTwoOverlapAtVarianceTime Ξ ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ :=
  sectionTwoOverlapAtVarianceTime_unique Ξ _ _ Ξ.clock_zero

@[simp] theorem sectionTwoOverlapAtVarianceTime_one (Ξ : AdmissibleCovariance) :
    sectionTwoOverlapAtVarianceTime Ξ ⟨1, by norm_num⟩ = ⟨1, by norm_num⟩ :=
  sectionTwoOverlapAtVarianceTime_unique Ξ _ _ Ξ.clock_one

theorem strictMono_sectionTwoOverlapAtVarianceTime (Ξ : AdmissibleCovariance) :
    StrictMono (sectionTwoOverlapAtVarianceTime Ξ) := by
  intro u v huv
  by_contra h
  have hquv : (sectionTwoOverlapAtVarianceTime Ξ v : ℝ) ≤
      (sectionTwoOverlapAtVarianceTime Ξ u : ℝ) := le_of_not_gt h
  have hclock := Ξ.clock_strictMonoOn.monotoneOn
    (sectionTwoOverlapAtVarianceTime Ξ v).property.1
    (sectionTwoOverlapAtVarianceTime Ξ u).property.1 hquv
  rw [sectionTwoOverlapAtVarianceTime_clock, sectionTwoOverlapAtVarianceTime_clock] at hclock
  exact (not_le_of_gt huv) hclock

/-- Physical volatility read along the normalized covariance clock. -/
def sectionTwoVarianceVolatility (Ξ : AdmissibleCovariance) (v : Overlap) : ℝ :=
  physicalVolatility Ξ (sectionTwoOverlapAtVarianceTime Ξ v : ℝ).toNNReal

theorem continuous_sectionTwoVarianceVolatility (Ξ : AdmissibleCovariance) :
    Continuous (sectionTwoVarianceVolatility Ξ) :=
  (continuous_physicalVolatility Ξ).comp
    (continuous_real_toNNReal.comp
      (continuous_subtype_val.comp (continuous_sectionTwoOverlapAtVarianceTime Ξ)))

theorem uniformContinuous_sectionTwoVarianceVolatility (Ξ : AdmissibleCovariance) :
    UniformContinuous (sectionTwoVarianceVolatility Ξ) := by
  exact CompactSpace.uniformContinuous_of_continuous
    (continuous_sectionTwoVarianceVolatility Ξ)

/-- Clamp used only to make partition-node constructions total. On the
closed normalized-time interval it is the identity. -/
def sectionTwoClampedVarianceOverlap (v : ℝ) : Overlap :=
  ⟨max 0 (min 1 v), le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem continuous_sectionTwoClampedVarianceOverlap :
    Continuous sectionTwoClampedVarianceOverlap :=
  (continuous_const.max (continuous_const.min continuous_id)).subtype_mk _

theorem uniformContinuous_sectionTwoClampedVarianceOverlap :
    UniformContinuous sectionTwoClampedVarianceOverlap :=
  (((LipschitzWith.id.const_min 1).const_max 0).subtype_mk _).uniformContinuous

@[simp] theorem sectionTwoClampedVarianceOverlap_coe (v : Overlap) :
    sectionTwoClampedVarianceOverlap v = v := by
  apply Subtype.ext
  change max 0 (min 1 (v : ℝ)) = (v : ℝ)
  rw [min_eq_right v.property.2, max_eq_right v.property.1]

/-- Physical overlap corresponding to a nonnegative normalized-time node. -/
def sectionTwoPhysicalOverlapAtTime (Ξ : AdmissibleCovariance) (v : ℝ≥0) : Overlap :=
  sectionTwoOverlapAtVarianceTime Ξ (sectionTwoClampedVarianceOverlap v)

/-- The same physical node with the nonnegative-time type used by Brownian
processes. -/
def sectionTwoPhysicalTimeAtVarianceTime (Ξ : AdmissibleCovariance) (v : ℝ≥0) : ℝ≥0 :=
  (sectionTwoPhysicalOverlapAtTime Ξ v : ℝ).toNNReal

theorem continuous_sectionTwoPhysicalOverlapAtTime (Ξ : AdmissibleCovariance) :
    Continuous (sectionTwoPhysicalOverlapAtTime Ξ) :=
  (continuous_sectionTwoOverlapAtVarianceTime Ξ).comp
    (continuous_sectionTwoClampedVarianceOverlap.comp NNReal.continuous_coe)

theorem continuous_sectionTwoPhysicalTimeAtVarianceTime (Ξ : AdmissibleCovariance) :
    Continuous (sectionTwoPhysicalTimeAtVarianceTime Ξ) :=
  continuous_real_toNNReal.comp
    (continuous_subtype_val.comp (continuous_sectionTwoPhysicalOverlapAtTime Ξ))

theorem uniformContinuous_sectionTwoPhysicalTimeAtVarianceTime (Ξ : AdmissibleCovariance) :
    UniformContinuous (sectionTwoPhysicalTimeAtVarianceTime Ξ) :=
  Real.lipschitzWith_toNNReal.uniformContinuous.comp
    (uniformContinuous_subtype_val.comp
      ((uniformContinuous_sectionTwoOverlapAtVarianceTime Ξ).comp
        (uniformContinuous_sectionTwoClampedVarianceOverlap.comp
          uniformContinuous_subtype_val)))

theorem sectionTwoPhysicalTimeAtVarianceTime_coe (Ξ : AdmissibleCovariance) (v : ℝ≥0) :
    (sectionTwoPhysicalTimeAtVarianceTime Ξ v : ℝ) = sectionTwoPhysicalOverlapAtTime Ξ v :=
  Real.coe_toNNReal _ (sectionTwoPhysicalOverlapAtTime Ξ v).property.1

theorem sectionTwoPhysicalTimeAtVarianceTime_clock (Ξ : AdmissibleCovariance)
    (v : ℝ≥0) (hv : (v : ℝ) ≤ 1) :
    Ξ.clock (sectionTwoPhysicalTimeAtVarianceTime Ξ v) = (v : ℝ) := by
  rw [sectionTwoPhysicalTimeAtVarianceTime_coe]
  change Ξ.clock (sectionTwoOverlapAtVarianceTime Ξ
    (sectionTwoClampedVarianceOverlap v)) = (v : ℝ)
  rw [sectionTwoOverlapAtVarianceTime_clock]
  change max 0 (min 1 (v : ℝ)) = (v : ℝ)
  rw [min_eq_right hv]
  exact max_eq_right v.coe_nonneg

end GeneralDepthPaper
