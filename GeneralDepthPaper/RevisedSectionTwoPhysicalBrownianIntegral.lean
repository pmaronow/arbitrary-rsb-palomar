module

public import GeneralDepthPaper.RevisedSectionTwoPhysicalBrownianSums
public import GeneralDepthPaper.RevisedSectionTwoPhysicalBrownian
public import GeneralDepthPaper.RevisedSectionTwoPhysicalHessianAdapted
public import GeneralDepthPaper.RevisedSectionTwoPhysicalClockError
public import GeneralDepthPaper.PhysicalHessianPartitionBound
public import FourPapersCommon.BoundedWienerMultiplier

@[expose] public section

/-! Physical-time Hessian left sums converge to the existing covariance-clock
left sums. The proof compares genuine Wiener increments, controls each bounded
Hessian multiplier in L², and telescopes monotone volatility increments. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus Paper
open scoped Topology NNReal ENNReal
namespace GeneralDepthPaper
open FourPapersCommon SpinGlass.Targets
set_option maxHeartbeats 150000

theorem monotone_sectionTwoPhysicalOverlapAtTime (Ξ : AdmissibleCovariance) :
    Monotone (sectionTwoPhysicalOverlapAtTime Ξ) := by
  intro u v huv
  apply (strictMono_sectionTwoOverlapAtVarianceTime Ξ).monotone
  change max 0 (min 1 (u : ℝ)) ≤ max 0 (min 1 (v : ℝ))
  gcongr

theorem sectionTwoPhysicalTimeAtVarianceTime_le_one (Ξ : AdmissibleCovariance)
    (v : ℝ≥0) : sectionTwoPhysicalTimeAtVarianceTime Ξ v ≤ 1 := by
  apply NNReal.coe_le_coe.mp
  rw [sectionTwoPhysicalTimeAtVarianceTime_coe, NNReal.coe_one]
  exact (sectionTwoPhysicalOverlapAtTime Ξ v).property.2

theorem sectionTwoClockDriver_ae_eq_wiener (Ξ : AdmissibleCovariance) (q : Overlap) :
    sectionTwoClockDriver Ξ q =ᵐ[canonicalBrownianMeasure]
      wienerIntegral isBrownianReal_canonicalBrownian.toIsPreBrownianReal
        (mixedBeta Ξ.toEvenMixture • intervalIndicator (sectionTwoBrownianTime Ξ q)) := by
  rw [map_smul, wienerIntegral_intervalIndicator]
  filter_upwards [Lp.coeFn_smul (mixedBeta Ξ.toEvenMixture)
      (brownianLp isBrownianReal_canonicalBrownian.toIsPreBrownianReal
        (sectionTwoBrownianTime Ξ q)),
    coeFn_brownianLp isBrownianReal_canonicalBrownian.toIsPreBrownianReal
      (sectionTwoBrownianTime Ξ q)] with sample hs hb
  rw [hs]
  simp only [Pi.smul_apply, smul_eq_mul, sectionTwoClockDriver, hb]

theorem sectionTwoPhysicalClockCellError_ae (Ξ : AdmissibleCovariance)
    (u v : ℝ≥0) (_hu : (u : ℝ) ≤ 1) (_hv : (v : ℝ) ≤ 1) :
    (fun sample => physicalVolatility Ξ (sectionTwoPhysicalTimeAtVarianceTime Ξ u) *
        (sectionTwoPhysicalBrownian Ξ (sectionTwoPhysicalTimeAtVarianceTime Ξ v) sample -
          sectionTwoPhysicalBrownian Ξ (sectionTwoPhysicalTimeAtVarianceTime Ξ u) sample) -
      (sectionTwoExtendedClockDriver Ξ (sectionTwoPhysicalTimeAtVarianceTime Ξ v) sample -
        sectionTwoExtendedClockDriver Ξ (sectionTwoPhysicalTimeAtVarianceTime Ξ u) sample))
      =ᵐ[canonicalBrownianMeasure]
        wienerIntegral isBrownianReal_canonicalBrownian.toIsPreBrownianReal
          (sectionTwoPhysicalClockCellError Ξ (sectionTwoPhysicalOverlapAtTime Ξ u)
            (sectionTwoPhysicalOverlapAtTime Ξ v)) := by
  let a := sectionTwoPhysicalOverlapAtTime Ξ u
  let b := sectionTwoPhysicalOverlapAtTime Ξ v
  have hJu : sectionTwoExtendedClockDriver Ξ (sectionTwoPhysicalTimeAtVarianceTime Ξ u) =
      sectionTwoClockDriver Ξ a := by
    unfold sectionTwoExtendedClockDriver sectionTwoClockDriver sectionTwoExtendedBrownianClock
      sectionTwoBrownianTime
    rw [sectionTwoPhysicalTimeAtVarianceTime_coe]
  have hJv : sectionTwoExtendedClockDriver Ξ (sectionTwoPhysicalTimeAtVarianceTime Ξ v) =
      sectionTwoClockDriver Ξ b := by
    unfold sectionTwoExtendedClockDriver sectionTwoClockDriver sectionTwoExtendedBrownianClock
      sectionTwoBrownianTime
    rw [sectionTwoPhysicalTimeAtVarianceTime_coe]
  have hσ : physicalVolatility Ξ (sectionTwoPhysicalTimeAtVarianceTime Ξ u) =
      Real.sqrt (Ξ.second a) := by
    rw [physicalVolatility_eq, sectionTwoPhysicalTimeAtVarianceTime_coe]
  rw [hJu, hJv, hσ]
  have hB := sectionTwoPhysicalBrownian_increment_ae_eq_wiener Ξ a b
  have hJ : sectionTwoClockDriver Ξ b - sectionTwoClockDriver Ξ a
      =ᵐ[canonicalBrownianMeasure]
      wienerIntegral isBrownianReal_canonicalBrownian.toIsPreBrownianReal
        (mixedBeta Ξ.toEvenMixture •
          (intervalIndicator (sectionTwoBrownianTime Ξ b) -
            intervalIndicator (sectionTwoBrownianTime Ξ a))) := by
    rw [smul_sub, map_sub]
    exact ((sectionTwoClockDriver_ae_eq_wiener Ξ b).sub
      (sectionTwoClockDriver_ae_eq_wiener Ξ a)).trans (Lp.coeFn_sub _ _).symm
  change (fun sample => Real.sqrt (Ξ.second a) *
      (sectionTwoPhysicalBrownian Ξ b.val.toNNReal sample -
        sectionTwoPhysicalBrownian Ξ a.val.toNNReal sample) -
      (sectionTwoClockDriver Ξ b sample - sectionTwoClockDriver Ξ a sample))
    =ᵐ[canonicalBrownianMeasure] wienerIntegral
      isBrownianReal_canonicalBrownian.toIsPreBrownianReal
      (Real.sqrt (Ξ.second a) •
        (sectionTwoPhysicalBrownianKernelLp Ξ b - sectionTwoPhysicalBrownianKernelLp Ξ a) -
       mixedBeta Ξ.toEvenMixture •
        (intervalIndicator (sectionTwoBrownianTime Ξ b) -
          intervalIndicator (sectionTwoBrownianTime Ξ a)))
  rw [map_sub, map_smul]
  filter_upwards [hB, hJ,
    Lp.coeFn_sub
      (Real.sqrt (Ξ.second a) • wienerIntegral
        isBrownianReal_canonicalBrownian.toIsPreBrownianReal
        (sectionTwoPhysicalBrownianKernelLp Ξ b - sectionTwoPhysicalBrownianKernelLp Ξ a))
      (wienerIntegral isBrownianReal_canonicalBrownian.toIsPreBrownianReal
        (mixedBeta Ξ.toEvenMixture •
          (intervalIndicator (sectionTwoBrownianTime Ξ b) -
            intervalIndicator (sectionTwoBrownianTime Ξ a)))),
    Lp.coeFn_smul (Real.sqrt (Ξ.second a))
      (wienerIntegral isBrownianReal_canonicalBrownian.toIsPreBrownianReal
        (sectionTwoPhysicalBrownianKernelLp Ξ b - sectionTwoPhysicalBrownianKernelLp Ξ a))]
    with sample hb hj hs hsm
  rw [hs]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at *
  rw [hsm, hb, hj]


theorem aestronglyMeasurable_sectionTwoPhysicalHessianAtVarianceTime
    (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) (v : ℝ≥0) (hv : (v : ℝ) ≤ 1) :
    AEStronglyMeasurable (sectionTwoPhysicalHessianAtVarianceTime Ξ μ v)
      canonicalBrownianMeasure :=
  ((stronglyMeasurable_sectionTwoActualHessianAtVarianceTime Ξ μ v hv).mono
    (canonicalBrownianFiltration.le v)).aestronglyMeasurable

def sectionTwoPhysicalHessianCellErrorLp (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) (u v : ℝ≥0) (hu : (u : ℝ) ≤ 1) :
    Lp ℝ 2 canonicalBrownianMeasure :=
  boundedWienerMultiplier isBrownianReal_canonicalBrownian.toIsPreBrownianReal
    (sectionTwoPhysicalHessianAtVarianceTime Ξ μ u)
    (aestronglyMeasurable_sectionTwoPhysicalHessianAtVarianceTime Ξ μ u hu)
    (norm_sectionTwoPhysicalHessianAtVarianceTime_le_one Ξ μ u)
    (sectionTwoPhysicalClockCellError Ξ (sectionTwoPhysicalOverlapAtTime Ξ u)
      (sectionTwoPhysicalOverlapAtTime Ξ v))

theorem sectionTwoPhysicalHessianCellErrorLp_coe_ae (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) (u v : ℝ≥0) (hu : (u : ℝ) ≤ 1) (hv : (v : ℝ) ≤ 1) :
    (sectionTwoPhysicalHessianCellErrorLp Ξ μ u v hu : BrownianSample → ℝ)
      =ᵐ[canonicalBrownianMeasure] fun sample =>
      sectionTwoPhysicalHessianAtVarianceTime Ξ μ u sample *
        physicalVolatility Ξ (sectionTwoPhysicalTimeAtVarianceTime Ξ u) *
        (sectionTwoPhysicalBrownian Ξ (sectionTwoPhysicalTimeAtVarianceTime Ξ v) sample -
          sectionTwoPhysicalBrownian Ξ (sectionTwoPhysicalTimeAtVarianceTime Ξ u) sample) -
      sectionTwoPhysicalHessianAtVarianceTime Ξ μ u sample * 1 *
        (sectionTwoExtendedClockDriver Ξ (sectionTwoPhysicalTimeAtVarianceTime Ξ v) sample -
          sectionTwoExtendedClockDriver Ξ (sectionTwoPhysicalTimeAtVarianceTime Ξ u) sample) := by
  filter_upwards [boundedWienerMultiplier_coe_ae
    isBrownianReal_canonicalBrownian.toIsPreBrownianReal
    (sectionTwoPhysicalHessianAtVarianceTime Ξ μ u)
    (aestronglyMeasurable_sectionTwoPhysicalHessianAtVarianceTime Ξ μ u hu)
    (norm_sectionTwoPhysicalHessianAtVarianceTime_le_one Ξ μ u)
    (sectionTwoPhysicalClockCellError Ξ (sectionTwoPhysicalOverlapAtTime Ξ u)
      (sectionTwoPhysicalOverlapAtTime Ξ v)),
    sectionTwoPhysicalClockCellError_ae Ξ u v hu hv] with sample hs he
  change (boundedWienerMultiplier _ _ _ _ _ : BrownianSample → ℝ) sample = _
  rw [hs, ←he]
  ring

theorem sectionTwoPhysicalHessianCellErrorLp_norm_le (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) (u v : ℝ≥0) (hu : (u : ℝ) ≤ 1) (huv : u ≤ v) :
    ‖sectionTwoPhysicalHessianCellErrorLp Ξ μ u v hu‖ ≤
      (physicalVolatility Ξ (sectionTwoPhysicalTimeAtVarianceTime Ξ v) -
       physicalVolatility Ξ (sectionTwoPhysicalTimeAtVarianceTime Ξ u)) *
      Real.sqrt (dist (sectionTwoPhysicalTimeAtVarianceTime Ξ u)
        (sectionTwoPhysicalTimeAtVarianceTime Ξ v)) := by
  apply (boundedWienerMultiplier_norm_le _ _ _ _ _).trans
  have hab := monotone_sectionTwoPhysicalOverlapAtTime Ξ huv
  have h := norm_sectionTwoPhysicalClockCellError_le Ξ _ _ hab
  have habr : (sectionTwoPhysicalOverlapAtTime Ξ u : ℝ) ≤
      (sectionTwoPhysicalOverlapAtTime Ξ v : ℝ) := hab
  simp only [physicalVolatility_eq, sectionTwoPhysicalTimeAtVarianceTime_coe,
    NNReal.dist_eq]
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr habr)]
  exact h

theorem sectionTwoVariancePartitionNode_le_one (l T : ℝ≥0)
    (hunit : l+T ≤ 1) (N i : ℕ) (hN : 0 < N) (hi : i ≤ N) :
    (l + uniformPartitionTime T N i : ℝ≥0) ≤ 1 := by
  apply le_trans _ hunit
  gcongr
  exact (uniformPartitionTime_mem_Icc_of_le T hN hi).2

/-- The L² difference of the genuine physical and clock sums on one
cropped interval. Out-of-range terms are zero solely to make this finite
sum total; every term of the actual partition uses the literal coefficient. -/
def sectionTwoPhysicalHessianPartitionErrorLp (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) (l T : ℝ≥0) (hunit : l+T ≤ 1) (j : ℕ) :
    Lp ℝ 2 canonicalBrownianMeasure := by
  classical
  exact ∑ i ∈ Finset.range (j+1),
    if hi : i < j+1 then
      sectionTwoPhysicalHessianCellErrorLp Ξ μ
        (l+uniformPartitionTime T (j+1) i)
        (l+uniformPartitionTime T (j+1) (i+1))
        (by exact_mod_cast (sectionTwoVariancePartitionNode_le_one l T hunit
          (j+1) i (Nat.succ_pos j) hi.le))
    else 0

theorem sectionTwoPhysicalHessianPartitionErrorLp_norm_le
    (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) (l T : ℝ≥0)
    (hunit : l+T ≤ 1) (j : ℕ) :
    ‖sectionTwoPhysicalHessianPartitionErrorLp Ξ μ l T hunit j‖ ≤
      Real.sqrt (Ξ.second 1) * Real.sqrt (sectionTwoPhysicalPartitionMesh Ξ l T j) := by
  unfold sectionTwoPhysicalHessianPartitionErrorLp
  apply physicalHessianPartition_norm_le_endpoint Ξ
    (sectionTwoPhysicalPartitionNode Ξ l T (j+1)) (j+1)
    (sectionTwoPhysicalPartitionMesh Ξ l T j)
  · exact sectionTwoPhysicalTimeAtVarianceTime_le_one Ξ _
  · intro i hi
    rw [dite_eq_left hi]
    let u := l + uniformPartitionTime T (j+1) i
    let v := l + uniformPartitionTime T (j+1) (i+1)
    have hu : (u : ℝ) ≤ 1 := by
      exact_mod_cast (sectionTwoVariancePartitionNode_le_one l T hunit
        (j+1) i (Nat.succ_pos j) hi.le)
    have huv : u ≤ v := by
      simpa only [u, v, add_comm] using add_le_add_left
        (monotone_uniformPartitionTime_general T (j+1) (Nat.le_succ i)) l
    change ‖sectionTwoPhysicalHessianCellErrorLp Ξ μ u v hu‖ ≤
      (physicalVolatility Ξ (sectionTwoPhysicalTimeAtVarianceTime Ξ v) -
        physicalVolatility Ξ (sectionTwoPhysicalTimeAtVarianceTime Ξ u)) *
        Real.sqrt (sectionTwoPhysicalPartitionMesh Ξ l T j)
    refine (sectionTwoPhysicalHessianCellErrorLp_norm_le Ξ μ u v hu huv).trans ?_
    apply mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (sectionTwoPhysicalPartition_gap_le_mesh Ξ l T j i hi))
    exact sub_nonneg.mpr (physicalVolatility_monotone Ξ (by
      apply NNReal.coe_le_coe.mp
      rw [sectionTwoPhysicalTimeAtVarianceTime_coe, sectionTwoPhysicalTimeAtVarianceTime_coe]
      exact monotone_sectionTwoPhysicalOverlapAtTime Ξ huv))

theorem sectionTwoPhysicalHessianPartitionErrorLp_tendsto
    (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) (l T : ℝ≥0)
    (hunit : l+T ≤ 1) :
    Tendsto (sectionTwoPhysicalHessianPartitionErrorLp Ξ μ l T hunit) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (sectionTwoPhysicalHessianPartitionErrorLp_norm_le Ξ μ l T hunit)
  have h := (sectionTwoPhysicalPartitionMesh_tendsto Ξ l T).sqrt
  simpa only [Real.sqrt_zero, mul_zero] using h.const_mul (Real.sqrt (Ξ.second 1))

/-- The difference of literal physical Brownian and clock left sums on
one normalized-time interval. This expression contains no proposed limit. -/
def sectionTwoPhysicalHessianPartitionDifference (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) (l T : ℝ≥0) (j : ℕ) (sample : BrownianSample) : ℝ :=
  (∑ i ∈ Finset.range (j+1),
    let u := l+uniformPartitionTime T (j+1) i
    let v := l+uniformPartitionTime T (j+1) (i+1)
    sectionTwoPhysicalHessianAtVarianceTime Ξ μ u sample *
      physicalVolatility Ξ (sectionTwoPhysicalTimeAtVarianceTime Ξ u) *
      (sectionTwoPhysicalBrownian Ξ (sectionTwoPhysicalTimeAtVarianceTime Ξ v) sample -
        sectionTwoPhysicalBrownian Ξ (sectionTwoPhysicalTimeAtVarianceTime Ξ u) sample)) -
  (∑ i ∈ Finset.range (j+1),
    let u := l+uniformPartitionTime T (j+1) i
    let v := l+uniformPartitionTime T (j+1) (i+1)
    sectionTwoPhysicalHessianAtVarianceTime Ξ μ u sample * 1 *
      (sectionTwoExtendedClockDriver Ξ (sectionTwoPhysicalTimeAtVarianceTime Ξ v) sample -
        sectionTwoExtendedClockDriver Ξ (sectionTwoPhysicalTimeAtVarianceTime Ξ u) sample))

theorem sectionTwoPhysicalHessianPartitionErrorLp_coe_ae
    (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) (l T : ℝ≥0)
    (hunit : l+T ≤ 1) (j : ℕ) :
    (sectionTwoPhysicalHessianPartitionErrorLp Ξ μ l T hunit j : BrownianSample → ℝ)
      =ᵐ[canonicalBrownianMeasure]
        sectionTwoPhysicalHessianPartitionDifference Ξ μ l T j := by
  classical
  unfold sectionTwoPhysicalHessianPartitionErrorLp
  refine (Lp.coeFn_finsetSum _ _).trans ?_
  have hterms : ∀ i ∈ Finset.range (j+1),
      ((if hi : i < j+1 then
        sectionTwoPhysicalHessianCellErrorLp Ξ μ
          (l+uniformPartitionTime T (j+1) i)
          (l+uniformPartitionTime T (j+1) (i+1))
          (by exact_mod_cast (sectionTwoVariancePartitionNode_le_one l T hunit
            (j+1) i (Nat.succ_pos j) hi.le))
        else 0 : Lp ℝ 2 canonicalBrownianMeasure) : BrownianSample → ℝ)
      =ᵐ[canonicalBrownianMeasure] fun sample =>
      sectionTwoPhysicalHessianAtVarianceTime Ξ μ (l+uniformPartitionTime T (j+1) i) sample *
        physicalVolatility Ξ (sectionTwoPhysicalTimeAtVarianceTime Ξ
          (l+uniformPartitionTime T (j+1) i)) *
        (sectionTwoPhysicalBrownian Ξ (sectionTwoPhysicalTimeAtVarianceTime Ξ
          (l+uniformPartitionTime T (j+1) (i+1))) sample -
         sectionTwoPhysicalBrownian Ξ (sectionTwoPhysicalTimeAtVarianceTime Ξ
          (l+uniformPartitionTime T (j+1) i)) sample) -
      sectionTwoPhysicalHessianAtVarianceTime Ξ μ (l+uniformPartitionTime T (j+1) i) sample * 1 *
        (sectionTwoExtendedClockDriver Ξ (sectionTwoPhysicalTimeAtVarianceTime Ξ
          (l+uniformPartitionTime T (j+1) (i+1))) sample -
         sectionTwoExtendedClockDriver Ξ (sectionTwoPhysicalTimeAtVarianceTime Ξ
          (l+uniformPartitionTime T (j+1) i)) sample) := by
    intro i hi
    have hN : i < j+1 := Finset.mem_range.mp hi
    simp only [dite_eq_left hN]
    exact sectionTwoPhysicalHessianCellErrorLp_coe_ae Ξ μ _ _ _
      (by exact_mod_cast (sectionTwoVariancePartitionNode_le_one l T hunit
        (j+1) (i+1) (Nat.succ_pos j) (by omega)))
  have hh := eventuallyEq_sum hterms
  refine hh.trans (Filter.Eventually.of_forall ?_)
  intro sample
  simp only [Finset.sum_apply, sectionTwoPhysicalHessianPartitionDifference,
    Finset.sum_sub_distrib]


theorem sectionTwoPhysicalHessianPartitionDifference_tendsto
    (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) (l T : ℝ≥0)
    (hunit : l+T ≤ 1) :
    TendstoInMeasure canonicalBrownianMeasure
      (sectionTwoPhysicalHessianPartitionDifference Ξ μ l T) atTop (fun _ => 0) := by
  have h := tendstoInMeasure_of_tendsto_Lp
    (sectionTwoPhysicalHessianPartitionErrorLp_tendsto Ξ μ l T hunit)
  apply h.congr (fun j => sectionTwoPhysicalHessianPartitionErrorLp_coe_ae
    Ξ μ l T hunit j)
  exact Lp.coeFn_zero _ _ _

end GeneralDepthPaper
