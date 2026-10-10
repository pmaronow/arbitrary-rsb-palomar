module

public import GeneralDepthPaper.RevisedSectionTwoPhysicalClockInverse
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

/-! Concrete physical-time Hessian sums on the actual diffusion. The
partition is obtained by applying the inverse covariance clock to the
existing normalized-time cell partition. The Brownian input is explicit;
its independent construction and Brownian law belong to the physical
driver module. None of these definitions refers to a proposed integral
value or gradient increment. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus Paper
open scoped Topology NNReal ENNReal

namespace GeneralDepthPaper
open FourPapersCommon SpinGlass.Targets
set_option maxHeartbeats 1000000

/-- The actual spatial Hessian along the actual diffusion, read at the
physical time corresponding to a normalized-time partition node. -/
def sectionTwoPhysicalHessianAtVarianceTime (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) (v : ℝ≥0) (sample : BrownianSample) : ℝ :=
  hessian Ξ μ (sectionTwoPhysicalOverlapAtTime Ξ v)
    (optimalState Ξ μ sample (sectionTwoPhysicalOverlapAtTime Ξ v))

theorem sectionTwoPhysicalHessianAtVarianceTime_eq_normalized
    (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) (v : ℝ≥0)
    (hv : (v : ℝ) ≤ 1) (sample : BrownianSample) :
    sectionTwoPhysicalHessianAtVarianceTime Ξ μ v sample =
      sectionTwoVarianceHessian Ξ μ v sample := by
  let w : Overlap := ⟨v, v.property, hv⟩
  have he : sectionTwoClampedVarianceOverlap v = w := by
    apply Subtype.ext
    change max 0 (min 1 (v : ℝ)) = (v : ℝ)
    rw [min_eq_right hv]
    exact max_eq_right v.coe_nonneg
  have hh := sectionTwoVarianceHessian_eq_physical Ξ μ w sample
  simp only [w, Real.toNNReal_coe] at hh
  rw [sectionTwoPhysicalHessianAtVarianceTime, sectionTwoPhysicalOverlapAtTime, he]
  exact hh.symm

theorem norm_sectionTwoPhysicalHessianAtVarianceTime_le_one
    (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) (v : ℝ≥0)
    (sample : BrownianSample) :
    ‖sectionTwoPhysicalHessianAtVarianceTime Ξ μ v sample‖ ≤ 1 :=
  Paper.norm_parisiHessian_le_one_all _ _ _

theorem sectionTwoExtendedClockDriver_physicalTime_eq
    (Ξ : AdmissibleCovariance) (v : ℝ≥0) (hv : (v : ℝ) ≤ 1)
    (sample : BrownianSample) :
    sectionTwoExtendedClockDriver Ξ (sectionTwoPhysicalTimeAtVarianceTime Ξ v) sample =
      mixedBeta Ξ.toEvenMixture * canonicalBrownian v sample := by
  rw [sectionTwoExtendedClockDriver, sectionTwoExtendedBrownianClock,
    sectionTwoPhysicalTimeAtVarianceTime_clock Ξ v hv, Real.toNNReal_coe]

/-- Inverse-clock image of a uniform normalized-time partition node. -/
def sectionTwoPhysicalPartitionNode (Ξ : AdmissibleCovariance)
    (l T : ℝ≥0) (N i : ℕ) : ℝ≥0 :=
  sectionTwoPhysicalTimeAtVarianceTime Ξ (l + uniformPartitionTime T N i)

/-- The actual largest physical-time gap in the nonempty partition. -/
def sectionTwoPhysicalPartitionMesh (Ξ : AdmissibleCovariance)
    (l T : ℝ≥0) (j : ℕ) : ℝ :=
  (Finset.range (j+1)).sup' Finset.nonempty_range_add_one
    (fun i => dist (sectionTwoPhysicalPartitionNode Ξ l T (j+1) i)
      (sectionTwoPhysicalPartitionNode Ξ l T (j+1) (i+1)))

theorem sectionTwoPhysicalPartitionMesh_nonneg (Ξ : AdmissibleCovariance)
    (l T : ℝ≥0) (j : ℕ) : 0 ≤ sectionTwoPhysicalPartitionMesh Ξ l T j := by
  apply (dist_nonneg : 0 ≤ dist (sectionTwoPhysicalPartitionNode Ξ l T (j+1) 0)
    (sectionTwoPhysicalPartitionNode Ξ l T (j+1) 1)).trans
  unfold sectionTwoPhysicalPartitionMesh
  exact Finset.le_sup' (fun i => dist (sectionTwoPhysicalPartitionNode Ξ l T (j+1) i)
    (sectionTwoPhysicalPartitionNode Ξ l T (j+1) (i+1)))
    (Finset.mem_range.mpr (Nat.succ_pos j))

theorem sectionTwoPhysicalPartition_gap_le_mesh (Ξ : AdmissibleCovariance)
    (l T : ℝ≥0) (j i : ℕ) (hi : i < j+1) :
    dist (sectionTwoPhysicalPartitionNode Ξ l T (j+1) i)
      (sectionTwoPhysicalPartitionNode Ξ l T (j+1) (i+1)) ≤
        sectionTwoPhysicalPartitionMesh Ξ l T j :=
    by
  unfold sectionTwoPhysicalPartitionMesh
  exact Finset.le_sup' (fun z => dist (sectionTwoPhysicalPartitionNode Ξ l T (j+1) z)
    (sectionTwoPhysicalPartitionNode Ξ l T (j+1) (z+1))) (Finset.mem_range.mpr hi)

theorem sectionTwoPhysicalPartitionMesh_tendsto (Ξ : AdmissibleCovariance)
    (l T : ℝ≥0) :
    Tendsto (sectionTwoPhysicalPartitionMesh Ξ l T) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.mp
    (uniformContinuous_sectionTwoPhysicalTimeAtVarianceTime Ξ) ε hε
  have hratio : Tendsto (fun j : ℕ => (T : ℝ) / ((j : ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hratio.eventually (gt_mem_nhds hδ))
  refine ⟨N, ?_⟩
  intro j hj
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (sectionTwoPhysicalPartitionMesh_nonneg Ξ l T j)]
  unfold sectionTwoPhysicalPartitionMesh
  rw [Finset.sup'_lt_iff]
  intro i _hi
  apply hd
  have he : dist (l + uniformPartitionTime T (j+1) i)
      (l + uniformPartitionTime T (j+1) (i+1)) = (T : ℝ)/((j : ℝ)+1) := by
    change dist ((l : ℝ) + (uniformPartitionTime T (j+1) i : ℝ))
      ((l : ℝ) + (uniformPartitionTime T (j+1) (i+1) : ℝ)) = _
    rw [dist_add_left, dist_comm]
    have hn := congrArg (fun x : ℝ≥0 => (x : ℝ))
      (uniformPartitionTime_succ_nndist T (Nat.succ_pos j) i)
    simpa only [dist_nndist, NNReal.coe_div, NNReal.coe_natCast,
      Nat.cast_add, Nat.cast_succ, Nat.cast_one, NNReal.coe_add, NNReal.coe_one] using hn
  rw [he]
  exact hN j hj

/-- A finite physical-time sum with the actual Hessian, a specified
deterministic coefficient and a specified stochastic driver. This helper
allows a direct comparison of the physical Brownian and clock drivers. -/
def finiteSchemePhysicalHessianCellSum (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) (D : ℝ≥0 → BrownianSample → ℝ) (c : ℝ≥0 → ℝ)
    {k : ℕ} (s : RSBScheme k) (t : ℝ≥0) (n i j : ℕ)
    (sample : BrownianSample) : ℝ := by
  classical
  let a := stochasticClippedNode s t i
  let b := stochasticClippedNode s t (i+1)
  let l := (stochasticCropLeft a b n).toNNReal
  let r := (stochasticCropRight a b n).toNNReal
  exact if a < b then
    ∑ z ∈ Finset.range (j+1),
      let u := l + uniformPartitionTime (r-l) (j+1) z
      let v := l + uniformPartitionTime (r-l) (j+1) (z+1)
      sectionTwoPhysicalHessianAtVarianceTime Ξ μ u sample *
        c (sectionTwoPhysicalTimeAtVarianceTime Ξ u) *
        (D (sectionTwoPhysicalTimeAtVarianceTime Ξ v) sample -
          D (sectionTwoPhysicalTimeAtVarianceTime Ξ u) sample)
    else 0

def finiteSchemePhysicalHessianSum (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) (D : ℝ≥0 → BrownianSample → ℝ) (c : ℝ≥0 → ℝ)
    {k : ℕ} (s : RSBScheme k) (t : ℝ≥0) (n j : ℕ)
    (sample : BrownianSample) : ℝ :=
  ∑ i ∈ Finset.range (k+2), finiteSchemePhysicalHessianCellSum Ξ μ D c s t n i j sample

/-- Literal physical Brownian left sums: the coefficient is precisely
`sqrt (Ξ''(q))` times the actual Hessian at the left physical endpoint. -/
def sectionTwoHessianPhysicalBrownianLeftSums (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) (hμ : (μ : Measure Overlap).support.Finite)
    (B : ℝ≥0 → BrownianSample → ℝ) (q : Overlap) (n j : ℕ) : BrownianSample → ℝ :=
  finiteSchemePhysicalHessianSum Ξ μ B (physicalVolatility Ξ)
    (sectionTwoMixedFiniteScheme Ξ μ hμ) (sectionTwoBrownianTime Ξ q) n j

/-- The comparison sums contain the same actual Hessian and physical
partition, with increments of the actual covariance-clock driver. -/
def sectionTwoHessianPhysicalClockLeftSums (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) (hμ : (μ : Measure Overlap).support.Finite)
    (q : Overlap) (n j : ℕ) : BrownianSample → ℝ :=
  finiteSchemePhysicalHessianSum Ξ μ (sectionTwoExtendedClockDriver Ξ) (fun _ => 1)
    (sectionTwoMixedFiniteScheme Ξ μ hμ) (sectionTwoBrownianTime Ξ q) n j

/-- Limits are constructed from the physical Brownian sums alone. A
separate convergence theorem must identify these with the actual process. -/
def sectionTwoHessianPhysicalBrownianInnerLimit (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) (hμ : (μ : Measure Overlap).support.Finite)
    (B : ℝ≥0 → BrownianSample → ℝ) (q : Overlap) (n : ℕ) : BrownianSample → ℝ :=
  stochasticProbabilityLimit canonicalBrownianMeasure
    (fun j => sectionTwoHessianPhysicalBrownianLeftSums Ξ μ hμ B q n j)

def sectionTwoHessianPhysicalBrownianIntegral (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) (hμ : (μ : Measure Overlap).support.Finite)
    (B : ℝ≥0 → BrownianSample → ℝ) (q : Overlap) : BrownianSample → ℝ :=
  stochasticProbabilityLimit canonicalBrownianMeasure
    (fun n => sectionTwoHessianPhysicalBrownianInnerLimit Ξ μ hμ B q n)

theorem finiteSchemePhysicalHessianCellSum_eq_clock
    (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) {k : ℕ} (s : RSBScheme k)
    (hs : parisiSchemeMeasure s = mixedMeasure Ξ.toEvenMixture μ)
    (t : ℝ≥0) (ht : (t : ℝ) ≤ 1) (n i j : ℕ) (hi : i ≤ k+1)
    (sample : BrownianSample) :
    finiteSchemePhysicalHessianCellSum Ξ μ (sectionTwoExtendedClockDriver Ξ)
      (fun _ => 1) s t n i j sample =
    finiteSchemeHessianCellLeftSums (mixedBeta Ξ.toEvenMixture) 0
      (mixedBeta_ne_zero Ξ.toEvenMixture) s t n i j sample := by
  classical
  let a := stochasticClippedNode s t i
  let b := stochasticClippedNode s t (i+1)
  let l := (stochasticCropLeft a b n).toNNReal
  let r := (stochasticCropRight a b n).toNNReal
  by_cases hab : a < b
  · have ha : 0 ≤ a := le_min t.property (s.q_nonneg (by omega))
    obtain ⟨hl0, _hl, hlr, hr⟩ := stochasticCrop_bounds ha hab n
    have hr0 : 0 ≤ stochasticCropRight a b n := hl0.trans hlr
    have hle : (l : ℝ) = stochasticCropLeft a b n := Real.coe_toNNReal _ hl0
    have hre : (r : ℝ) = stochasticCropRight a b n := Real.coe_toNNReal _ hr0
    have hlrN : l ≤ r := by exact_mod_cast (show (l : ℝ) ≤ (r : ℝ) by rw [hle, hre]; exact hlr)
    have hr1 : (r : ℝ) ≤ 1 := by
      rw [hre]
      exact hr.le.trans ((min_le_left _ _).trans ht)
    have hnode (z : ℕ) (hz : z ≤ j+1) :
        (l + uniformPartitionTime (r-l) (j+1) z : ℝ≥0) ≤ r := by
      calc
        _ ≤ l + (r-l) := by
          gcongr
          exact (uniformPartitionTime_mem_Icc_of_le (r-l) (Nat.succ_pos j) hz).2
        _ = r := add_tsub_cancel_of_le hlrN
    change (if a < b then _ else 0) = (if a < b then _ else 0)
    rw [ite_eq_left hab, ite_eq_left hab, uniformAdaptedMartingaleLeftSumProcess_terminal]
    apply Finset.sum_congr rfl
    intro z hz
    have hzN : z < j+1 := Finset.mem_range.mp hz
    let u := l + uniformPartitionTime (r-l) (j+1) z
    let v := l + uniformPartitionTime (r-l) (j+1) (z+1)
    have hu1 : (u : ℝ) ≤ 1 :=
      (NNReal.coe_le_coe.mpr (hnode z hzN.le)).trans hr1
    have hv1 : (v : ℝ) ≤ 1 :=
      (NNReal.coe_le_coe.mpr (hnode (z+1) (by omega))).trans hr1
    change sectionTwoPhysicalHessianAtVarianceTime Ξ μ u sample * 1 *
      (sectionTwoExtendedClockDriver Ξ (sectionTwoPhysicalTimeAtVarianceTime Ξ v) sample -
        sectionTwoExtendedClockDriver Ξ (sectionTwoPhysicalTimeAtVarianceTime Ξ u) sample) = _
    rw [sectionTwoPhysicalHessianAtVarianceTime_eq_normalized Ξ μ u hu1 sample,
      sectionTwoExtendedClockDriver_physicalTime_eq Ξ v hv1 sample,
      sectionTwoExtendedClockDriver_physicalTime_eq Ξ u hu1 sample]
    simp only [sectionTwoVarianceHessian, hs, canonicalDiracShiftMartingale,
      u, v, NNReal.coe_add, mul_one]
    ring
  · change (if a < b then _ else 0) = (if a < b then _ else 0)
    rw [ite_eq_right hab, ite_eq_right hab]

theorem sectionTwoHessianPhysicalClockLeftSums_eq_clock
    (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (hμ : (μ : Measure Overlap).support.Finite) (q : Overlap) (n j : ℕ) :
    sectionTwoHessianPhysicalClockLeftSums Ξ μ hμ q n j =
      sectionTwoHessianClockLeftSums Ξ μ hμ q n j := by
  funext sample
  unfold sectionTwoHessianPhysicalClockLeftSums sectionTwoHessianClockLeftSums
    finiteSchemePhysicalHessianSum finiteSchemeHessianLeftSums
  apply Finset.sum_congr rfl
  intro i hi
  exact finiteSchemePhysicalHessianCellSum_eq_clock Ξ μ _
    (sectionTwoMixedFiniteScheme_represents Ξ μ hμ) _
    (by rw [sectionTwoBrownianTime, Real.coe_toNNReal _ (Ξ.clock_mem_unit q.property).1]
        exact (Ξ.clock_mem_unit q.property).2) n i j (by
      have := Finset.mem_range.mp hi
      omega) sample

end GeneralDepthPaper
