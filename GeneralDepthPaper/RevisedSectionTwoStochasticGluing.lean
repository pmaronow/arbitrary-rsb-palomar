module

public import GeneralDepthPaper.RevisedSectionTwoStochasticLimits
public import Paper.ParisiSchemeMeasure
public import FRSB.FiniteSchemeRepresentation
public import GeneralDepthPaper.RevisedSectionTwoStochasticPaths

@[expose] public section

/-! Finite-cell construction of the actual Hessian stochastic integral.
Each cell is cropped away from the CDF jumps. Mesh size tends to zero
first, and the crop then tends to zero. All limits are in probability. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus Paper
open scoped Topology NNReal ENNReal
namespace GeneralDepthPaper
open SpinGlass.Targets
set_option maxHeartbeats 1000000

def stochasticClippedNode {k : ℕ} (s : RSBScheme k) (t : ℝ≥0) (i : ℕ) : ℝ :=
  min (t:ℝ) (s.q i)

def stochasticCropLeft (a b : ℝ) (n : ℕ) : ℝ := a+(b-a)/((n:ℝ)+3)
def stochasticCropRight (a b : ℝ) (n : ℕ) : ℝ := b-(b-a)/((n:ℝ)+3)

theorem stochasticCrop_bounds {a b : ℝ} (ha : 0 ≤ a) (hab : a<b) (n : ℕ) :
    0 ≤ stochasticCropLeft a b n ∧
    a<stochasticCropLeft a b n ∧
    stochasticCropLeft a b n ≤ stochasticCropRight a b n ∧
    stochasticCropRight a b n<b := by
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  have hden : 0<(n:ℝ)+3 := by positivity
  have hd : 0<(b-a)/((n:ℝ)+3) := div_pos (sub_pos.mpr hab) hden
  have he : (b-a)/((n:ℝ)+3)*((n:ℝ)+3)=b-a := div_mul_cancel₀ _ hden.ne'
  have hmul : 0 ≤ (b-a)/((n:ℝ)+3)*(n:ℝ) := mul_nonneg hd.le hn
  dsimp only [stochasticCropLeft,stochasticCropRight]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> nlinarith

theorem stochasticCropLeft_tendsto (a b : ℝ) :
    Tendsto (stochasticCropLeft a b) atTop (𝓝 a) := by
  change Tendsto (fun n:ℕ => a+(b-a)/((n:ℝ)+3)) atTop (𝓝 a)
  have hd : Tendsto (fun n:ℕ => (b-a)/((n:ℝ)+3)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 3 tendsto_natCast_atTop_atTop)
  simpa only [add_zero] using tendsto_const_nhds.add hd

theorem stochasticCropRight_tendsto (a b : ℝ) :
    Tendsto (stochasticCropRight a b) atTop (𝓝 b) := by
  change Tendsto (fun n:ℕ => b-(b-a)/((n:ℝ)+3)) atTop (𝓝 b)
  have hd : Tendsto (fun n:ℕ => (b-a)/((n:ℝ)+3)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 3 tendsto_natCast_atTop_atTop)
  simpa only [sub_zero] using tendsto_const_nhds.sub hd

/-- The actual Hessian left sums on one cropped constant-CDF cell. The
zero branch covers every empty cell, including repeated scheme nodes. -/
def finiteSchemeHessianCellLeftSums (β h : ℝ) (hβ : β≠0)
    {k : ℕ} (s : RSBScheme k) (t : ℝ≥0) (n i j : ℕ) (sample : Paper.BrownianSample) : ℝ := by
  classical
  let a:=stochasticClippedNode s t i
  let b:=stochasticClippedNode s t (i+1)
  let l:=(stochasticCropLeft a b n).toNNReal
  let r:=(stochasticCropRight a b n).toNNReal
  exact if a<b then
    uniformAdaptedMartingaleLeftSumProcess (canonicalDiracShiftMartingale β l)
      (fun v sample => Paper.parisiHessian β (Paper.parisiSchemeMeasure s)
        ((l:ℝ)+v,Paper.selectedParisiItoState β h hβ (Paper.parisiSchemeMeasure s) (l+v) sample))
      (r-l) (j+1) (r-l) sample else 0

def finiteSchemeHessianCellIncrement (β h : ℝ) (hβ : β≠0)
    {k : ℕ} (s : RSBScheme k) (t : ℝ≥0) (n i : ℕ) (sample : Paper.BrownianSample) : ℝ := by
  classical
  let a:=stochasticClippedNode s t i
  let b:=stochasticClippedNode s t (i+1)
  exact if a<b then
    Paper.selectedParisiGradientProcess β h hβ (Paper.parisiSchemeMeasure s)
      (stochasticCropRight a b n).toNNReal sample-
    Paper.selectedParisiGradientProcess β h hβ (Paper.parisiSchemeMeasure s)
      (stochasticCropLeft a b n).toNNReal sample else 0

theorem finiteSchemeHessianCellLeftSums_tendsto
    (β h : ℝ) (hβ : β≠0) {k : ℕ} (s : RSBScheme k)
    (t : ℝ≥0) (_ht : (t:ℝ) ≤ 1) (n i : ℕ) (hi : i ≤ k+1) :
    TendstoInMeasure Paper.canonicalBrownianMeasure
      (fun j => finiteSchemeHessianCellLeftSums β h hβ s t n i j) atTop
      (finiteSchemeHessianCellIncrement β h hβ s t n i) := by
  let a:=stochasticClippedNode s t i
  let b:=stochasticClippedNode s t (i+1)
  have ha : 0 ≤ a := le_min t.property (s.q_nonneg (by omega))
  by_cases hab : a<b
  · have haeq : a=s.q i := by
      dsimp only [a,b,stochasticClippedNode,a,b] at hab ⊢
      by_cases hqi : (t:ℝ) ≤ s.q i
      · rw [min_eq_left hqi] at hab
        exact False.elim (not_lt_of_ge (min_le_left _ _) hab)
      · exact min_eq_right (le_of_not_ge hqi)
    have hb : b ≤ s.q (i+1) := min_le_right _ _
    have hsab : s.q i<s.q (i+1) := haeq ▸ hab.trans_le hb
    obtain ⟨hl0,hl,hlr,hr⟩:=stochasticCrop_bounds ha hab n
    have hr0 : 0 ≤ stochasticCropRight a b n := hl0.trans hlr
    let l:=(stochasticCropLeft a b n).toNNReal
    let r:=(stochasticCropRight a b n).toNNReal
    have hle : (l:ℝ)=stochasticCropLeft a b n := Real.coe_toNNReal _ hl0
    have hre : (r:ℝ)=stochasticCropRight a b n := Real.coe_toNNReal _ hr0
    have hconv:=actualGradient_stochastic_cell_interior β h hβ
      (Paper.parisiSchemeMeasure s) (s.q_nonneg (by omega)) hsab
      (s.q_le_one (by omega)) (fun v hv=>Paper.parisiCDF_scheme_cell s hi hv)
      l r (by simpa only [hle,←haeq] using hl)
      (by exact_mod_cast (show (l:ℝ) ≤ (r:ℝ) by simpa only [hle,hre] using hlr))
      (by rw [hre];exact hr.trans_le hb)
    change TendstoInMeasure Paper.canonicalBrownianMeasure
      (fun j sample => if a<b then
        uniformAdaptedMartingaleLeftSumProcess (canonicalDiracShiftMartingale β l)
          (fun v sample => Paper.parisiHessian β (Paper.parisiSchemeMeasure s)
            ((l:ℝ)+v,Paper.selectedParisiItoState β h hβ (Paper.parisiSchemeMeasure s) (l+v) sample))
          (r-l) (j+1) (r-l) sample else 0) atTop
      (fun sample => if a<b then
        Paper.selectedParisiGradientProcess β h hβ (Paper.parisiSchemeMeasure s) r sample-
          Paper.selectedParisiGradientProcess β h hβ (Paper.parisiSchemeMeasure s) l sample else 0)
    simp only [ite_eq_left hab]
    exact hconv
  · have hz (j:ℕ) : finiteSchemeHessianCellLeftSums β h hβ s t n i j=fun _=>0 := by
      funext sample
      change (if a<b then _ else 0)=0
      rw [ite_eq_right hab]
    have hzi : finiteSchemeHessianCellIncrement β h hβ s t n i=fun _=>0 := by
      funext sample
      change (if a<b then _ else 0)=0
      rw [ite_eq_right hab]
    simp only [hz,hzi]
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    simpa only [dist_self,not_le.mpr hε,Set.ofPred_false,measure_empty]
      using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ≥0∞)) atTop (𝓝 0))

/-- Removing the crop yields the actual gradient increment between the
closed endpoints of the cell, even when an endpoint carries an atom. -/
theorem finiteSchemeHessianCellIncrement_tendsto
    (β h : ℝ) (hβ : β≠0) {k : ℕ} (s : RSBScheme k)
    (t : ℝ≥0) (i : ℕ) (hi : i ≤ k+1) :
    TendstoInMeasure Paper.canonicalBrownianMeasure
      (fun n => finiteSchemeHessianCellIncrement β h hβ s t n i) atTop
      (fun sample =>
        Paper.selectedParisiGradientProcess β h hβ (Paper.parisiSchemeMeasure s)
          (stochasticClippedNode s t (i+1)).toNNReal sample-
        Paper.selectedParisiGradientProcess β h hβ (Paper.parisiSchemeMeasure s)
          (stochasticClippedNode s t i).toNNReal sample) := by
  let a:=stochasticClippedNode s t i
  let b:=stochasticClippedNode s t (i+1)
  have hab_le : a ≤ b := min_le_min le_rfl (s.q_mono i hi)
  by_cases hab : a<b
  · apply tendstoInMeasure_of_tendsto_ae
    · intro n
      change AEStronglyMeasurable
        (fun sample => if a<b then
          Paper.selectedParisiGradientProcess β h hβ (Paper.parisiSchemeMeasure s)
            (stochasticCropRight a b n).toNNReal sample-
          Paper.selectedParisiGradientProcess β h hβ (Paper.parisiSchemeMeasure s)
            (stochasticCropLeft a b n).toNNReal sample else 0) _
      simp only [ite_eq_left hab]
      exact (Paper.measurable_selectedParisiGradientProcess_fixed _ _ _ _ _).aestronglyMeasurable.sub
        (Paper.measurable_selectedParisiGradientProcess_fixed _ _ _ _ _).aestronglyMeasurable
    · exact .of_forall fun sample => by
        change Tendsto (fun n => if a<b then
          Paper.selectedParisiGradientProcess β h hβ (Paper.parisiSchemeMeasure s)
            (stochasticCropRight a b n).toNNReal sample-
          Paper.selectedParisiGradientProcess β h hβ (Paper.parisiSchemeMeasure s)
            (stochasticCropLeft a b n).toNNReal sample else 0) atTop _
        simp only [ite_eq_left hab]
        have hc:=Paper.continuous_selectedParisiGradientProcess_path β h hβ
          (Paper.parisiSchemeMeasure s) sample
        exact (hc.tendsto _ |>.comp (continuous_real_toNNReal.tendsto b |>.comp
          (stochasticCropRight_tendsto a b))).sub
          (hc.tendsto _ |>.comp (continuous_real_toNNReal.tendsto a |>.comp
            (stochasticCropLeft_tendsto a b)))
  · have he : a=b := le_antisymm hab_le (le_of_not_gt hab)
    have hz (n:ℕ) : finiteSchemeHessianCellIncrement β h hβ s t n i=fun _=>0 := by
      funext sample
      change (if a<b then _ else 0)=0
      rw [ite_eq_right hab]
    change TendstoInMeasure _ (fun n => finiteSchemeHessianCellIncrement β h hβ s t n i) atTop
      (fun sample => Paper.selectedParisiGradientProcess β h hβ (Paper.parisiSchemeMeasure s)
        b.toNNReal sample-Paper.selectedParisiGradientProcess β h hβ
        (Paper.parisiSchemeMeasure s) a.toNNReal sample)
    simp only [hz,he,sub_self]
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    simpa only [dist_self,not_le.mpr hε,Set.ofPred_false,measure_empty]
      using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ≥0∞)) atTop (𝓝 0))

def finiteSchemeHessianLeftSums (β h : ℝ) (hβ : β≠0)
    {k : ℕ} (s : RSBScheme k) (t : ℝ≥0) (n j : ℕ) (sample : Paper.BrownianSample) : ℝ :=
  ∑ i ∈ Finset.range (k+2), finiteSchemeHessianCellLeftSums β h hβ s t n i j sample

def finiteSchemeHessianInnerLimit (β h : ℝ) (hβ : β≠0)
    {k : ℕ} (s : RSBScheme k) (t : ℝ≥0) (n : ℕ) : Paper.BrownianSample → ℝ :=
  stochasticProbabilityLimit Paper.canonicalBrownianMeasure
    (fun j => finiteSchemeHessianLeftSums β h hβ s t n j)

/-- The Hessian stochastic integral is constructed from the genuine
Hessian/Brownian left sums by mesh and endpoint limits, in that order. -/
def finiteSchemeHessianStochasticIntegral (β h : ℝ) (hβ : β≠0)
    {k : ℕ} (s : RSBScheme k) (t : ℝ≥0) : Paper.BrownianSample → ℝ :=
  stochasticProbabilityLimit Paper.canonicalBrownianMeasure
    (fun n => finiteSchemeHessianInnerLimit β h hβ s t n)

theorem finiteSchemeHessianLeftSums_tendsto
    (β h : ℝ) (hβ : β≠0) {k : ℕ} (s : RSBScheme k)
    (t : ℝ≥0) (ht : (t:ℝ) ≤ 1) (n : ℕ) :
    TendstoInMeasure Paper.canonicalBrownianMeasure
      (fun j => finiteSchemeHessianLeftSums β h hβ s t n j) atTop
      (fun sample => ∑ i ∈ Finset.range (k+2),
        finiteSchemeHessianCellIncrement β h hβ s t n i sample) :=
  tendstoInMeasure_finset_sum _ _ _ (fun i hi =>
    finiteSchemeHessianCellLeftSums_tendsto β h hβ s t ht n i (by
      have := Finset.mem_range.mp hi
      omega))

theorem finiteSchemeHessianInnerLimit_eq
    (β h : ℝ) (hβ : β≠0) {k : ℕ} (s : RSBScheme k)
    (t : ℝ≥0) (ht : (t:ℝ) ≤ 1) (n : ℕ) :
    finiteSchemeHessianInnerLimit β h hβ s t n =ᵐ[Paper.canonicalBrownianMeasure]
      (fun sample => ∑ i ∈ Finset.range (k+2),
        finiteSchemeHessianCellIncrement β h hβ s t n i sample) :=
  stochasticProbabilityLimit_eq (finiteSchemeHessianLeftSums_tendsto β h hβ s t ht n)

theorem finiteSchemeHessianInnerLimit_tendsto
    (β h : ℝ) (hβ : β≠0) {k : ℕ} (s : RSBScheme k)
    (t : ℝ≥0) (ht : (t:ℝ) ≤ 1) :
    TendstoInMeasure Paper.canonicalBrownianMeasure
      (fun n => finiteSchemeHessianInnerLimit β h hβ s t n) atTop
      (fun sample => Paper.selectedParisiGradientProcess β h hβ (Paper.parisiSchemeMeasure s) t sample-
        Paper.selectedParisiGradientProcess β h hβ (Paper.parisiSchemeMeasure s) 0 sample) := by
  have hc:=tendstoInMeasure_finset_sum (Finset.range (k+2))
    (fun i n => finiteSchemeHessianCellIncrement β h hβ s t n i)
    (fun i sample =>
      Paper.selectedParisiGradientProcess β h hβ (Paper.parisiSchemeMeasure s)
        (stochasticClippedNode s t (i+1)).toNNReal sample-
      Paper.selectedParisiGradientProcess β h hβ (Paper.parisiSchemeMeasure s)
        (stochasticClippedNode s t i).toNNReal sample)
    (fun i hi => finiteSchemeHessianCellIncrement_tendsto β h hβ s t i (by
      have:=Finset.mem_range.mp hi
      omega))
  have he (sample:Paper.BrownianSample) :
      (∑ i ∈ Finset.range (k+2),
        (Paper.selectedParisiGradientProcess β h hβ (Paper.parisiSchemeMeasure s)
          (stochasticClippedNode s t (i+1)).toNNReal sample-
        Paper.selectedParisiGradientProcess β h hβ (Paper.parisiSchemeMeasure s)
          (stochasticClippedNode s t i).toNNReal sample))=
      Paper.selectedParisiGradientProcess β h hβ (Paper.parisiSchemeMeasure s) t sample-
        Paper.selectedParisiGradientProcess β h hβ (Paper.parisiSchemeMeasure s) 0 sample := by
    rw [Finset.sum_range_sub (fun i => Paper.selectedParisiGradientProcess β h hβ
      (Paper.parisiSchemeMeasure s) (stochasticClippedNode s t i).toNNReal sample)]
    simp only [stochasticClippedNode,s.q_top,s.q_zero,min_eq_left ht]
    rw [min_eq_right (show (0:ℝ) ≤ (t:ℝ) from t.property),Real.toNNReal_coe,
      Real.toNNReal_zero]
  have hc':=hc.congr_right (.of_forall he)
  exact hc'.congr_left (fun n => (finiteSchemeHessianInnerLimit_eq β h hβ s t ht n).symm)

/-- The constructed stochastic integral equals the actual gradient
increment almost surely; its value was not supplied to the construction. -/
theorem finiteSchemeHessianStochasticIntegral_eq
    (β h : ℝ) (hβ : β≠0) {k : ℕ} (s : RSBScheme k)
    (t : ℝ≥0) (ht : (t:ℝ) ≤ 1) :
    finiteSchemeHessianStochasticIntegral β h hβ s t =ᵐ[Paper.canonicalBrownianMeasure]
      (fun sample => Paper.selectedParisiGradientProcess β h hβ (Paper.parisiSchemeMeasure s) t sample-
        Paper.selectedParisiGradientProcess β h hβ (Paper.parisiSchemeMeasure s) 0 sample) :=
  stochasticProbabilityLimit_eq (finiteSchemeHessianInnerLimit_tendsto β h hβ s t ht)

end GeneralDepthPaper
