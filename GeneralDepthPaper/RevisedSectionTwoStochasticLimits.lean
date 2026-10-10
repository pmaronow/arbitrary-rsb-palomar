module

public import GeneralDepthPaper.RevisedSectionTwoStochasticCell
public import Paper.ParisiGradientMartingaleLaw

@[expose] public section

/-! Limits used to construct the Hessian stochastic integral. The chosen
limit depends only on its sequence of genuine stochastic left sums. Its
identification with a gradient increment is a theorem, not a definition. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus Paper
open scoped Topology NNReal ENNReal
namespace GeneralDepthPaper
set_option maxHeartbeats 1000000

/-- A representative of the limit in probability, when this limit exists.
This definition contains no proposed value of the stochastic integral. -/
def stochasticProbabilityLimit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : ℕ → Ω → ℝ) : Ω → ℝ := by
  classical
  exact if h : ∃ g, TendstoInMeasure P f atTop g then Classical.choose h else fun _ => 0

theorem stochasticProbabilityLimit_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {f : ℕ → Ω → ℝ}
    (h : ∃ g, TendstoInMeasure P f atTop g) :
    TendstoInMeasure P f atTop (stochasticProbabilityLimit P f) := by
  rw [stochasticProbabilityLimit, dite_eq_left h]
  exact Classical.choose_spec h

theorem stochasticProbabilityLimit_eq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hg : TendstoInMeasure P f atTop g) :
    stochasticProbabilityLimit P f =ᵐ[P] g :=
  tendstoInMeasure_ae_unique (stochasticProbabilityLimit_tendsto ⟨g,hg⟩) hg

theorem tendstoInMeasure_finset_sum {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (s : Finset ι) (f : ι → ℕ → Ω → ℝ) (g : ι → Ω → ℝ)
    (h : ∀ i ∈ s, TendstoInMeasure P (f i) atTop (g i)) :
    TendstoInMeasure P (fun n sample => ∑ i ∈ s, f i n sample) atTop
      (fun sample => ∑ i ∈ s, g i sample) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    simpa only [dist_self,not_le.mpr hε,Set.ofPred_false,measure_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ≥0∞)) atTop (𝓝 0))
  | @insert i s hi ih =>
    have hadd := (h i (Finset.mem_insert_self i s)).add_real_noMeas
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.sum_insert hi] using hadd

end GeneralDepthPaper
