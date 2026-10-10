module

public import DepthPaper.RevisedAppendixACoordinates

@[expose] public section

/-! Literal finite differentiability on a closed parameter domain: the
actual derivatives in its interior extend continuously to its boundary.
No smooth ambient extension or extra derivative order is assumed. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
namespace DepthPaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64
universe u
variable {E F G : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

structure RevisedClosedCData (ell : ℕ) (D : Set E) (f : E → F) where
  jets : E → FormalMultilinearSeries ℝ E F
  continuous_value : ContinuousOn f D
  smooth_interior : ContDiffOn ℝ ell f (interior D)
  continuous_jets : ∀ j ≤ ell, ContinuousOn (fun x => jets x j) D
  zero : ∀ x ∈ D, jets x 0 = iteratedFDeriv ℝ 0 f x
  actual_interior : ∀ j ≤ ell, ∀ x ∈ interior D, jets x j = iteratedFDeriv ℝ j f x

/-- Extending the actual composed interior derivatives through the
Faà di Bruno formula is continuous on the closed domain. -/
def RevisedClosedCData.comp {ell : ℕ} {D : Set E} {f : E → F}
    (h : RevisedClosedCData ell D f) (H : F → G)
    (hH : ∀ x ∈ D, ContDiffAt ℝ ∞ H (f x)) : RevisedClosedCData ell D (H ∘ f) := by
  let J : E → FormalMultilinearSeries ℝ E G := fun x =>
    (ftaylorSeries ℝ H (f x)).taylorComp (h.jets x)
  have hj (j : ℕ) (hj : j ≤ ell) : ContinuousOn (fun x => J x j) D := by
    apply continuousOn_finset_sum
    intro c _
    let B := c.compAlongOrderedFinpartitionL ℝ E F G
    change ContinuousOn (fun x => B (iteratedFDeriv ℝ c.length H (f x))
      (fun i => h.jets x (c.partSize i))) D
    change ContinuousOn ((fun p => B p.1 p.2) ∘ (fun x =>
      (iteratedFDeriv ℝ c.length H (f x),fun i => h.jets x (c.partSize i)))) D
    apply B.continuous_uncurry_of_multilinear.comp_continuousOn
    apply ContinuousOn.prodMk
    · intro x hx
      exact ((hH x hx).continuousAt_iteratedFDeriv (by simp)).comp_continuousWithinAt
        (h.continuous_value x hx)
    · exact continuousOn_pi.mpr (fun i => h.continuous_jets _ ((c.partSize_le i).trans hj))
  have he (j : ℕ) (hj : j ≤ ell) (x : E) (hx : x ∈ interior D) :
      J x j=iteratedFDeriv ℝ j (H ∘ f) x := by
    have hf := h.smooth_interior.contDiffAt (isOpen_interior.mem_nhds hx)
    rw [iteratedFDeriv_comp ((hH x (interior_subset hx)).of_le (by simp)) hf
      (by exact_mod_cast hj)]
    unfold J FormalMultilinearSeries.taylorComp
    apply Finset.sum_congr rfl
    intro c _
    unfold FormalMultilinearSeries.compAlongOrderedFinpartition
    congr 1
    funext i
    exact h.actual_interior _ ((c.partSize_le i).trans hj) x hx
  refine ⟨J,?_,?_,hj,?_,he⟩
  · intro x hx
    exact (hH x hx).continuousAt.comp_continuousWithinAt (h.continuous_value x hx)
  · intro x hx
    exact ((hH x (interior_subset hx)).of_le (by simp)).comp_contDiffWithinAt x
      (h.smooth_interior x hx)
  · intro x hx
    ext v
    simp [J,FormalMultilinearSeries.taylorComp,
      FormalMultilinearSeries.compAlongOrderedFinpartition,
      OrderedFinpartition.compAlongOrderFinpartition_apply,
      ftaylorSeries,iteratedFDeriv_zero_apply,OrderedFinpartition.atomic]

end DepthPaper
