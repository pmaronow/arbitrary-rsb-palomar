module

public import DepthPaper.RevisedClosedIFTConvention
public import DepthPaper.RevisedClosedIFTSmooth
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-! The revised manuscript's Lemma B.4. The hypotheses use its stated
closed-domain convention: interior derivatives extend continuously to the
boundary. `ClosedInteriorCk` expresses that convention directly, and its
equivalence with `ContDiffOn` on these convex open closures is proved in
`RevisedClosedIFTConvention`.

The proof uses relative derivatives at the boundary and induction, rather
than a Whitney extension. Neither an extension nor the regularity of the
root is assumed. All finite orders, including zero-dimensional Euclidean
spaces and empty parameter domains, are covered. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper.RevisedClosedIFT
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 64
universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Closed-domain implicit function theorem with the paper's closed `C^k`
convention, the actual first derivative, and all differentiated zero
identities. Compactness of the parameter closure is retained to match the
paper, although compactness of the solution set suffices for this proof. -/
theorem closed_domain_implicit_function
    {U : Set E} {V : Set F} {Φ : E×F→F} {y : E→F}
    (hUopen : IsOpen U) (hUconvex : Convex ℝ U) (_hDcompact : IsCompact (closure U))
    (hVopen : IsOpen V) (hVconvex : Convex ℝ V) (hKcompact : IsCompact (closure V))
    (k : ℕ) (hk : 1≤k)
    (hΦ : ClosedInteriorCk k Φ (closure U×ˢclosure V))
    (hzero : ∀θ∈closure U,Φ (θ,y θ)=0)
    (hunique : ∀θ∈closure U,∀z∈closure V,Φ (θ,z)=0 → z=y θ)
    (hyInterior : ∀θ∈closure U,y θ∈interior (closure V))
    (hinv : ∀θ∈closure U,
      (partialY (fderivWithin ℝ Φ (closure U×ˢclosure V) (θ,y θ))).IsInvertible) :
    ClosedInteriorCk k y (closure U) ∧
    (∀θ∈closure U,HasFDerivWithinAt y
      (implicitDerivative (fderivWithin ℝ Φ (closure U×ˢclosure V) (θ,y θ)))
      (closure U) θ) ∧
    (∀j : ℕ,j≤k → ∀θ∈closure U,
      iteratedFDerivWithin ℝ j (fun u=>Φ (u,y u)) (closure U) θ=0) := by
  classical
  by_cases hUne : U.Nonempty
  · have hyK : ∀θ∈closure U,y θ∈closure V :=
      fun θ hθ=>interior_subset (hyInterior θ hθ)
    obtain ⟨θ,hθ⟩ := hUne
    have hVne : V.Nonempty :=
      closure_nonempty_iff.mp ⟨y θ,hyK θ (subset_closure hθ)⟩
    obtain ⟨z,hz⟩ := hVne
    have hD : UniqueDiffOn ℝ (closure U) :=
      uniqueDiffOn_convex hUconvex.closure (by
        exact ⟨θ,interior_mono subset_closure (hUopen.interior_eq.symm ▸ hθ)⟩)
    have hDK : UniqueDiffOn ℝ (closure U×ˢclosure V) := by
      rw [←closure_prod_eq]
      apply uniqueDiffOn_convex (hUconvex.prod hVconvex).closure
      exact ⟨(θ,z),interior_mono subset_closure
        ((hUopen.prod hVopen).interior_eq.symm ▸ (show (θ,z)∈U×ˢV from ⟨hθ,hz⟩))⟩
    have hΦdiff : ContDiffOn ℝ k Φ (closure U×ˢclosure V) := by
      have h := closedInteriorCk_contDiffOn_closure (hUopen.prod hVopen)
        (hUconvex.prod hVconvex) ⟨(θ,z),hθ,hz⟩ k Φ
        (by simpa only [closure_prod_eq] using hΦ)
      simpa only [closure_prod_eq] using h
    have hydiff := contDiffOn_unique_implicit_root hD hDK hKcompact k hΦdiff
      hyK hzero hunique hinv
    refine ⟨contDiffOn_closedInteriorCk hD k y hydiff,?_,?_⟩
    · intro θ hθ
      apply hasFDerivWithinAt_implicit_root hθ hyK (hydiff.continuousOn θ hθ) hzero
      · exact (hΦdiff.differentiableOn (by exact_mod_cast Nat.ne_zero_of_lt hk)
          (θ,y θ) ⟨hθ,hyK θ hθ⟩).hasFDerivWithinAt
      · exact hinv θ hθ
    · intro j _ θ hθ
      calc
        iteratedFDerivWithin ℝ j (fun u=>Φ (u,y u)) (closure U) θ =
            iteratedFDerivWithin ℝ j (fun _ : E=>(0:F)) (closure U) θ :=
          iteratedFDerivWithin_congr hzero hθ j
        _=0 := by simp
  · have hUempty : U=∅ := Set.not_nonempty_iff_eq_empty.mp hUne
    have hDempty : closure U=∅ := by simp [hUempty]
    have hD : UniqueDiffOn ℝ (closure U) := by
      rw [hDempty]
      exact uniqueDiffOn_empty
    refine ⟨contDiffOn_closedInteriorCk hD k y (by simp [hDempty]),?_,?_⟩
    · simp [hDempty]
    · simp [hDempty]

/-- Existence formulation of the same result: the function is selected from
pointwise unique roots, and its regularity is a conclusion. -/
theorem exists_closed_domain_implicit_function
    {U : Set E} {V : Set F} {Φ : E×F→F}
    (hUopen : IsOpen U) (hUconvex : Convex ℝ U) (hDcompact : IsCompact (closure U))
    (hVopen : IsOpen V) (hVconvex : Convex ℝ V) (hKcompact : IsCompact (closure V))
    (k : ℕ) (hk : 1≤k)
    (hΦ : ClosedInteriorCk k Φ (closure U×ˢclosure V))
    (hroots : ∀θ∈closure U,∃! z,z∈closure V ∧ Φ (θ,z)=0)
    (hrootInterior : ∀θ∈closure U,∀z∈closure V,Φ (θ,z)=0 → z∈interior (closure V))
    (hinv : ∀θ∈closure U,∀z∈closure V,Φ (θ,z)=0 →
      (partialY (fderivWithin ℝ Φ (closure U×ˢclosure V) (θ,z))).IsInvertible) :
    ∃y : E→F,
      (∀θ∈closure U,y θ∈interior (closure V) ∧ Φ (θ,y θ)=0) ∧
      ClosedInteriorCk k y (closure U) ∧
      (∀θ∈closure U,HasFDerivWithinAt y
        (implicitDerivative (fderivWithin ℝ Φ (closure U×ˢclosure V) (θ,y θ)))
        (closure U) θ) ∧
      (∀j : ℕ,j≤k → ∀θ∈closure U,
        iteratedFDerivWithin ℝ j (fun u=>Φ (u,y u)) (closure U) θ=0) := by
  classical
  let y : E→F := fun θ=>if hθ : θ∈closure U then Classical.choose (hroots θ hθ) else 0
  have hychoice (θ : E) (hθ : θ∈closure U) : y θ=Classical.choose (hroots θ hθ) := by
    simp only [y,dite_eq_left hθ]
  have hyK (θ : E) (hθ : θ∈closure U) : y θ∈closure V := by
    rw [hychoice θ hθ]
    exact (Classical.choose_spec (hroots θ hθ)).1.1
  have hzero (θ : E) (hθ : θ∈closure U) : Φ (θ,y θ)=0 := by
    rw [hychoice θ hθ]
    exact (Classical.choose_spec (hroots θ hθ)).1.2
  have hunique (θ : E) (hθ : θ∈closure U) (z : F) (hz : z∈closure V)
      (hΦz : Φ (θ,z)=0) : z=y θ := by
    rw [hychoice θ hθ]
    exact (Classical.choose_spec (hroots θ hθ)).2 z ⟨hz,hΦz⟩
  have hyInterior (θ : E) (hθ : θ∈closure U) : y θ∈interior (closure V) :=
    hrootInterior θ hθ (y θ) (hyK θ hθ) (hzero θ hθ)
  refine ⟨y,fun θ hθ=>⟨hyInterior θ hθ,hzero θ hθ⟩,?_⟩
  exact closed_domain_implicit_function hUopen hUconvex hDcompact hVopen hVconvex hKcompact
    k hk hΦ hzero hunique hyInterior
    (fun θ hθ=>hinv θ hθ (y θ) (hyK θ hθ) (hzero θ hθ))

/-- The literal Euclidean-space instance of revised Lemma B.4. No positive
dimension hypotheses are imposed. -/
theorem euclidean_closed_domain_implicit_function
    {d n : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))}
    {V : Set (EuclideanSpace ℝ (Fin n))}
    {Φ : EuclideanSpace ℝ (Fin d)×EuclideanSpace ℝ (Fin n)→EuclideanSpace ℝ (Fin n)}
    {y : EuclideanSpace ℝ (Fin d)→EuclideanSpace ℝ (Fin n)}
    (hUopen : IsOpen U) (hUconvex : Convex ℝ U) (hDcompact : IsCompact (closure U))
    (hVopen : IsOpen V) (hVconvex : Convex ℝ V) (hKcompact : IsCompact (closure V))
    (k : ℕ) (hk : 1≤k)
    (hΦ : ClosedInteriorCk k Φ (closure U×ˢclosure V))
    (hzero : ∀θ∈closure U,Φ (θ,y θ)=0)
    (hunique : ∀θ∈closure U,∀z∈closure V,Φ (θ,z)=0 → z=y θ)
    (hyInterior : ∀θ∈closure U,y θ∈interior (closure V))
    (hinv : ∀θ∈closure U,
      (partialY (fderivWithin ℝ Φ (closure U×ˢclosure V) (θ,y θ))).IsInvertible) :
    ClosedInteriorCk k y (closure U) ∧
    (∀θ∈closure U,HasFDerivWithinAt y
      (implicitDerivative (fderivWithin ℝ Φ (closure U×ˢclosure V) (θ,y θ)))
      (closure U) θ) ∧
    (∀j : ℕ,j≤k → ∀θ∈closure U,
      iteratedFDerivWithin ℝ j (fun u=>Φ (u,y u)) (closure U) θ=0) :=
  closed_domain_implicit_function hUopen hUconvex hDcompact
    hVopen hVconvex hKcompact k hk hΦ hzero hunique hyInterior hinv

end DepthPaper.RevisedClosedIFT
