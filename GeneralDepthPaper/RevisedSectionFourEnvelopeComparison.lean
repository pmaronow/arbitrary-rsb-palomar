module

public import GeneralDepthPaper.CompositionDifferenceBounds
public import GeneralDepthPaper.StationaryGraphBounds

@[expose] public section

/-! Full derivative fields, rather than a single directional response,
converge in C² from C³ scalar errors and C² graph errors. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 64
universe u
variable {E F G : Type u}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem revised_full_derivative_C2_comparison
    (g : F→G) (s : Set F) (hg : BoundedSmoothOn g s) (hs : Convex ℝ s)
    (D : ℝ) (hD : 1≤D) :
    ∃C : ℝ,0≤C ∧ ∀f : F→G,∀a b : E→F,∀x : E,∀ε η : ℝ,
      0≤ε → 0≤η → ContDiffAt ℝ ∞ a x → ContDiffAt ℝ ∞ b x → a x∈s → b x∈s →
      ContDiffAt ℝ ∞ f (a x) →
      (∀i,i≤2 → ‖iteratedFDeriv ℝ i a x‖≤D) →
      (∀i,i≤2 → ‖iteratedFDeriv ℝ i b x‖≤D) →
      (∀i,i≤2 → ‖iteratedFDeriv ℝ i (fun y=>a y-b y) x‖≤η) →
      (∀ i : ℕ, 1 ≤ i → i ≤ 3 → ‖iteratedFDeriv ℝ i (fun y=>f y-g y) (a x)‖ ≤ ε) →
      ∀j,j≤2 → ‖iteratedFDeriv ℝ j
        (fun y=>fderiv ℝ f (a y)-fderiv ℝ g (b y)) x‖≤C*(ε+η) := by
  obtain ⟨K,hK,HK⟩ := composition_difference_bounds_up_to (E:=E) 2 hg.fderiv hs D hD
  refine ⟨2*D^2+K,by positivity,?_⟩
  intro f a b x ε η hε hη ha hb hax hbx hf haja hajb hd hj j hj2
  let R : F→F→L[ℝ]G := fun w=>fderiv ℝ f w-fderiv ℝ g w
  let H : F→F→L[ℝ]G := fderiv ℝ g
  have hR : ContDiffAt ℝ ∞ R (a x) :=
    (hf.fderiv_right (m:=∞) (by simp)).sub (hg.fderiv.smooth (a x) hax)
  have hRb (i : ℕ) (hi : i≤2) : ‖iteratedFDeriv ℝ i R (a x)‖≤ε := by
    rw [norm_iteratedFDeriv_fderiv_difference hf (hg.smooth (a x) hax)]
    exact hj (i+1) (by omega) (by omega)
  have hsmall := norm_iteratedFDeriv_composition_uniform_low_order hR ha 2 hε hD hRb haja j hj2
  have hfixed := HK a b x η hη ha hb hax hbx haja hajb hd j hj2
  have he : (fun y=>fderiv ℝ f (a y)-fderiv ℝ g (b y))=
      (fun y=>(R∘a) y+(H (a y)-H (b y))) := by
    funext y
    dsimp only [R,H,Function.comp_def]
    abel
  have hfix : ContDiffAt ℝ ∞ (fun y=>H (a y)-H (b y)) x :=
    ((hg.fderiv.smooth (a x) hax).comp x ha).sub
      ((hg.fderiv.smooth (b x) hbx).comp x hb)
  rw [he,fun_iteratedFDeriv_add_apply ((hR.comp x ha).of_le (by simp))
    (hfix.of_le (by simp))]
  have hn : ‖iteratedFDeriv ℝ j (R∘a) x+
      iteratedFDeriv ℝ j (fun y=>H (a y)-H (b y)) x‖≤2*ε*D^2+K*η :=
    (norm_add_le _ _).trans (add_le_add (by simpa using hsmall) hfixed)
  exact hn.trans (by
    have h1 := mul_nonneg (show (0:ℝ)≤2*D^2 by positivity) hη
    have h2 := mul_nonneg hK hε
    nlinarith)

end GeneralDepthPaper
