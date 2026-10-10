module

public import DepthPaper.StationaryMassJetBounds
public import DepthPaper.StationaryGraphBounds

@[expose] public section


/-! Actual directional responses lose one scalar derivative. Their C²
composition errors are controlled by C³ scalar errors and C² graph errors. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 64
variable {E F:Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem directional_response_C2_comparison
    (g:F→ℝ) (v:F) (hv:‖v‖ ≤ 1) (s:Set F)
    (hH:BoundedSmoothOn (fun w=>fderiv ℝ g w v) s) (hs:Convex ℝ s)
    (D:ℝ) (hD:1 ≤ D) :
    ∃C:ℝ,0 ≤ C ∧ ∀f:F→ℝ,∀a b:E→F,∀x:E,∀ε η:ℝ,
      0 ≤ ε → 0 ≤ η → ContDiffAt ℝ ∞ a x → ContDiffAt ℝ ∞ b x → a x∈s → b x∈s →
      ContDiffAt ℝ ∞ f (a x) → ContDiffAt ℝ ∞ g (a x) →
      (∀i,i ≤ 2→‖iteratedFDeriv ℝ i a x‖ ≤ D)→
      (∀i,i ≤ 2→‖iteratedFDeriv ℝ i b x‖ ≤ D)→
      (∀i,i ≤ 2→‖iteratedFDeriv ℝ i (fun y=>a y-b y) x‖ ≤ η)→
      (∀i,1 ≤ i→i ≤ 3→‖iteratedFDeriv ℝ i (fun y=>f y-g y) (a x)‖ ≤ ε)→
      ∀j,j ≤ 2→‖iteratedFDeriv ℝ j
        (fun y=>fderiv ℝ f (a y) v-fderiv ℝ g (b y) v) x‖ ≤ C*(ε+η) := by
  obtain ⟨K,hK,HK⟩:=composition_difference_bounds_up_to (E:=E) 2 hH hs D hD
  refine ⟨2*D^2+K,by positivity,?_⟩
  intro f a b x ε η hε hη ha hb hax hbx hf hg hja hjb hjdiff hjscalar j hj
  let R: F→ℝ:=fun w=>fderiv ℝ f w v-fderiv ℝ g w v
  let H:F→ℝ:=fun w=>fderiv ℝ g w v
  have hR:ContDiffAt ℝ ∞ R (a x) :=
    ((hf.fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const).sub
      ((hg.fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const)
  have hRbound (i:ℕ) (hi:i ≤ 2):‖iteratedFDeriv ℝ i R (a x)‖ ≤ ε :=
    (norm_directional_jet_difference_le hf hg v hv i).trans
      (hjscalar (i+1) (by omega) (by omega))
  have hsmall:=norm_iteratedFDeriv_composition_uniform_low_order hR ha 2 hε hD hRbound hja j hj
  have hfixed:=HK a b x η hη ha hb hax hbx hja hjb hjdiff j hj
  have he:(fun y=>fderiv ℝ f (a y) v-fderiv ℝ g (b y) v)=
      (fun y=>(R∘a) y+(H (a y)-H (b y))) := by
    ext y
    dsimp only [R,H,Function.comp_def]
    ring
  have hfix:ContDiffAt ℝ ∞ (fun y=>H (a y)-H (b y)) x :=
    ((hH.smooth _ hax).comp x ha).sub ((hH.smooth _ hbx).comp x hb)
  rw [he,fun_iteratedFDeriv_add_apply ((hR.comp x ha).of_le (by simp))
    (hfix.of_le (by simp))]
  have hn:‖iteratedFDeriv ℝ j (R∘a) x+
      iteratedFDeriv ℝ j (fun y=>H (a y)-H (b y)) x‖ ≤ 2*ε*D^2+K*η := by
    exact (norm_add_le _ _).trans (add_le_add (by simpa using hsmall) hfixed)
  exact hn.trans (by
    have h1:=mul_nonneg (show (0:ℝ) ≤ 2*D^2 by positivity) hη
    have h2:=mul_nonneg hK hε
    nlinarith)

end DepthPaper
