module

public import DepthPaper.HighDegreeLowerBounds

@[expose] public section


/-! Quantitative assembly of genuine finite recursion input jets. The norms
are the actual product/Pi operator norms used by the Cole–Hopf parameter
space, rather than an informal coordinate bound. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
namespace DepthPaper
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
set_option maxSynthPendingDepth 64

theorem norm_iteratedFDeriv_pi_le {ι : Type*} [Fintype ι] {f : E→ι→F}
    {x : E} (hf : ContDiffAt ℝ ∞ f x) (j : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀i,‖iteratedFDeriv ℝ j (fun y => f y i) x‖ ≤ C) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro u
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))).mpr
  intro i
  have he : iteratedFDeriv ℝ j (fun y => f y i) x=
      (ContinuousLinearMap.proj i).compContinuousMultilinearMap (iteratedFDeriv ℝ j f x) :=
    (ContinuousLinearMap.proj i).iteratedFDeriv_comp_left hf (by simp)
  have hev : (iteratedFDeriv ℝ j f x u) i=iteratedFDeriv ℝ j (fun y => f y i) x u := by
    rw [he]
    rfl
  rw [hev]
  exact ((iteratedFDeriv ℝ j (fun y => f y i) x).le_opNorm u).trans (mul_le_mul_of_nonneg_right (hb i) (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))

theorem norm_iteratedFDeriv_prod_le {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E→F} {g : E→G} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (hg : ContDiffAt ℝ ∞ g x) (j : ℕ) {C : ℝ}
    (hbf : ‖iteratedFDeriv ℝ j f x‖ ≤ C) (hbg : ‖iteratedFDeriv ℝ j g x‖ ≤ C) :
    ‖iteratedFDeriv ℝ j (fun y => (f y,g y)) x‖ ≤ C := by
  rw [iteratedFDeriv_prodMk hf hg (by simp)]
  apply ContinuousMultilinearMap.opNorm_le_bound ((norm_nonneg _).trans hbf)
  intro u
  change ‖(iteratedFDeriv ℝ j f x u,iteratedFDeriv ℝ j g x u)‖ ≤ _
  rw [Prod.norm_def]
  exact max_le (((iteratedFDeriv ℝ j f x).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right hbf (Finset.prod_nonneg (fun _ _ => norm_nonneg _))))
    (((iteratedFDeriv ℝ j g x).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right hbg (Finset.prod_nonneg (fun _ _ => norm_nonneg _))))



theorem iteratedFDeriv_comp_CLM_local {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E→L[ℝ] F) {f : F→G} {x : E} (hf : ContDiffAt ℝ ∞ f (L x)) (j : ℕ) :
    iteratedFDeriv ℝ j (f ∘ L) x=
      (iteratedFDeriv ℝ j f (L x)).compContinuousLinearMap (fun _ => L) := by
  obtain ⟨u,hu,hxu,hfu⟩ := (hf.contDiffWithinAt (s:=univ)).contDiffOn'
    (m:=(j:ℕ∞ω)) (by simp) (by simp)
  have hfu' : ContDiffOn ℝ j f u := by simpa using hfu
  have hp : IsOpen (L ⁻¹' u) := hu.preimage L.continuous
  have H := L.iteratedFDerivWithin_comp_right hfu' hu.uniqueDiffOn hp.uniqueDiffOn hxu le_rfl
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hp.uniqueDiffOn
      ((hf.comp x L.contDiff.contDiffAt).of_le (by simp)) hxu,
    iteratedFDerivWithin_eq_iteratedFDeriv hu.uniqueDiffOn (hf.of_le (by simp)) hxu] at H
  exact H

theorem norm_iteratedFDeriv_comp_CLM_contraction {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E→L[ℝ] F) (hL : ‖L‖ ≤ 1) {f : F→G} {x : E}
    (hf : ContDiffAt ℝ ∞ f (L x)) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ j f (L x)‖ := by
  rw [iteratedFDeriv_comp_CLM_local L hf j]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  have hp : (∏i:Fin j,‖L‖) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hL)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (norm_nonneg _)


theorem BoundedSmoothOn.all_orders_up_to_bound {f : E→F} {s : Set E}
    (hf : BoundedSmoothOn f s) (j : ℕ) :
    ∃C:ℝ,1 ≤ C ∧ ∀x∈s,∀i:ℕ,i ≤ j → ‖iteratedFDeriv ℝ i f x‖ ≤ C := by
  choose C hC hb using hf.bound
  refine ⟨1+∑i∈Finset.range (j+1),C i,le_add_of_nonneg_right
    (Finset.sum_nonneg (fun i _ => hC i)),?_⟩
  intro x hx i hi
  exact (hb i x hx).trans ((Finset.single_le_sum (fun k _ => hC k)
    (Finset.mem_range.mpr (by omega))).trans (le_add_of_nonneg_left zero_le_one))

end DepthPaper
