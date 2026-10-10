module

public import GeneralDepthPaper.CompositionDifferenceBounds

@[expose] public section


/-! Quantitative chain bounds for two parameter maps with the same
value at the base point. Only the actual outer jets at that common point
are used; a global convex-neighborhood bound is unnecessary. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
namespace GeneralDepthPaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 64
universe u
variable {E F G:Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem coincident_composition_difference_bounds_up_to (n:ℕ) (D:ℝ) (hD:1 ≤ D) :
    ∃C:ℝ,0 ≤ C ∧ ∀H:F→G,∀f g:E→F,∀x:E,∀A ε:ℝ,0 ≤ A→0 ≤ ε→
      ContDiffAt ℝ ∞ H (f x)→ContDiffAt ℝ ∞ f x→ContDiffAt ℝ ∞ g x→f x=g x→
      (∀i,i ≤ n→‖iteratedFDeriv ℝ i H (f x)‖ ≤ A)→
      (∀i,i ≤ n→‖iteratedFDeriv ℝ i f x‖ ≤ D)→
      (∀i,i ≤ n→‖iteratedFDeriv ℝ i g x‖ ≤ D)→
      (∀i,i ≤ n→‖iteratedFDeriv ℝ i (fun y=>f y-g y) x‖ ≤ ε)→
      ∀j,j ≤ n→‖iteratedFDeriv ℝ j (fun y=>H (f y)-H (g y)) x‖ ≤ C*A*ε := by
  classical
  induction n generalizing G with
  | zero=>
    refine ⟨0,le_rfl,?_⟩
    intro H f g x A ε hA hε hH hf hg heq hHb hfb hgb hdiff j hj
    have hj0:j=0:=by omega
    subst j
    simp [norm_iteratedFDeriv_zero,heq]
  | succ n ih=>
    obtain ⟨Cprev,hCprev,hprev⟩ := ih (G:=G)
    obtain ⟨Cdiff,hCdiff,hdiff⟩ := ih (G:=F→L[ℝ] G)
    let L := ContinuousLinearMap.compL ℝ E F G
    let K:ℝ := ‖L‖*(2:ℝ)^n*(Cdiff*D+(n.factorial:ℝ)*D^n)
    have hK:0 ≤ K := by dsimp only [K];positivity
    refine ⟨max Cprev K,hCprev.trans (le_max_left _ _),?_⟩
    intro H f g x A ε hA hε hH hf hg heq hHb hfb hgb hdj j hj
    have hHG:ContDiffAt ℝ ∞ H (g x) := by rw [←heq];exact hH
    by_cases hjn:j ≤ n
    · exact (hprev H f g x A ε hA hε hH hf hg heq
        (fun i hi=>hHb i (by omega)) (fun i hi=>hfb i (by omega))
        (fun i hi=>hgb i (by omega)) (fun i hi=>hdj i (by omega)) j hjn).trans
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hA) hε)
    · have hjEq:j=n+1 := by omega
      subst j
      let U:E→F→L[ℝ] G := fun y=>fderiv ℝ H (f y)-fderiv ℝ H (g y)
      let V:E→E→L[ℝ] F := fderiv ℝ f
      let P:E→F→L[ℝ] G := fun y=>fderiv ℝ H (g y)
      let Q:E→E→L[ℝ] F := fun y=>fderiv ℝ f y-fderiv ℝ g y
      have hHF:ContDiffAt ℝ ∞ (fderiv ℝ H) (f x) := hH.fderiv_right (m:=∞) (by simp)
      have hHGF:ContDiffAt ℝ ∞ (fderiv ℝ H) (g x) := hHG.fderiv_right (m:=∞) (by simp)
      have hU:ContDiffAt ℝ ∞ U x := (hHF.comp x hf).sub (hHGF.comp x hg)
      have hV:ContDiffAt ℝ ∞ V x := hf.fderiv_right (m:=∞) (by simp)
      have hP:ContDiffAt ℝ ∞ P x := hHGF.comp x hg
      have hQ:ContDiffAt ℝ ∞ Q x :=
        (hf.fderiv_right (m:=∞) (by simp)).sub (hg.fderiv_right (m:=∞) (by simp))
      have hHfb:∀i,i ≤ n→‖iteratedFDeriv ℝ i (fderiv ℝ H) (f x)‖ ≤ A := by
        intro i hi
        rw [norm_iteratedFDeriv_fderiv]
        exact hHb (i+1) (by omega)
      have hUb:∀i,i ≤ n→‖iteratedFDeriv ℝ i U x‖ ≤ Cdiff*A*ε :=
        hdiff (fderiv ℝ H) f g x A ε hA hε hHF hf hg heq hHfb
          (fun i hi=>hfb i (by omega)) (fun i hi=>hgb i (by omega))
          (fun i hi=>hdj i (by omega))
      have hVb:∀i,i ≤ n→‖iteratedFDeriv ℝ i V x‖ ≤ D := by
        intro i hi
        rw [norm_iteratedFDeriv_fderiv]
        exact hfb (i+1) (by omega)
      let B:ℝ := (n.factorial:ℝ)*A*D^n
      have hB:0 ≤ B := by dsimp only [B];positivity
      have hPb:∀i,i ≤ n→‖iteratedFDeriv ℝ i P x‖ ≤ B :=
        norm_iteratedFDeriv_composition_uniform_low_order hHGF hg n hA hD
          (fun i hi=>by rw [←heq];exact hHfb i hi) (fun i hi=>hgb i (by omega))
      have hQb:∀i,i ≤ n→‖iteratedFDeriv ℝ i Q x‖ ≤ ε := by
        intro i hi
        rw [norm_iteratedFDeriv_fderiv_difference hf hg]
        exact hdj (i+1) (by omega)
      have hUV := norm_iteratedFDeriv_bilinear_uniform_bound L hU hV n
        (mul_nonneg (mul_nonneg hCdiff hA) hε) (zero_le_one.trans hD) hUb hVb
      have hPQ := norm_iteratedFDeriv_bilinear_uniform_bound L hP hQ n hB hε hPb hQb
      have hs1:ContDiffAt ℝ ∞ (fun y=>L (U y) (V y)) x :=
        L.isBoundedBilinearMap.contDiff.contDiffAt.comp₂ hU hV
      have hs2:ContDiffAt ℝ ∞ (fun y=>L (P y) (Q y)) x :=
        L.isBoundedBilinearMap.contDiff.contDiffAt.comp₂ hP hQ
      have he := eventually_fderiv_composition_difference hH hHG hf hg
      have heqjet:‖iteratedFDeriv ℝ (n+1) (fun y=>H (f y)-H (g y)) x‖=
          ‖iteratedFDeriv ℝ n (fun y=>L (U y) (V y)+L (P y) (Q y)) x‖ := by
        rw [←norm_iteratedFDeriv_fderiv]
        exact congrArg norm ((he.iteratedFDeriv (𝕜:=ℝ) n).eq_of_nhds)
      rw [heqjet,fun_iteratedFDeriv_add_apply (hs1.of_le (by simp)) (hs2.of_le (by simp))]
      have hsum:‖iteratedFDeriv ℝ n (fun y=>L (U y) (V y)) x‖+
          ‖iteratedFDeriv ℝ n (fun y=>L (P y) (Q y)) x‖ ≤ K*A*ε := by
        convert add_le_add hUV hPQ using 1 <;> dsimp only [K,B] <;> ring
      exact (norm_add_le _ _).trans (hsum.trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hA) hε))

end GeneralDepthPaper
