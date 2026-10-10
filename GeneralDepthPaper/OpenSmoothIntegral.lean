module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Normed.Group.Continuity

@[expose] public section


/-! Genuine finite-order differentiation of a parameter integral on an
open domain. Local bounds are required only on a neighborhood contained
in that domain; no global smooth extension of the integrand is assumed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 1200000
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {α : Type} [MeasurableSpace α]

theorem iteratedFDeriv_fderiv_eq_curry_open {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E→F) (j : ℕ) (x : E) :
    iteratedFDeriv ℝ j (fderiv ℝ f) x=
      continuousMultilinearCurryRightEquiv' ℝ j E F (iteratedFDeriv ℝ (j+1) f x) := by
  rw [iteratedFDeriv_succ_eq_comp_right]
  simp only [Function.comp_apply,LinearIsometryEquiv.apply_symm_apply]

theorem contDiffOn_integral_of_dominated_derivatives {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (N : ℕ) (μ : Measure α) {U : Set E} (hU : IsOpen U)
    (f : E→α→F) (hf : ∀z,ContDiffOn ℝ N (fun x=>f x z) U)
    (hmeas : ∀j,j≤N→∀x∈U,AEStronglyMeasurable
      (fun z=>iteratedFDeriv ℝ j (fun y=>f y z) x) μ)
    (hbound : ∀x∈U,∃s∈𝓝 x,s⊆U ∧ ∃B:ℕ→α→ℝ,
      (∀j,j≤N→Integrable (B j) μ) ∧
      ∀j,j≤N→∀y∈s,∀z,‖iteratedFDeriv ℝ j (fun u=>f u z) y‖≤B j z) :
    ContDiffOn ℝ N (fun x=>∫z,f x z ∂μ) U := by
  induction N generalizing F with
  | zero=>
    change ContDiffOn ℝ 0 (fun x=>∫z,f x z ∂μ) U
    rw [contDiffOn_zero]
    intro x hx
    obtain ⟨s,hs,hsub,B,hBi,hB⟩ := hbound x hx
    have hm : ∀ᶠy in 𝓝 x,AEStronglyMeasurable (f y) μ := by
      filter_upwards [hs] with y hy
      have hh := (continuousMultilinearCurryFin0 ℝ E F).continuous.comp_aestronglyMeasurable
        (hmeas 0 le_rfl y (hsub hy))
      simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,
        LinearIsometryEquiv.apply_symm_apply] using hh
    exact (continuousAt_of_dominated hm
      (Filter.Eventually.mono hs fun y hy=>Eventually.of_forall fun z=>by
        simpa only [norm_iteratedFDeriv_zero] using hB 0 le_rfl y hy z)
      (hBi 0 le_rfl) (Eventually.of_forall fun z=>
        ((hf z x hx).contDiffAt (hU.mem_nhds hx)).continuousAt)).continuousWithinAt
  | succ N ih=>
    let g : E→α→E→L[ℝ] F := fun x z=>fderiv ℝ (fun y=>f y z) x
    have hg : ∀z,ContDiffOn ℝ N (fun x=>g x z) U :=
      fun z=>(hf z).fderiv_of_isOpen hU (by norm_cast)
    have hgm : ∀j,j≤N→∀x∈U,AEStronglyMeasurable
        (fun z=>iteratedFDeriv ℝ j (fun y=>g y z) x) μ := by
      intro j hj x hx
      have hh := (continuousMultilinearCurryRightEquiv' ℝ j E F).continuous.comp_aestronglyMeasurable
        (hmeas (j+1) (by omega) x hx)
      simpa only [g,iteratedFDeriv_fderiv_eq_curry_open] using hh
    have hgb : ∀x∈U,∃s∈𝓝 x,s⊆U ∧ ∃B:ℕ→α→ℝ,
        (∀j,j≤N→Integrable (B j) μ) ∧
        ∀j,j≤N→∀y∈s,∀z,‖iteratedFDeriv ℝ j (fun u=>g u z) y‖≤B j z := by
      intro x hx
      obtain ⟨s,hs,hsub,B,hBi,hB⟩ := hbound x hx
      refine ⟨s,hs,hsub,fun j=>B (j+1),fun j hj=>hBi _ (by omega),?_⟩
      intro j hj y hy z
      simpa only [g,norm_iteratedFDeriv_fderiv] using hB (j+1) (by omega) y hy z
    have hgd := ih g hg hgm hgb
    have hd : ∀x∈U,HasFDerivAt (fun y=>∫z,f y z ∂μ) (∫z,g x z ∂μ) x := by
      intro x hx
      obtain ⟨s,hs,hsub,B,hBi,hB⟩ := hbound x hx
      have hm : ∀ᶠy in 𝓝 x,AEStronglyMeasurable (f y) μ := by
        filter_upwards [hs] with y hy
        have hh := (continuousMultilinearCurryFin0 ℝ E F).continuous.comp_aestronglyMeasurable
          (hmeas 0 (by omega) y (hsub hy))
        simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,
          LinearIsometryEquiv.apply_symm_apply] using hh
      have hmx : AEStronglyMeasurable (f x) μ := hm.self_of_nhds
      have hi : Integrable (f x) μ := (hBi 0 (by omega)).mono' hmx
        (Eventually.of_forall fun z=>by
          simpa only [norm_iteratedFDeriv_zero] using hB 0 (by omega) x (mem_of_mem_nhds hs) z)
      have hgm0 : AEStronglyMeasurable (g x) μ := by
        have hh := (continuousMultilinearCurryFin0 ℝ E (E→L[ℝ] F)).continuous.comp_aestronglyMeasurable
          (hgm 0 (Nat.zero_le _) x hx)
        simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,
          LinearIsometryEquiv.apply_symm_apply] using hh
      apply hasFDerivAt_integral_of_dominated_of_fderiv_le hs hm hi hgm0 (bound:=B 1)
      · exact Eventually.of_forall fun z y hy=>by
          simpa only [g,norm_iteratedFDeriv_one] using hB 1 (by omega) y hy z
      · exact hBi 1 (by omega)
      · exact Eventually.of_forall fun z y hy=>
          (((hf z y (hsub hy)).contDiffAt (hU.mem_nhds (hsub hy))).differentiableAt (by norm_num)).hasFDerivAt
    rw [show ((N+1:ℕ):ℕ∞ω)=(N:ℕ∞ω)+1 by norm_cast]
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hU.uniqueDiffOn).mpr
    exact ⟨by simp,fun x=>∫z,g x z ∂μ,hgd,fun x hx=>(hd x hx).hasFDerivWithinAt⟩

set_option backward.isDefEq.respectTransparency false in
theorem iteratedFDeriv_integral_on_open_domain {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (N : ℕ) (μ : Measure α) {U : Set E} (hU : IsOpen U)
    (f : E→α→F) (hf : ∀z,ContDiffOn ℝ N (fun x=>f x z) U)
    (hmeas : ∀j,j≤N→∀x∈U,AEStronglyMeasurable
      (fun z=>iteratedFDeriv ℝ j (fun y=>f y z) x) μ)
    (hbound : ∀x∈U,∃s∈𝓝 x,s⊆U ∧ ∃B:ℕ→α→ℝ,
      (∀j,j≤N→Integrable (B j) μ) ∧
      ∀j,j≤N→∀y∈s,∀z,‖iteratedFDeriv ℝ j (fun u=>f u z) y‖≤B j z)
    (j : ℕ) (hj : j≤N) {x : E} (hx : x∈U) :
    iteratedFDeriv ℝ j (fun y=>∫z,f y z ∂μ) x=
      ∫z,iteratedFDeriv ℝ j (fun y=>f y z) x ∂μ := by
  induction j generalizing x with
  | zero=>
    simp only [iteratedFDeriv_zero_eq_comp,Function.comp_apply]
    exact ((continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.integral_comp_comm _).symm
  | succ j ih=>
    let F₀ := fun y z=>iteratedFDeriv ℝ j (fun u=>f u z) y
    let F₁ := fun y z=>fderiv ℝ (fun u=>F₀ u z) y
    have he : (fun y=>iteratedFDeriv ℝ j (fun u=>∫z,f u z ∂μ) y)=ᶠ[𝓝 x]
        (fun y=>∫z,F₀ y z ∂μ) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact ih (by omega) hy
    obtain ⟨s,hs,hsub,B,hBi,hB⟩ := hbound x hx
    have hF₀ : ∀ᶠy in 𝓝 x,AEStronglyMeasurable (F₀ y) μ := by
      filter_upwards [hs] with y hy
      exact hmeas j (by omega) y (hsub hy)
    have hF₁ : AEStronglyMeasurable (F₁ x) μ := by
      have hh := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1)=>E) F).continuous.comp_aestronglyMeasurable
        (hmeas (j+1) hj x hx)
      simpa only [F₀,F₁,fderiv_iteratedFDeriv,Function.comp_apply] using hh
    have hi : Integrable (F₀ x) μ := (hBi j (by omega)).mono' hF₀.self_of_nhds
      (Eventually.of_forall fun z=>hB j (by omega) x (mem_of_mem_nhds hs) z)
    have hd : HasFDerivAt (fun y=>∫z,F₀ y z ∂μ) (∫z,F₁ x z ∂μ) x :=
      hasFDerivAt_integral_of_dominated_of_fderiv_le hs hF₀ hi hF₁ (bound:=B (j+1))
        (Eventually.of_forall fun z y hy=>by
          simpa only [F₀,F₁,norm_fderiv_iteratedFDeriv] using hB (j+1) hj y hy z)
        (hBi (j+1) hj)
        (Eventually.of_forall fun z y hy=>
          (((hf z y (hsub hy)).contDiffAt (hU.mem_nhds (hsub hy))).differentiableAt_iteratedFDeriv
            (by norm_cast)).hasFDerivAt)
    rw [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply,he.fderiv_eq,hd.fderiv]
    have hi₁ : Integrable (F₁ x) μ := (hBi (j+1) hj).mono' hF₁
      (Eventually.of_forall fun z=>by
        simpa only [F₀,F₁,norm_fderiv_iteratedFDeriv] using
          hB (j+1) hj x (mem_of_mem_nhds hs) z)
    have hij : Integrable (fun z=>iteratedFDeriv ℝ (j+1) (fun y=>f y z) x) μ :=
      (hBi (j+1) hj).mono' (hmeas (j+1) hj x hx)
        (Eventually.of_forall fun z=>hB (j+1) hj x (mem_of_mem_nhds hs) z)
    ext v
    change (∫z,F₁ x z ∂μ) (v 0) (Fin.tail v)=_
    rw [ContinuousLinearMap.integral_apply hi₁,ContinuousMultilinearMap.integral_apply hij]
    rw [ContinuousMultilinearMap.integral_apply (hi₁.apply_continuousLinearMap (v 0))]
    apply integral_congr_ae
    exact Eventually.of_forall fun z=>by
      simp only [F₀,F₁,iteratedFDeriv_succ_apply_left]

end GeneralDepthPaper
