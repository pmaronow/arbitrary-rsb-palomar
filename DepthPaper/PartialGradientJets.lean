module

public import DepthPaper.ImplicitStationaryJets
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section


/-! Partial-gradient jets are contractions of actual scalar jets.  A fourth
scalar-jet bound makes the second gradient jet Lipschitz in the selected
spatial point; this is the genuine modulus required for C² branch errors. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace DepthPaper
variable {Θ E : Type*}
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 64

theorem norm_inr_contraction : ‖ContinuousLinearMap.inr ℝ Θ E‖ ≤ 1 := by
  apply (ContinuousLinearMap.inr ℝ Θ E).opNorm_le_bound (by norm_num)
  intro v
  simp

theorem partialGradient_eq_fullDerivative (f : Θ×E→ℝ) {θ : Θ} {z : E}
    (hf : DifferentiableAt ℝ f (θ,z)) :
    partialGradient f θ z=(fderiv ℝ f (θ,z)).comp (ContinuousLinearMap.inr ℝ Θ E) := by
  have hp := (hasFDerivAt_const (𝕜:=ℝ) (x:=z) θ).prodMk (hasFDerivAt_id (𝕜:=ℝ) z)
  have he : ContinuousLinearMap.prod (0:E→L[ℝ]Θ) (ContinuousLinearMap.id ℝ E)=
      ContinuousLinearMap.inr ℝ Θ E := rfl
  simpa only [partialGradient,Function.comp_def,he] using (hf.hasFDerivAt.comp z hp).fderiv

theorem norm_iteratedFDeriv_partialGradient_le (f : Θ×E→ℝ) {p : Θ×E}
    (hf : ContDiffAt ℝ ∞ f p) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun u:Θ×E=>partialGradient f u.1 u.2) p‖ ≤
      ‖iteratedFDeriv ℝ (j+1) f p‖ := by
  let P : ((Θ×E)→L[ℝ]ℝ)→L[ℝ] (E→L[ℝ]ℝ) :=
    (ContinuousLinearMap.compL ℝ E (Θ×E) ℝ).flip (ContinuousLinearMap.inr ℝ Θ E)
  have hP : ‖P‖ ≤ 1 := by
    apply P.opNorm_le_bound (by norm_num)
    intro L
    apply (ContinuousLinearMap.opNorm_comp_le L _).trans
    simpa only [mul_one,one_mul] using mul_le_mul_of_nonneg_left (norm_inr_contraction (Θ:=Θ) (E:=E)) (norm_nonneg L)
  have he : (fun u:Θ×E=>partialGradient f u.1 u.2)=ᶠ[𝓝 p]
      (P ∘ fderiv ℝ f) := by
    have hd : ∀ᶠu in 𝓝 p,DifferentiableAt ℝ f u :=
      ((hf.of_le (show (1:ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)).mono
        (fun _ hu=>hu.differentiableAt (by simp))
    filter_upwards [hd] with u hu
    exact partialGradient_eq_fullDerivative f hu
  rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
  have hDF := hf.fderiv_right (m:=∞) (by simp)
  apply (P.norm_iteratedFDeriv_comp_left hDF (show (j:ℕ∞ω) ≤ ∞ by simp)).trans
  rw [norm_iteratedFDeriv_fderiv]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hP
    (norm_nonneg (iteratedFDeriv ℝ (j+1) f p))

theorem norm_iteratedFDeriv_partialGradient_sub_le (f g : Θ×E→ℝ) {p : Θ×E}
    (hf : ContDiffAt ℝ ∞ f p) (hg : ContDiffAt ℝ ∞ g p) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun u:Θ×E=>partialGradient f u.1 u.2) p-
      iteratedFDeriv ℝ j (fun u:Θ×E=>partialGradient g u.1 u.2) p‖ ≤
      ‖iteratedFDeriv ℝ (j+1) (fun u=>f u-g u) p‖ := by
  have hF := contDiffAt_partialGradient f hf
  have hG := contDiffAt_partialGradient g hg
  have he : (fun u:Θ×E=>partialGradient f u.1 u.2-partialGradient g u.1 u.2)=ᶠ[𝓝 p]
      (fun u:Θ×E=>partialGradient (fun w=>f w-g w) u.1 u.2) := by
    have hfd : ∀ᶠu in 𝓝 p,DifferentiableAt ℝ f u :=
      ((hf.of_le (show (1:ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)).mono
        (fun _ hu=>hu.differentiableAt (by simp))
    have hgd : ∀ᶠu in 𝓝 p,DifferentiableAt ℝ g u :=
      ((hg.of_le (show (1:ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)).mono
        (fun _ hu=>hu.differentiableAt (by simp))
    filter_upwards [hfd,hgd] with u hu hv
    have hfg : DifferentiableAt ℝ (fun w=>f w-g w) u := by simpa only [Pi.sub_def] using hu.sub hv
    rw [partialGradient_eq_fullDerivative f hu,partialGradient_eq_fullDerivative g hv,
      partialGradient_eq_fullDerivative _ hfg,fderiv_fun_sub hu hv]
    rfl
  rw [←fun_iteratedFDeriv_sub_apply (hF.of_le (by simp)) (hG.of_le (by simp)), (he.iteratedFDeriv ℝ j).eq_of_nhds]
  exact norm_iteratedFDeriv_partialGradient_le _ (hf.sub hg) j

/-- Spatial displacement of the actual partial-gradient jet. -/
theorem partialGradient_jet_spatial_lipschitz (g : Θ×E→ℝ) {s : Set E}
    (hs : Convex ℝ s) (θ : Θ) (j : ℕ) {K : ℝ}
    (hg : ∀z∈s,ContDiffAt ℝ ∞ g (θ,z))
    (hK : ∀z∈s,‖iteratedFDeriv ℝ (j+2) g (θ,z)‖ ≤ K)
    {x y : E} (hx : x∈s) (hy : y∈s) :
    ‖iteratedFDeriv ℝ j (fun u:Θ×E=>partialGradient g u.1 u.2) (θ,y)-
      iteratedFDeriv ℝ j (fun u:Θ×E=>partialGradient g u.1 u.2) (θ,x)‖ ≤ K*‖y-x‖ := by
  let G := fun u:Θ×E=>partialGradient g u.1 u.2
  let J := iteratedFDeriv ℝ j G
  apply hs.norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) ?_ ?_ hx hy
  · intro z hz
    exact (((contDiffAt_partialGradient g (hg z hz)).iteratedFDeriv_right (m:=∞)
      (by simp)).comp z (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  · intro z hz
    have hJ : ContDiffAt ℝ ∞ J (θ,z) :=
      (contDiffAt_partialGradient g (hg z hz)).iteratedFDeriv_right (m:=∞) (by simp)
    have hp := (hasFDerivAt_const (𝕜:=ℝ) (x:=z) θ).prodMk (hasFDerivAt_id (𝕜:=ℝ) z)
    have he : ContinuousLinearMap.prod (0:E→L[ℝ]Θ) (ContinuousLinearMap.id ℝ E)=
        ContinuousLinearMap.inr ℝ Θ E := rfl
    have hd := ((hJ.differentiableAt (by simp)).hasFDerivAt.comp z hp).fderiv
    rw [show fderiv ℝ (fun z=>J (θ,z)) z=(fderiv ℝ J (θ,z)).comp
      (ContinuousLinearMap.inr ℝ Θ E) by simpa only [Function.comp_def,he] using hd]
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    apply (mul_le_mul_of_nonneg_left (norm_inr_contraction (Θ:=Θ) (E:=E)) (norm_nonneg _)).trans
    rw [mul_one,norm_fderiv_iteratedFDeriv]
    exact (norm_iteratedFDeriv_partialGradient_le g (hg z hz) (j+1)).trans (hK z hz)

theorem partialGradient_jet_graph_error (f g : Θ×E→ℝ) {s : Set E}
    (hs : Convex ℝ s) (θ : Θ) (j : ℕ) {K ε : ℝ}
    (hf : ∀z∈s,ContDiffAt ℝ ∞ f (θ,z))
    (hg : ∀z∈s,ContDiffAt ℝ ∞ g (θ,z))
    (hK : ∀z∈s,‖iteratedFDeriv ℝ (j+2) g (θ,z)‖ ≤ K)
    (hε : ∀z∈s,‖iteratedFDeriv ℝ (j+1) (fun u=>f u-g u) (θ,z)‖ ≤ ε)
    {x y : E} (hx : x∈s) (hy : y∈s) :
    ‖iteratedFDeriv ℝ j (fun u:Θ×E=>partialGradient f u.1 u.2) (θ,y)-
      iteratedFDeriv ℝ j (fun u:Θ×E=>partialGradient g u.1 u.2) (θ,x)‖ ≤ ε+K*‖y-x‖ := by
  have he := (norm_iteratedFDeriv_partialGradient_sub_le f g (hf y hy) (hg y hy) j).trans (hε y hy)
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add he (partialGradient_jet_spatial_lipschitz g hs θ j hg hK hx hy))

end DepthPaper
