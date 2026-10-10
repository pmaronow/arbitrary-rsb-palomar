module

public import GeneralDepthPaper.ConvexStationaryBall
public import GeneralDepthPaper.FrozenEndpointJetBounds

@[expose] public section


/-! Restricting actual full Fréchet jets to the atomic-coordinate fiber is
a contraction for the product norm, including the actual dual Hessian. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GeneralDepthPaper
variable {Θ E:Type} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 1000000

def partialHessian (f:Θ×E→ℝ) (θ:Θ) (z:E) : E→L[ℝ] E→L[ℝ]ℝ :=
  fderiv ℝ (partialGradient f θ) z

theorem norm_partial_fiber_jet_le {f:Θ×E→ℝ} {θ:Θ} {z:E}
    (hf:ContDiffAt ℝ ∞ f (θ,z)) (j:ℕ) :
    ‖iteratedFDeriv ℝ j (fun w=>f (θ,w)) z‖ ≤ ‖iteratedFDeriv ℝ j f (θ,z)‖ := by
  have hL:‖ContinuousLinearMap.inr ℝ Θ E‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    simp only [ContinuousLinearMap.inr_apply,Prod.norm_def,norm_zero,one_mul]
    exact max_le (norm_nonneg _) le_rfl
  have H:=norm_iteratedFDeriv_affine_contraction_at (ContinuousLinearMap.inr ℝ Θ E) hL
    (θ,0) (x:=z) (by simpa only [ContinuousLinearMap.inr_apply,Prod.mk_add_mk,
      zero_add,add_zero] using hf) j
  simpa only [ContinuousLinearMap.inr_apply,Prod.mk_add_mk,zero_add,add_zero] using H

theorem norm_partialGradient_le {f:Θ×E→ℝ} {θ:Θ} {z:E}
    (hf:ContDiffAt ℝ ∞ f (θ,z)) :
    ‖partialGradient f θ z‖ ≤ ‖iteratedFDeriv ℝ 1 f (θ,z)‖ := by
  simpa only [partialGradient,norm_iteratedFDeriv_one] using norm_partial_fiber_jet_le hf 1

theorem norm_partialHessian_le {f:Θ×E→ℝ} {θ:Θ} {z:E}
    (hf:ContDiffAt ℝ ∞ f (θ,z)) :
    ‖partialHessian f θ z‖ ≤ ‖iteratedFDeriv ℝ 2 f (θ,z)‖ := by
  change ‖fderiv ℝ (fderiv ℝ (fun w=>f (θ,w))) z‖ ≤ _
  simpa only [←norm_iteratedFDeriv_fderiv (n:=1),
    norm_iteratedFDeriv_one] using norm_partial_fiber_jet_le hf 2

theorem partialGradient_sub {f g:Θ×E→ℝ} {θ:Θ} {z:E}
    (hf:ContDiffAt ℝ ∞ f (θ,z)) (hg:ContDiffAt ℝ ∞ g (θ,z)) :
    partialGradient (fun p=>f p-g p) θ z=partialGradient f θ z-partialGradient g θ z := by
  exact fderiv_sub
    ((hf.comp z (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp))
    ((hg.comp z (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp))

theorem partialHessian_sub {f g:Θ×E→ℝ} {θ:Θ} {z:E}
    (hf:ContDiffAt ℝ ∞ f (θ,z)) (hg:ContDiffAt ℝ ∞ g (θ,z)) :
    partialHessian (fun p=>f p-g p) θ z=partialHessian f θ z-partialHessian g θ z := by
  have hff:=hf.comp z (contDiffAt_const.prodMk contDiffAt_id)
  have hgg:=hg.comp z (contDiffAt_const.prodMk contDiffAt_id)
  have he:(partialGradient (fun p=>f p-g p) θ)=ᶠ[𝓝 z]
      (fun w=>partialGradient f θ w-partialGradient g θ w) := by
    filter_upwards [eventually_differentiableAt_of_contDiffAt hff,
      eventually_differentiableAt_of_contDiffAt hgg] with w hwf hwg
    exact fderiv_sub hwf hwg
  rw [partialHessian,he.fderiv_eq]
  exact fderiv_sub
    ((hff.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp))
    ((hgg.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp))

theorem norm_partialGradient_sub_le {f g:Θ×E→ℝ} {θ:Θ} {z:E}
    (hf:ContDiffAt ℝ ∞ f (θ,z)) (hg:ContDiffAt ℝ ∞ g (θ,z)) :
    ‖partialGradient f θ z-partialGradient g θ z‖ ≤
      ‖iteratedFDeriv ℝ 1 (fun p=>f p-g p) (θ,z)‖ := by
  rw [←partialGradient_sub hf hg]
  exact norm_partialGradient_le (hf.sub hg)

theorem norm_partialHessian_sub_le {f g:Θ×E→ℝ} {θ:Θ} {z:E}
    (hf:ContDiffAt ℝ ∞ f (θ,z)) (hg:ContDiffAt ℝ ∞ g (θ,z)) :
    ‖partialHessian f θ z-partialHessian g θ z‖ ≤
      ‖iteratedFDeriv ℝ 2 (fun p=>f p-g p) (θ,z)‖ := by
  rw [←partialHessian_sub hf hg]
  exact norm_partialHessian_le (hf.sub hg)

end GeneralDepthPaper
