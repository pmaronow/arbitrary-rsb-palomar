module

public import GeneralDepthPaper.CoerciveStationaryLocal

@[expose] public section


/-! Genuine stationarity on an ordinary neighborhood, including when the
chosen physical parameter lies on a closed parameter-window boundary. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace GeneralDepthPaper
variable {Θ E:Type*}
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem eventually_stationary_coerciveBallStationarySelector
    (f:Θ×E→ℝ) (c z₀:E) (R d κ:ℝ) (θ:Θ) (hd:0<d) (hκ:0<κ)
    (hz₀:dist z₀ c≤R-d)
    (hf:∀z∈closedBall c R,ContDiffAt ℝ ∞ f (θ,z))
    (hB:∀z∈closedBall c R,∀v:E,
      κ*‖v‖^2≤fderiv ℝ (partialGradient f θ) z v v)
    (hsmall:‖partialGradient f θ z₀‖<κ*d/2) :
    ∀ᶠu in 𝓝 θ,coerciveBallStationarySelector f c R u∈ball c R ∧
      partialGradient f u (coerciveBallStationarySelector f c R u)=0 := by
  classical
  let q := coerciveBallStationarySelector f c R
  have hs := coerciveBallStationarySelector_spec f c z₀ R d κ θ hd hκ hz₀ hf hB hsmall
  have hq : q θ∈closedBall c R := ball_subset_closedBall hs.1
  have hG := contDiffAt_partialGradient f (hf _ hq)
  have hpos : ∀v:E,v≠0→0<(fderiv ℝ (fun p:Θ×E=>partialGradient f p.1 p.2) (θ,q θ)
      ∘L ContinuousLinearMap.inr ℝ Θ E) v v := by
    rw [partialGradient_partial_hessian f (hf _ hq)]
    intro v hv
    exact (mul_pos hκ (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv))).trans_le (hB _ hq v)
  obtain ⟨w,hwθ,hws,hwe,_⟩ := FourPapersCommon.exists_smooth_stationary_selector
    (fun p:Θ×E=>partialGradient f p.1 p.2) (θ,q θ) hG (by simp) hs.2.1 hpos
  have hwb : ∀ᶠu in 𝓝 θ,w u∈ball c R :=
    hws.continuousAt.eventually (isOpen_ball.mem_nhds (hwθ.symm ▸ hs.1))
  filter_upwards [hwe,hwb] with u hwu hbu
  have hex : ∃z∈ball c R,partialGradient f u z=0 := ⟨w u,hbu,hwu⟩
  simpa only [coerciveBallStationarySelector,dif_pos hex] using hex.choose_spec

end GeneralDepthPaper
