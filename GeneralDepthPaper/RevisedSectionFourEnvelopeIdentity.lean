module

public import GeneralDepthPaper.RevisedAsymptoticsEnvelope
public import GeneralDepthPaper.StationaryMassLocalIdentity

@[expose] public section

/-! The full parameter envelope theorem for the actual stationary scalar
objective, and the exact pressure formula for its limiting counterpart. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 64
variable {Θ Z : Type}
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [CompleteSpace Θ]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]

def revisedParameterGradientProjection :
    ((Θ×Z)→L[ℝ]ℝ)→L[ℝ](Θ→L[ℝ]ℝ) :=
  (ContinuousLinearMap.compL ℝ Θ (Θ×Z) ℝ).flip (ContinuousLinearMap.inl ℝ Θ Z)

omit [CompleteSpace Θ] [FiniteDimensional ℝ Z] in
theorem revisedParameterGradientProjection_norm_le :
    ‖revisedParameterGradientProjection (Θ:=Θ) (Z:=Z)‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro L
  apply (ContinuousLinearMap.opNorm_comp_le L _).trans
  have hL : ‖ContinuousLinearMap.inl ℝ Θ Z‖≤1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    simp
  simpa only [mul_one,one_mul] using mul_le_mul_of_nonneg_left hL (norm_nonneg L)

theorem revised_fderiv_stationary_graph
    {f : Θ×Z→ℝ} {q : Θ→Z} {θ : Θ}
    (hf : DifferentiableAt ℝ f (θ,q θ)) (hq : DifferentiableAt ℝ q θ)
    (hs : partialGradient f θ (q θ)=0) :
    fderiv ℝ (fun u=>f (u,q u)) θ=
      revisedParameterGradientProjection (fderiv ℝ f (θ,q θ)) := by
  have hchain := hf.hasFDerivAt.comp θ ((hasFDerivAt_id θ).prodMk hq.hasFDerivAt)
  have he := hchain.fderiv
  simp only [Function.comp_def,id_eq] at he
  rw [he]
  ext v
  change fderiv ℝ f (θ,q θ) (v,fderiv ℝ q θ v)=fderiv ℝ f (θ,q θ) (v,0)
  rw [show (v,fderiv ℝ q θ v)=(v,0)+(0,fderiv ℝ q θ v) by simp,map_add]
  have hz : fderiv ℝ f (θ,q θ) (0,fderiv ℝ q θ v)=0 := by
    rw [partialGradient_eq_fullDerivative f hf] at hs
    have he := congrArg (fun L : Z→L[ℝ]ℝ=>L (fderiv ℝ q θ v)) hs
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply,zero_apply] using he
  rw [hz,add_zero]

theorem revised_eventually_fderiv_stationary_graph
    {f : Θ×Z→ℝ} {q : Θ→Z} {θ : Θ}
    (hf : ContDiffAt ℝ ∞ f (θ,q θ)) (hq : ContDiffAt ℝ ∞ q θ)
    (hs : ∀ᶠu in 𝓝 θ,partialGradient f u (q u)=0) :
    (fun u=>fderiv ℝ (fun t=>f (t,q t)) u)=ᶠ[𝓝 θ]
      (fun u=>revisedParameterGradientProjection (fderiv ℝ f (u,q u))) := by
  have hgraph : ContinuousAt (fun u=>(u,q u)) θ := continuousAt_id.prodMk hq.continuousAt
  filter_upwards [hgraph.eventually (eventually_differentiableAt_of_contDiffAt hf),
    eventually_differentiableAt_of_contDiffAt hq,hs] with u hfu hqu hsu
  exact revised_fderiv_stationary_graph hfu hqu hsu

def revisedLimitingScalarObjective (Ξ : AdmissibleCovariance) (θ : ℝ×ℝ) : ℝ :=
  limitingPressureObjective (scaledThermodynamicPressure Ξ.toEvenMixture) θ.1 θ.2

namespace LimitingStandingData
variable {Ξ : AdmissibleCovariance} {r : ℕ} {seed : AtomicPoint r}

theorem revisedLimitingScalarObjective_eventuallyEq (d : LimitingStandingData Ξ seed)
    (θ : ℝ×ℝ) (hθ : θ∈d.parameterWindow) :
    (fun u=>stationaryLimitingObjective Ξ (u,d.branch u.2))=ᶠ[𝓝 θ]
      revisedLimitingScalarObjective Ξ := by
  filter_upwards [continuousAt_snd.eventually
    (d.massDomain_open.mem_nhds (d.massWindow_subset hθ.2)),
    continuousAt_snd.eventually (isOpen_Ioi.mem_nhds (d.massLower_mem.1.trans_le hθ.2.1))]
    with u hu hupos
  obtain ⟨hzu,hndu⟩ := d.branch_nondegenerate_domain u.2 hu
  exact limitingAtomicObjective_eq_J_of_minimizer Ξ (d.branch u.2) hzu u.2 hupos hndu.1 u.1

theorem revisedLimitingScalarObjective_smooth (d : LimitingStandingData Ξ seed)
    (θ : ℝ×ℝ) (hθ : θ∈d.parameterWindow) :
    ContDiffAt ℝ ∞ (revisedLimitingScalarObjective Ξ) θ := by
  have hz : d.branch θ.2∈closedBall seed d.radius := by
    rw [mem_closedBall]
    linarith [d.branch_close θ.2 hθ.2,d.radius_pos]
  have hcomp : ContDiffAt ℝ ∞ (fun u=>stationaryLimitingObjective Ξ (u,d.branch u.2)) θ :=
    ContDiffAt.comp (g:=stationaryLimitingObjective Ξ) (f:=fun u : ℝ×ℝ=>(u,d.branch u.2)) θ
      (d.boundedSmoothOn_stationaryLimitingObjective.smooth (θ,d.branch θ.2) ⟨hθ,hz⟩)
      (contDiffAt_id.prodMk (d.limiting_branch_bounded_smooth.smooth θ hθ))
  exact hcomp.congr_of_eventuallyEq (d.revisedLimitingScalarObjective_eventuallyEq θ hθ).symm

end LimitingStandingData
end GeneralDepthPaper
