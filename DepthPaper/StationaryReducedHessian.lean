module

public import DepthPaper.StationaryScalarHessian
public import DepthPaper.StationaryMassPositive

@[expose] public section


/-! The actual lower and mass coordinates have a positive full reduced
Hessian, obtained by differentiating the true lower stationary equation. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 64

def fixedCouplingReducedObjective (Ξ:AdmissibleCovariance) {r:ℕ}
    (p:ℕ) (qc cQ CQ lam:ℝ) (v:AtomicPoint r×ℝ) : ℝ :=
  stationaryReducedObjective Ξ p qc cQ CQ ((lam,v.2),v.1)

def fixedCouplingAssembly {r:ℕ} :
    (AtomicPoint r×ℝ)→L[ℝ]((ℝ×ℝ)×AtomicPoint r) :=
  (ContinuousLinearMap.prod (0:(AtomicPoint r×ℝ)→L[ℝ]ℝ)
    (ContinuousLinearMap.snd ℝ (AtomicPoint r) ℝ)).prod
      (ContinuousLinearMap.fst ℝ (AtomicPoint r) ℝ)

namespace LimitingStandingData
variable {Ξ:AdmissibleCovariance} {r:ℕ} {seed:AtomicPoint r}

theorem stationary_reduced_hessian_positive (d:LimitingStandingData Ξ seed) :
    ∀ᶠp:ℕ in atTop,∀he:Even p,∀theta∈d.parameterWindow,
      ∀v:AtomicPoint r×ℝ,v≠0→0<fderiv ℝ
        (fderiv ℝ (fixedCouplingReducedObjective Ξ p d.cutoff d.stripRateLower d.stripRateUpper theta.1))
        (d.stationaryBranch p theta,theta.2) v v := by
  obtain ⟨_,_,_,_,_,Hreg⟩:=d.stationaryBranch_regular_error_eventually
  filter_upwards [Hreg,d.stationaryMassFunction_mass_partial_pos_eventually] with p hp hm he theta ht
  let F:=stationaryReducedObjective Ξ (r:=r) p d.cutoff d.stripRateLower d.stripRateUpper
  let f:=fixedCouplingReducedObjective Ξ (r:=r) p d.cutoff d.stripRateLower d.stripRateUpper theta.1
  let q:ℝ→AtomicPoint r:=fun m=>d.stationaryBranch p (theta.1,m)
  have hr:=hp he theta ht
  have hb:d.stationaryBranch p theta∈closedBall seed d.radius :=
    ball_subset_closedBall (hr.2.2.2.2.self_of_nhds.1)
  have hF:ContDiffAt ℝ ∞ F (theta,d.stationaryBranch p theta) := hr.2.1 _ hb
  have hf:ContDiffAt ℝ 2 f (q theta.2,theta.2) := by
    exact (hF.comp (q theta.2,theta.2)
      ((contDiffAt_const.prodMk contDiffAt_snd).prodMk contDiffAt_fst)).of_le (by simp)
  have hq:ContDiffAt ℝ 2 q theta.2 :=
    (hr.1.comp theta.2 (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)
  have hgraph:ContinuousAt (fun m:ℝ=>((theta.1,m),q m)) theta.2 :=
    (continuousAt_const.prodMk continuousAt_id).prodMk hq.continuousAt
  have hz:∀ᶠm in 𝓝 theta.2,∀v:AtomicPoint r,fderiv ℝ f (q m,m) (v,0)=0 := by
    have hnear:∀ᶠm in 𝓝 theta.2,
        partialGradient F (theta.1,m) (q m)=0 :=
      ((continuousAt_const.prodMk continuousAt_id).eventually hr.2.2.2.2).mono (fun _ h=>h.2)
    have hFD:∀ᶠm in 𝓝 theta.2,DifferentiableAt ℝ F ((theta.1,m),q m) :=
      (hgraph.eventually ((hF.of_le (show (1:WithTop ℕ∞)≤∞ by simp)).eventually (by norm_num))).mono (fun _ hu=>hu.differentiableAt (by norm_num))
    filter_upwards [hnear,hFD] with m hzero hdiff
    intro v
    have hi:HasFDerivAt (fun y:AtomicPoint r×ℝ=>((theta.1,y.2),y.1))
        fixedCouplingAssembly (q m,m) := by
      convert ((hasFDerivAt_const (𝕜:=ℝ) theta.1 (q m,m)).prodMk
        (hasFDerivAt_snd (𝕜:=ℝ) (p:=(q m,m)))).prodMk (hasFDerivAt_fst (𝕜:=ℝ) (p:=(q m,m))) using 1 <;> rfl
    have hd:=hdiff.hasFDerivAt.comp (q m,m) hi
    have hzfull:=congrArg (fun L:AtomicPoint r→L[ℝ]ℝ=>L v) hzero
    rw [partialGradient_eq_fullDerivative _ hdiff] at hzfull
    change (fderiv ℝ (F ∘ fun y:AtomicPoint r×ℝ=>((theta.1,y.2),y.1)) (q m,m)) (v,0)=0
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply,zero_apply] at hzfull
    change fderiv ℝ F ((theta.1,m),q m) ((0,0),v)=0 at hzfull
    change fderiv ℝ F ((theta.1,m),q m) ((0,0),v)=0
    exact hzfull

  have hA:∀v:AtomicPoint r,v≠0→0<fderiv ℝ (fderiv ℝ f) (q theta.2,theta.2) (v,0) (v,0) := by
    intro v hv
    have he:=scalar_hessian_affine (f:=f) (ContinuousLinearMap.inl ℝ (AtomicPoint r) ℝ)
      (0,theta.2) (q theta.2) (by simpa using hf) v v
    have he':partialHessian F theta (q theta.2) v v=
        fderiv ℝ (fderiv ℝ f) (q theta.2,theta.2) (v,0) (v,0) := by
      change fderiv ℝ (fderiv ℝ (fun y=>F (theta,y))) (q theta.2) v v=_
      simpa only [ContinuousLinearMap.inl_apply,Prod.mk_add_mk,zero_add,add_zero,
        partialHessian,partialGradient,f,fixedCouplingReducedObjective,F,q,Prod.eta] using he
    rw [←he']
    exact (mul_pos (half_pos d.margin_pos) (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv))).trans_le
      (hr.2.2.1 _ hb v)
  have hMD:=hm he theta ht
  have hdg:HasDerivAt (fun m=>d.stationaryMassFunction p (theta.1,m))
      (fderiv ℝ (d.stationaryMassFunction p) theta (0,1)) theta.2 :=
    by simpa only [Function.comp_def,id_eq,Prod.eta] using
      (hMD.1.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt theta.2
        ((hasDerivAt_const theta.2 theta.1).prodMk (hasDerivAt_id theta.2))
  have heq:(fun m=>fderiv ℝ f (q m,m) (0,1))=ᶠ[𝓝 theta.2]
      (fun m=>d.stationaryMassFunction p (theta.1,m)) := by
    have hFD:∀ᶠm in 𝓝 theta.2,DifferentiableAt ℝ F ((theta.1,m),q m) :=
      (hgraph.eventually ((hF.of_le (show (1:WithTop ℕ∞)≤∞ by simp)).eventually (by norm_num))).mono (fun _ hu=>hu.differentiableAt (by norm_num))
    filter_upwards [hFD] with m hdiff
    have hi:HasFDerivAt (fun y:AtomicPoint r×ℝ=>((theta.1,y.2),y.1))
        fixedCouplingAssembly (q m,m) := by
      convert ((hasFDerivAt_const (𝕜:=ℝ) theta.1 (q m,m)).prodMk
        (hasFDerivAt_snd (𝕜:=ℝ) (p:=(q m,m)))).prodMk (hasFDerivAt_fst (𝕜:=ℝ) (p:=(q m,m))) using 1 <;> rfl
    have hd:=hdiff.hasFDerivAt.comp (q m,m) hi
    change (fderiv ℝ (F ∘ fun y:AtomicPoint r×ℝ=>((theta.1,y.2),y.1)) (q m,m)) (0,1)=_
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.comp_apply,fixedCouplingAssembly,
      ContinuousLinearMap.prod_apply,ContinuousLinearMap.snd,ContinuousLinearMap.fst,
      zero_apply,stationaryMassFunction,F,q]
    rfl
  have hd:=hdg.congr_of_eventuallyEq heq
  apply stationary_full_hessian_positive hf hq hz hA
  intro v hv
  rw [stationary_scalar_response_hessian hf hq hz hd]
  exact mul_pos (sq_pos_of_ne_zero hv) ((half_pos d.slope_pos).trans_le hMD.2)

end LimitingStandingData
end DepthPaper
