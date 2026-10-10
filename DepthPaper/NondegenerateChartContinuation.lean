module

public import DepthPaper.AtomicContactStability
public import FourPapersCommon.PositiveHessianPersistence

@[expose] public section


/-! A continuous actual stationary chart near a nondegenerate optimizer
remains a nondegenerate optimizer. Neither minimization nor contact stability
is assumed of the continued charts. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
open FourPapersCommon
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

def atomicHessianFamily {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
    (F : SmoothCovarianceFamily Θ) (r : ℕ) (p : Θ×AtomicPoint r) :
    AtomicPoint r→L[ℝ]AtomicPoint r→L[ℝ]ℝ :=
  fderiv ℝ (atomicGradientFamily F r) p ∘L ContinuousLinearMap.inr ℝ Θ (AtomicPoint r)

namespace SmoothCovarianceFamily
variable {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]

theorem continuousAt_atomicHessianFamily (F : SmoothCovarianceFamily Θ) {r : ℕ}
    {θ : Θ} (hθ : θ∈F.domain) (z : AtomicPoint r) (hz : IsAtomicPoint z) :
    ContinuousAt (atomicHessianFamily F r) (θ,z) :=
  ((F.contDiffAt_atomicGradientFamily hθ z hz).fderiv_right (m:=∞) (by simp)).continuousAt.clm_comp
    continuousAt_const

theorem eventually_nondegenerate_stationary_chart (F : SmoothCovarianceFamily Θ)
    {θ : Θ} (hθ : θ∈F.domain) {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (hbase : Nondegenerate (F.covariance θ) z hz)
    (zF : Θ→AtomicPoint r) (hvalue : zF θ=z) (hcont : ContinuousAt zF θ)
    (hs : ∀ᶠt in 𝓝 θ,atomicGradientFamily F r (t,zF t)=0) :
    ∀ᶠt in 𝓝 θ,∀ht:IsAtomicPoint (zF t),Nondegenerate (F.covariance t) (zF t) ht := by
  have hv : ∀ᶠt in 𝓝 θ,IsAtomicPoint (zF t) := by
    have he:=hcont ((isOpen_atomic_domain r).mem_nhds (show zF θ∈{z:AtomicPoint r|IsAtomicPoint z} by
      change IsAtomicPoint (zF θ);rw [hvalue];exact hz))
    exact he
  have hg:=F.eventually_stationary_contact_geometry hθ z hz ⟨hbase.2.1,hbase.2.2.1⟩
    zF hvalue hcont (hv.and hs)
  have hB : ∀v:AtomicPoint r,v≠0→0 < atomicHessianFamily F r (θ,z) v v := by
    rw [atomicHessianFamily,F.atomicGradientFamily_partial_hessian hθ z hz]
    exact hbase.2.2.2
  have hH : ContinuousAt (fun t=>atomicHessianFamily F r (t,zF t)) θ := by
    have hc:=F.continuousAt_atomicHessianFamily hθ z hz
    have hi : ContinuousAt (fun t=>(t,zF t)) θ := continuousAt_id.prodMk hcont
    have hc' : ContinuousAt (atomicHessianFamily F r) (θ,zF θ) := by simpa only [hvalue] using hc
    exact hc'.comp (f:=fun t=>(t,zF t)) hi
  have hp : ∀ᶠt in 𝓝 θ,∀v:AtomicPoint r,v≠0→0 < atomicHessianFamily F r (t,zF t) v v := by
    have he : ∀ᶠB in 𝓝 (atomicHessianFamily F r (θ,zF θ)),∀v:AtomicPoint r,v≠0→0 < B v v :=
      isOpen_positive_hessians.mem_nhds (by
        change ∀v:AtomicPoint r,v≠0→0 < atomicHessianFamily F r (θ,zF θ) v v
        simpa only [hvalue] using hB)
    exact hH.tendsto.eventually he
  filter_upwards [hg,hp,F.isOpen_domain.mem_nhds hθ] with t ht hp htd
  intro hzt
  have hgeom:=ht hzt
  refine ⟨hgeom.isMinimizer,hgeom.1,hgeom.2,?_⟩
  rw [positiveAtomicHessian,←F.atomicGradientFamily_partial_hessian htd (zF t) hzt]
  exact hp

end SmoothCovarianceFamily
end DepthPaper
