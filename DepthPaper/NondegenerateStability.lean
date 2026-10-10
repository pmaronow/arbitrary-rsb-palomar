module

public import DepthPaper.NondegenerateChartContinuation
public import FourPapersCommon.SmoothStationaryNeighborhood

@[expose] public section


/-! Literal Proposition 2.7: every nondegenerate finite-depth optimizer
continues smoothly and remains the actual nondegenerate Parisi optimizer. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
open FourPapersCommon
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

namespace SmoothCovarianceFamily
variable {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]

theorem nondegenerate_stability (F : SmoothCovarianceFamily Θ) {θ : Θ}
    (hθ : θ∈F.domain) {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (hbase : Nondegenerate (F.covariance θ) z hz) :
    ∃V:Set Θ,IsOpen V ∧ θ∈V ∧ V⊆F.domain ∧ ∃zF:Θ→AtomicPoint r,
      zF θ=z ∧ ContDiffOn ℝ ∞ zF V ∧
      ∀t∈V,∃ht:IsAtomicPoint (zF t),Nondegenerate (F.covariance t) (zF t) ht := by
  let U:Set (Θ×AtomicPoint r):=
    (F.domain×ˢ{z:AtomicPoint r|IsAtomicPoint z})∩
      {p|∀v:AtomicPoint r,v≠0→0 < atomicHessianFamily F r p v v}
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    have hD : (F.domain×ˢ{z:AtomicPoint r|IsAtomicPoint z})∈𝓝 p :=
      (F.isOpen_domain.prod (isOpen_atomic_domain r)).mem_nhds hp.1
    have hP : {p|∀v:AtomicPoint r,v≠0→0 < atomicHessianFamily F r p v v}∈𝓝 p := by
      have hc:=F.continuousAt_atomicHessianFamily hp.1.1 p.2 hp.1.2
      exact hc (isOpen_positive_hessians.mem_nhds hp.2)
    exact inter_mem hD hP
  have hG : ContDiffOn ℝ ∞ (atomicGradientFamily F r) U := by
    intro p hp
    exact (F.contDiffAt_atomicGradientFamily hp.1.1 p.2 hp.1.2).contDiffWithinAt
  have hp : (θ,z)∈U := by
    refine ⟨⟨hθ,hz⟩,?_⟩
    change ∀v:AtomicPoint r,v≠0→0 < atomicHessianFamily F r (θ,z) v v
    rw [atomicHessianFamily,F.atomicGradientFamily_partial_hessian hθ z hz]
    exact hbase.2.2.2
  have hzero : atomicGradientFamily F r (θ,z)=0 :=
    fderiv_atomicFunctional_eq_zero_of_minimizer _ z hz hbase.1
  obtain ⟨zF,V,hV,hθV,hvalue,hsmooth,hdata⟩ :=
    exists_smooth_stationary_neighborhood (atomicGradientFamily F r) U hU hG (θ,z) hp hzero
      (fun p hp=>hp.2)
  have hcont : ContinuousAt zF θ :=
    (hsmooth.contDiffAt (hV.mem_nhds hθV)).continuousAt
  have hv : ∀ᶠt in 𝓝 θ,t∈V := hV.mem_nhds hθV
  have hs : ∀ᶠt in 𝓝 θ,atomicGradientFamily F r (t,zF t)=0 := by
    filter_upwards [hv] with t ht
    exact (hdata t ht).2
  have hn:=F.eventually_nondegenerate_stationary_chart hθ z hz hbase zF hvalue hcont hs
  obtain ⟨W,hWsub,hW,hθW⟩:=mem_nhds_iff.mp (hv.and hn)
  refine ⟨W,hW,hθW,?_,zF,hvalue,hsmooth.mono (fun t ht=>(hWsub ht).1),?_⟩
  · intro t ht
    exact (hdata t (hWsub ht).1).1.1.1
  · intro t ht
    have hzt : IsAtomicPoint (zF t) := (hdata t (hWsub ht).1).1.1.2
    exact ⟨hzt,(hWsub ht).2 hzt⟩

end SmoothCovarianceFamily
end DepthPaper
