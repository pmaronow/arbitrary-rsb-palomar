module

public import DepthPaper.EndpointRootProposition
public import DepthPaper.PartialJetBounds
public import DepthPaper.LimitingHessianBox

@[expose] public section


/-! The actual stationary-coordinate objective is a norm-preserving
reordering of the already verified reduced endpoint functional. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 64

def stationaryParameterAssembly {r:ℕ} :
    ((ℝ×ℝ)×AtomicPoint r)→L[ℝ] HighDegreeLowerParameter r where
  toFun w:=(w.2,(w.1.2,w.1.1))
  map_add' u v:=by rfl
  map_smul' a u:=by rfl
  cont:=by fun_prop

theorem norm_stationaryParameterAssembly_le {r:ℕ} :
    ‖stationaryParameterAssembly (r:=r)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro w
  simp only [stationaryParameterAssembly,ContinuousLinearMap.coe_mk',LinearMap.coe_mk,
    AddHom.coe_mk,Prod.norm_def,one_mul]
  exact max_le (le_max_right _ _) (max_le
    ((le_max_right _ _).trans (le_max_left _ _))
    ((le_max_left _ _).trans (le_max_left _ _)))

def stationaryReducedObjective (Ξ:AdmissibleCovariance) {r:ℕ} (p:ℕ) (qc cQ CQ:ℝ)
    (w:(ℝ×ℝ)×AtomicPoint r) : ℝ :=
  reducedEndpointFunctional Ξ p qc cQ CQ (stationaryParameterAssembly w)

def stationaryLimitingObjective (Ξ:AdmissibleCovariance) {r:ℕ}
    (w:(ℝ×ℝ)×AtomicPoint r) : ℝ := limitingObjectiveCore Ξ (stationaryParameterAssembly w)

theorem contDiffAt_stationaryLimitingObjective (Ξ:AdmissibleCovariance) {r:ℕ}
    (z:AtomicPoint r) (hz:IsAtomicPoint z) (theta:ℝ×ℝ) (hm:0 < theta.2) :
    ContDiffAt ℝ ∞ (stationaryLimitingObjective Ξ) (theta,z) := by
  have h:=contDiffAt_limitingObjectiveCore Ξ
    (theta:=stationaryParameterAssembly (theta,z)) hz hm
  exact h.comp (theta,z) stationaryParameterAssembly.contDiff.contDiffAt

theorem stationaryLimitingObjective_gradient (Ξ:AdmissibleCovariance) {r:ℕ}
    (z:AtomicPoint r) (hz:IsAtomicPoint z) (theta:ℝ×ℝ) (hm:0 < theta.2) :
    partialGradient (stationaryLimitingObjective Ξ) theta z=
      fderiv ℝ (fun y=>limitingAtomicPhi Ξ r (y,theta.2)) z :=
  fderiv_limitingAtomicObjective_locations Ξ z hz theta.2 hm theta.1

theorem stationaryLimitingObjective_hessian (Ξ:AdmissibleCovariance) {r:ℕ}
    (z:AtomicPoint r) (hz:IsAtomicPoint z) (theta:ℝ×ℝ) (hm:0 < theta.2) :
    partialHessian (stationaryLimitingObjective Ξ) theta z=limitingHessianField Ξ r (z,theta.2) := by
  have he:(partialGradient (stationaryLimitingObjective Ξ) theta)=ᶠ[𝓝 z]
      (fun y=>fderiv ℝ (fun w=>limitingAtomicPhi Ξ r (w,theta.2)) y) := by
    filter_upwards [(isOpen_atomic_domain r).mem_nhds hz] with y hy
    exact stationaryLimitingObjective_gradient Ξ y hy theta hm
  rw [partialHessian,he.fderiv_eq,limitingAtomicPhi_hessian_eq Ξ z hz theta.2 hm]

theorem norm_stationaryObjective_difference_jet_le (Ξ:AdmissibleCovariance) {r:ℕ}
    (p:ℕ) (qc cQ CQ:ℝ) (theta:ℝ×ℝ) (z:AtomicPoint r) (j:ℕ)
    (hf:ContDiffAt ℝ ∞ (fun u:HighDegreeLowerParameter r=>
      reducedEndpointFunctional Ξ p qc cQ CQ u-limitingObjectiveCore Ξ u)
      (stationaryParameterAssembly (theta,z))) :
    ‖iteratedFDeriv ℝ j (fun w=>stationaryReducedObjective Ξ p qc cQ CQ w-
      stationaryLimitingObjective Ξ w) (theta,z)‖ ≤
      ‖iteratedFDeriv ℝ j (fun u:HighDegreeLowerParameter r=>
        reducedEndpointFunctional Ξ p qc cQ CQ u-limitingObjectiveCore Ξ u)
        (stationaryParameterAssembly (theta,z))‖ :=
  norm_iteratedFDeriv_comp_CLM_contraction stationaryParameterAssembly
    norm_stationaryParameterAssembly_le hf j

end DepthPaper
