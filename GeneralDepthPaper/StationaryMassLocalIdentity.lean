module

public import GeneralDepthPaper.StationaryMassJetBounds
public import GeneralDepthPaper.StationaryLowerC2

@[expose] public section


/-! The true pressure envelope identity holds on an ordinary mass
neighborhood, so its ordinary endpoint jets agree with the actual branch. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 1600000
namespace LimitingStandingData
variable {Ξ:AdmissibleCovariance} {r:ℕ} {seed:AtomicPoint r}

theorem pressure_smooth_on_massDomain (d:LimitingStandingData Ξ seed)
    (m:ℝ) (hm:m∈d.massDomain) (hmp:0 < m) :
    ContDiffAt ℝ ∞ (scaledThermodynamicPressure Ξ.toEvenMixture) m := by
  let F:=temperatureCovarianceFamily Ξ
  obtain ⟨hz,hnd⟩:=d.branch_nondegenerate_domain m hm
  have hc:=((F.finite_step_regularity r).contDiffAt
    ((F.isOpen_domain.prod (isOpen_atomic_domain r)).mem_nhds
      (show (m,d.branch m)∈F.domain×ˢ{z:AtomicPoint r|IsAtomicPoint z} from ⟨hmp,hz⟩))).comp m
        (contDiffAt_id.prodMk (d.branch_smooth.contDiffAt (d.massDomain_open.mem_nhds hm)))
  apply hc.congr_of_eventuallyEq
  filter_upwards [d.massDomain_open.mem_nhds hm,isOpen_Ioi.mem_nhds hmp] with t ht htp
  obtain ⟨hzt,hndt⟩:=d.branch_nondegenerate_domain t ht
  change scaledThermodynamicPressure Ξ.toEvenMixture t=
    atomicFunctionalExtension (F.covariance t) r (d.branch t)
  rw [scaledThermodynamicPressure_eq_temperature_parisiPressure Ξ t htp.ne',
    atomicFunctionalExtension_eq _ (d.branch t) hzt,
    parisiMinimizer_unique _ (atomicMeasure (d.branch t) hzt) hndt.1,parisiMinimizer_value]

theorem limitingMassJetField_eq_on_massDomain (d:LimitingStandingData Ξ seed)
    (theta:ℝ×ℝ) (hm:theta.2∈d.massDomain) (hmp:0 < theta.2) :
    d.limitingMassJetField (theta,d.branch theta.2)=
      (theta.1-pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) theta.2)/2 := by
  obtain ⟨hz,hnd⟩:=d.branch_nondegenerate_domain theta.2 hm
  have hzero:fderiv ℝ (fun y=>limitingAtomicObjective Ξ r theta.1 (y,theta.2)) (d.branch theta.2)=0 := by
    rw [fderiv_limitingAtomicObjective_locations Ξ _ hz theta.2 hmp theta.1,
      fderiv_limitingAtomicPhi_locations Ξ _ hz theta.2 hmp,
      fderiv_atomicFunctional_eq_zero_of_minimizer _ (d.branch theta.2) hz hnd.1,smul_zero]
  have he:(fun t=>limitingAtomicObjective Ξ r theta.1 (d.branch t,t))=ᶠ[𝓝 theta.2]
      limitingPressureObjective (scaledThermodynamicPressure Ξ.toEvenMixture) theta.1 := by
    filter_upwards [d.massDomain_open.mem_nhds hm,isOpen_Ioi.mem_nhds hmp] with t ht htp
    obtain ⟨hzt,hndt⟩:=d.branch_nondegenerate_domain t ht
    exact limitingAtomicObjective_eq_J_of_minimizer Ξ (d.branch t) hzt t htp hndt.1 theta.1
  have ht:=(hasDerivAt_limitingPressureObjective (scaledThermodynamicPressure Ξ.toEvenMixture)
    theta.1 theta.2 hmp.ne' ((d.pressure_smooth_on_massDomain theta.2 hm hmp).differentiableAt
      (by simp))).congr_of_eventuallyEq he
  have hfreeze:=hasDerivAt_frozen_parameter_of_stationary (limitingAtomicObjective Ξ r theta.1)
    d.branch theta.2 _
    ((contDiffAt_limitingAtomicObjective Ξ _ hz theta.2 hmp theta.1).differentiableAt (by simp))
    ((d.branch_smooth.contDiffAt (d.massDomain_open.mem_nhds hm)).differentiableAt (by simp))
    hzero ht
  have hf:=contDiffAt_stationaryLimitingObjective Ξ _ hz theta hmp
  have hi:HasDerivAt (fun t:ℝ=>((theta.1,t),d.branch theta.2)) ((0,1),0) theta.2 :=
    ((hasDerivAt_const theta.2 theta.1).prodMk (hasDerivAt_id theta.2)).prodMk
      (hasDerivAt_const theta.2 (d.branch theta.2))
  have hc:=(hf.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt theta.2 hi
  exact hc.unique hfreeze

theorem limitingMassJetField_branch_eventuallyEq (d:LimitingStandingData Ξ seed)
    (theta:ℝ×ℝ) (ht:theta∈d.parameterWindow) :
    (fun u:ℝ×ℝ=>d.limitingMassJetField (u,d.branch u.2))=ᶠ[𝓝 theta]
      (fun u=>(u.1-pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) u.2)/2) := by
  filter_upwards [continuousAt_snd.eventually
    (d.massDomain_open.mem_nhds (d.massWindow_subset ht.2)),
    continuousAt_snd.eventually (isOpen_Ioi.mem_nhds
      (d.massLower_mem.1.trans_le ht.2.1))] with u hu hm
  exact d.limitingMassJetField_eq_on_massDomain u hu hm

end LimitingStandingData
end GeneralDepthPaper
