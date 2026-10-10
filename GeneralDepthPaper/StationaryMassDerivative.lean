module

public import GeneralDepthPaper.StationaryLowerActual

@[expose] public section


/-! The limiting partial mass derivative is the actual pressure envelope,
and the finite-degree mass function is the actual reduced-functional jet. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 64

namespace LimitingStandingData
variable {Ξ:AdmissibleCovariance} {r:ℕ} {seed:AtomicPoint r}

def stationaryMassFunction (d:LimitingStandingData Ξ seed) (p:ℕ) (theta:ℝ×ℝ) : ℝ :=
  fderiv ℝ (stationaryReducedObjective Ξ p d.cutoff d.stripRateLower d.stripRateUpper)
    (theta,d.stationaryBranch p theta) ((0,1),0)

theorem limiting_frozen_mass_derivative (d:LimitingStandingData Ξ seed)
    (lam m:ℝ) (hm:m∈Icc d.massLower 1) :
    HasDerivAt (fun t=>limitingAtomicObjective Ξ r lam (d.branch m,t))
      ((lam-pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) m)/2) m := by
  have hmp:0 < m := d.massLower_mem.1.trans_le hm.1
  have hmV:m∈d.massDomain := d.massWindow_subset hm
  obtain ⟨hzm,hndm⟩:=d.branch_nondegenerate m hm
  have hzero:fderiv ℝ (fun y=>limitingAtomicObjective Ξ r lam (y,m)) (d.branch m)=0 := by
    rw [fderiv_limitingAtomicObjective_locations Ξ _ hzm m hmp lam]
    exact d.branch_stationary m hm
  have he:(fun t=>limitingAtomicObjective Ξ r lam (d.branch t,t))=ᶠ[𝓝 m]
      limitingPressureObjective (scaledThermodynamicPressure Ξ.toEvenMixture) lam := by
    filter_upwards [d.massDomain_open.mem_nhds hmV,isOpen_Ioi.mem_nhds hmp] with t ht htp
    obtain ⟨hzt,hndt⟩:=d.branch_nondegenerate_domain t ht
    exact limitingAtomicObjective_eq_J_of_minimizer Ξ (d.branch t) hzt t htp hndt.1 lam
  have ht:=(hasDerivAt_limitingPressureObjective (scaledThermodynamicPressure Ξ.toEvenMixture)
    lam m hmp.ne' ((d.pressure_smooth m hm).differentiableAt (by simp))).congr_of_eventuallyEq he
  exact hasDerivAt_frozen_parameter_of_stationary (limitingAtomicObjective Ξ r lam) d.branch m _
    ((contDiffAt_limitingAtomicObjective Ξ (d.branch m) hzm m hmp lam).differentiableAt (by simp))
    ((d.branch_smooth.contDiffAt (d.massDomain_open.mem_nhds hmV)).differentiableAt (by simp))
    hzero ht

theorem limiting_mass_jet_eq (d:LimitingStandingData Ξ seed) (theta:ℝ×ℝ)
    (hm:theta.2∈Icc d.massLower 1) :
    fderiv ℝ (stationaryLimitingObjective Ξ) (theta,d.branch theta.2) ((0,1),0)=
      (theta.1-pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) theta.2)/2 := by
  obtain ⟨hz,_⟩:=d.branch_nondegenerate theta.2 hm
  have hf:=contDiffAt_stationaryLimitingObjective Ξ (d.branch theta.2) hz theta
    (d.massLower_mem.1.trans_le hm.1)
  have hi:HasDerivAt (fun t:ℝ=>((theta.1,t),d.branch theta.2)) ((0,1),0) theta.2 :=
    ((hasDerivAt_const theta.2 theta.1).prodMk (hasDerivAt_id theta.2)).prodMk
      (hasDerivAt_const theta.2 (d.branch theta.2))
  have hc:=(hf.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt theta.2 hi
  exact hc.unique (d.limiting_frozen_mass_derivative theta.1 theta.2 hm)

end LimitingStandingData
end GeneralDepthPaper
