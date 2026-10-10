module

public import GeneralDepthPaper.LimitingAtomicObjective

@[expose] public section


/-! Literal Proposition 3.3 for the actual nondegenerate finite-depth
temperature branch and the actual thermodynamic pressure. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem limitingAtomicObjective_eq_J_of_minimizer (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : 0 < m)
    (hmin : IsParisiMinimizer ((temperatureCovarianceFamily Ξ).covariance m) (atomicMeasure z hz))
    (lam : ℝ) :
    limitingAtomicObjective Ξ r lam (z,m)=
      limitingPressureObjective (scaledThermodynamicPressure Ξ.toEvenMixture) lam m := by
  rw [limitingAtomicObjective,limitingAtomicPhi,
    atomicFunctionalExtension_eq _ z hz,
    parisiMinimizer_unique _ (atomicMeasure z hz) hmin,parisiMinimizer_value,
    ←scaledThermodynamicPressure_eq_temperature_parisiPressure Ξ m hm.ne']
  rfl

theorem limiting_corner (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (hnd : Nondegenerate Ξ z hz) :
    ∃m1∈Ioo (0:ℝ) 1,∃c>0,∃zF:ℝ→AtomicPoint r,
      zF 1=z ∧ ContDiffOn ℝ ∞ zF (Icc m1 1) ∧
      (∀m∈Icc m1 1,∃hzm:IsAtomicPoint (zF m),
        Nondegenerate ((temperatureCovarianceFamily Ξ).covariance m) (zF m) hzm ∧
        ∀lam:ℝ,
          limitingPressureObjective (scaledThermodynamicPressure Ξ.toEvenMixture) lam m=
            limitingAtomicObjective Ξ r lam (zF m,m) ∧
          fderiv ℝ (fun y=>limitingAtomicObjective Ξ r lam (y,m)) (zF m)=0 ∧
          HasDerivAt (fun t=>limitingAtomicObjective Ξ r lam (zF m,t))
            ((lam-pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) m)/2) m ∧
          (∀v:AtomicPoint r,v≠0→
            0 < (fderiv ℝ (fun y=>fderiv ℝ (fun w=>limitingAtomicPhi Ξ r (w,m)) y) (zF m) v) v) ∧
          deriv (pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture)) m≤-2*c) ∧
      deriv (pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture)) 1=
        -2*pressureKappa (scaledThermodynamicPressure Ξ.toEvenMixture) ∧
      0 < pressureKappa (scaledThermodynamicPressure Ξ.toEvenMixture) := by
  let F:=temperatureCovarianceFamily Ξ
  let p:=scaledThermodynamicPressure Ξ.toEvenMixture
  have hbase : Nondegenerate (F.covariance 1) z hz := by
    simpa only [F,temperatureCovarianceFamily_one] using hnd
  obtain ⟨V0,hV0,h1V0,hVD,zF,hvalue,hsm,hdata⟩:=F.nondegenerate_stability
    (θ:=1) (by norm_num [F,temperatureCovarianceFamily]) z hz hbase
  obtain ⟨Vp,hVp,h1Vp,hVpD,hP⟩:=exists_smooth_temperature_pressure Ξ z hz hnd
  have hentropy : 0 < pressureEntropy p 1 := by
    simpa only [pressureEntropy,thermodynamicEntropy,p,one_mul] using
      (positive_entropy Ξ z hz hnd).2.2.1
  obtain ⟨m1,hm1,c,hc,hM,hEll,hEll1⟩:=exists_limiting_mass_window p (V0∩Vp)
    (hV0.inter hVp) ⟨h1V0,h1Vp⟩ (hP.mono inter_subset_right)
    (convexOn_scaledThermodynamicPressure _) hentropy
  have hK : 0 < pressureKappa p := pressureKappa_pos p (convexOn_scaledThermodynamicPressure _)
    ((contDiffAt_temperature_pressure Ξ z hz hnd).of_le (by simp)) hentropy
  refine ⟨m1,hm1,c,hc,zF,hvalue,hsm.mono (fun m hm=>(hM hm).1),?_,hEll1,hK⟩
  intro m hm
  have hmV : m∈V0 := (hM hm).1
  have hmP : m∈Vp := (hM hm).2
  have hmp : 0 < m := hVD hmV
  obtain ⟨hzm,hndm⟩:=hdata m hmV
  refine ⟨hzm,hndm,?_⟩
  intro lam
  have hzeroA:=fderiv_atomicFunctional_eq_zero_of_minimizer (F.covariance m) (zF m) hzm hndm.1
  have hzero : fderiv ℝ (fun y=>limitingAtomicObjective Ξ r lam (y,m)) (zF m)=0 := by
    rw [fderiv_limitingAtomicObjective_locations Ξ (zF m) hzm m hmp lam,
      fderiv_limitingAtomicPhi_locations Ξ (zF m) hzm m hmp,hzeroA,smul_zero]
  have hpd : DifferentiableAt ℝ p m := (hP.contDiffAt (hVp.mem_nhds hmP)).differentiableAt
    (by norm_num)
  have he : (fun t=>limitingAtomicObjective Ξ r lam (zF t,t))=ᶠ[𝓝 m]
      limitingPressureObjective p lam := by
    filter_upwards [hV0.mem_nhds hmV] with t ht
    obtain ⟨hzt,hnt⟩:=hdata t ht
    exact limitingAtomicObjective_eq_J_of_minimizer Ξ (zF t) hzt t (hVD ht) hnt.1 lam
  have htotal := (hasDerivAt_limitingPressureObjective p lam m hmp.ne' hpd).congr_of_eventuallyEq he
  have hpartial:=hasDerivAt_frozen_parameter_of_stationary (limitingAtomicObjective Ξ r lam) zF m
    ((lam-pressureEll p m)/2)
    ((contDiffAt_limitingAtomicObjective Ξ (zF m) hzm m hmp lam).differentiableAt (by norm_num))
    ((hsm.contDiffAt (hV0.mem_nhds hmV)).differentiableAt (by norm_num)) hzero htotal
  exact ⟨(limitingAtomicObjective_eq_J_of_minimizer Ξ (zF m) hzm m hmp hndm.1 lam).symm,
    hzero,hpartial,positive_limitingAtomicPhi_hessian Ξ (zF m) hzm m hmp hndm.2.2.2.1,hEll m hm⟩

end GeneralDepthPaper
