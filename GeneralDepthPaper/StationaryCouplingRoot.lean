module

public import GeneralDepthPaper.StationaryMassC2
public import GeneralDepthPaper.IntervalRootLocalSmooth

@[expose] public section


/-! The actual mass stationarity equation has one smooth coupling root
throughout the constructed mass window. No root or derivative estimate is
assumed: both follow from the genuine C² reduced-functional estimates. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 2300000
set_option maxSynthPendingDepth 64

namespace LimitingStandingData
variable {Ξ:AdmissibleCovariance} {r:ℕ} {seed:AtomicPoint r}

def couplingRootEquation (d:LimitingStandingData Ξ seed) (p:ℕ) (w:ℝ×ℝ):ℝ:=
  d.stationaryMassFunction p (w.2,w.1)

def couplingCurve (d:LimitingStandingData Ξ seed) (p:ℕ):ℝ→ℝ:=
  intervalImplicitRoot (d.couplingRootEquation p) d.couplingLower d.couplingUpper

theorem coupling_window_strict (d:LimitingStandingData Ξ seed):d.couplingLower < d.couplingUpper := by
  have hanti:=d.ell_strictAnti ⟨le_rfl,d.massLower_mem.2.le⟩
    ⟨d.massLower_mem.2.le,le_rfl⟩ d.massLower_mem.2
  dsimp only [couplingLower,couplingUpper]
  linarith [d.couplingMargin_pos]

theorem stationaryMassFunction_coupling_partial_error
    (d:LimitingStandingData Ξ seed) (p:ℕ) (theta:ℝ×ℝ) (ht:theta∈d.parameterWindow)
    (hf:ContDiffAt ℝ ∞ (d.stationaryMassFunction p) theta)
    {ε:ℝ} (hε:‖iteratedFDeriv ℝ 1 (fun u:ℝ×ℝ=>d.stationaryMassFunction p u-
      (u.1-pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) u.2)/2) theta‖ ≤ ε) :
    |fderiv ℝ (d.stationaryMassFunction p) theta (1,0)-1/2| ≤ ε := by
  let g:ℝ×ℝ→ℝ:=fun u=>(u.1-pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) u.2)/2
  have hg:ContDiffAt ℝ ∞ g theta :=
    (contDiffAt_fst.sub ((d.ell_smooth theta.2 ht.2).comp theta contDiffAt_snd)).div_const 2
  have hi:HasDerivAt (fun t:ℝ=>(t,theta.2)) (1,0) theta.1:=
    (hasDerivAt_id theta.1).prodMk (hasDerivAt_const theta.1 theta.2)
  have hc:=(hf.sub hg).differentiableAt (by simp)
  have hd:=hc.hasFDerivAt.comp_hasDerivAt theta.1 hi
  have hdf:=((hf.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt theta.1 hi).sub
    (((hasDerivAt_id theta.1).sub_const
      (pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) theta.2)).div_const 2)
  have he:fderiv ℝ (fun u=>d.stationaryMassFunction p u-g u) theta (1,0)=
      fderiv ℝ (d.stationaryMassFunction p) theta (1,0)-1/2:=hd.unique hdf
  rw [←he,←Real.norm_eq_abs]
  have hh:=(fderiv ℝ (fun u=>d.stationaryMassFunction p u-g u) theta).le_opNorm ((1,0):ℝ×ℝ)
  simp only [Prod.norm_def,Real.norm_eq_abs,abs_one,norm_zero,max_eq_left zero_le_one,mul_one] at hh
  exact hh.trans (by simpa only [norm_iteratedFDeriv_one] using hε)

theorem couplingCurve_eventually (d:LimitingStandingData Ξ seed):
    ∃C:ℝ,0 < C ∧ ∃A:ℕ,∃c:ℝ,0 < c ∧
      ∀ᶠp:ℕ in atTop,∀heven:Even p,∀m∈Icc d.massLower 1,
        d.couplingCurve p m∈Ioo d.couplingLower d.couplingUpper ∧
        d.stationaryMassFunction p (d.couplingCurve p m,m)=0 ∧
        ContDiffAt ℝ ∞ (d.couplingCurve p) m ∧
        (∀ᶠu in 𝓝 m,d.couplingCurve p u∈Ioo d.couplingLower d.couplingUpper ∧
          d.stationaryMassFunction p (d.couplingCurve p u,u)=0) ∧
        |d.couplingCurve p m-pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) m| ≤
          C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) ∧
        (∀lam∈Icc d.couplingLower d.couplingUpper,
          d.stationaryMassFunction p (lam,m)=0→lam=d.couplingCurve p m) := by
  obtain ⟨C,hC,A,c,hc,H⟩:=d.stationaryMassFunction_C2_exponential_error
  have Hsmall:∀ᶠp:ℕ in atTop,C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) < min d.couplingMargin (1/4) :=
    (tendsto_nat_polynomial_exp C c A hc).eventually
      (eventually_lt_nhds (lt_min d.couplingMargin_pos (by norm_num)))
  refine ⟨2*C,by positivity,A,c,hc,?_⟩
  filter_upwards [H,Hsmall] with p hp hsmall heven m hm
  let G:=d.couplingRootEquation p
  have hg (lam:ℝ) (hl:lam∈Icc d.couplingLower d.couplingUpper):
      ContDiffAt ℝ ∞ G (m,lam):=
    (hp heven (lam,m) ⟨hl,hm⟩).1.comp (m,lam) (contDiffAt_snd.prodMk contDiffAt_fst)
  have hslice (lam:ℝ) (hl:lam∈Icc d.couplingLower d.couplingUpper):
      ContDiffAt ℝ ∞ (fun t=>G (m,t)) lam:=
    (hg lam hl).comp lam (contDiffAt_const.prodMk contDiffAt_id)
  have hvalue (lam:ℝ) (hl:lam∈Icc d.couplingLower d.couplingUpper):
      |G (m,lam)-(lam-pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) m)/2| ≤
        C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) := by
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,G,couplingRootEquation] using
      (hp heven (lam,m) ⟨hl,hm⟩).2 0 (by norm_num)
  have hpartial (lam:ℝ) (hl:lam∈Icc d.couplingLower d.couplingUpper):
      0 < deriv (fun t=>G (m,t)) lam := by
    have hbase:=hp heven (lam,m) ⟨hl,hm⟩
    have herr:=d.stationaryMassFunction_coupling_partial_error p (lam,m) ⟨hl,hm⟩
      hbase.1 (hbase.2 1 (by norm_num))
    have hd:HasDerivAt (fun t=>G (m,t))
        (fderiv ℝ (d.stationaryMassFunction p) (lam,m) (1,0)) lam :=
      (hbase.1.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt lam
        ((hasDerivAt_id lam).prodMk (hasDerivAt_const lam m))
    rw [hd.deriv]
    have hh:=neg_le_abs (fderiv ℝ (d.stationaryMassFunction p) (lam,m) (1,0)-1/2)
    have hb:=hsmall.trans_le (min_le_right _ _)
    linarith
  have hanti:=d.ell_strictAnti.antitoneOn
  have hlo:G (m,d.couplingLower) < 0 := by
    have hh:=hvalue d.couplingLower ⟨le_rfl,d.couplingLower_le_upper⟩
    have hb:=hsmall.trans_le (min_le_left _ _)
    have hell:=hanti hm ⟨d.massLower_mem.2.le,le_rfl⟩ hm.2
    have habs:=le_abs_self (G (m,d.couplingLower)-
      (d.couplingLower-pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) m)/2)
    dsimp only [couplingLower] at hh habs
    change G (m,pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) 1-2*d.couplingMargin) < 0
    linarith
  have hhi:0 < G (m,d.couplingUpper) := by
    have hh:=hvalue d.couplingUpper ⟨d.couplingLower_le_upper,le_rfl⟩
    have hb:=hsmall.trans_le (min_le_left _ _)
    have hell:=hanti ⟨le_rfl,d.massLower_mem.2.le⟩ hm hm.1
    have habs:=neg_le_abs (G (m,d.couplingUpper)-
      (d.couplingUpper-pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) m)/2)
    dsimp only [couplingUpper] at hh habs
    change 0 < G (m,pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) d.massLower+2*d.couplingMargin)
    linarith
  have hroot:=intervalImplicitRoot_spec G d.coupling_window_strict m hslice hlo hhi hpartial
  have hpos (lam:ℝ) (hl:lam∈Icc d.couplingLower d.couplingUpper):
      0 < fderiv ℝ G (m,lam) (0,1) := by
    rw [←interval_partial_derivative_eq G m lam (hg lam hl)]
    exact hpartial lam hl
  have hsm:=intervalImplicitRoot_local_smooth_spec G d.coupling_window_strict m hg hpos hroot.1 hroot.2
  refine ⟨hroot.1,hroot.2,hsm.1,hsm.2,?_,?_⟩
  · have hh:=hvalue (d.couplingCurve p m) ⟨hroot.1.1.le,hroot.1.2.le⟩
    have hz:G (m,d.couplingCurve p m)=0:=hroot.2
    rw [hz,zero_sub,abs_neg,abs_div,abs_of_pos (show (0:ℝ) < 2 by norm_num)] at hh
    calc
      _ ≤ 2*(C*(p:ℝ)^A*Real.exp (-c*(p:ℝ))) := by linarith
      _ = _ := by ring
  · intro lam hl hz
    have hli:lam∈Ioo d.couplingLower d.couplingUpper := by
      constructor
      · exact lt_of_le_of_ne hl.1 (by intro he;subst lam;exact ne_of_lt hlo hz)
      · exact lt_of_le_of_ne hl.2 (by intro he;subst lam;exact ne_of_gt hhi hz)
    exact (intervalImplicitRoot_unique G d.coupling_window_strict m hslice hlo hhi hpartial hli hz).symm

end LimitingStandingData
end GeneralDepthPaper
