module

public import GeneralDepthPaper.StationaryCouplingC2

@[expose] public section


/-! The actual coupling curve is strictly decreasing. Its inverse lower
mass is an actual unique scalar root throughout the transition window. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 1800000

namespace LimitingStandingData
variable {Ξ:AdmissibleCovariance} {r:ℕ} {seed:AtomicPoint r}

def bifurcatingMass (d:LimitingStandingData Ξ seed) (p:ℕ) (lam:ℝ):ℝ:=
  intervalImplicitRoot (fun w:ℝ×ℝ=>w.1-d.couplingCurve p w.2) d.massLower 1 lam

theorem couplingCurve_slope_eventually (d:LimitingStandingData Ξ seed):
    ∀ᶠp:ℕ in atTop,∀heven:Even p,∀m∈Icc d.massLower 1,
      ContDiffAt ℝ ∞ (d.couplingCurve p) m ∧ deriv (d.couplingCurve p) m ≤ -d.slope := by
  obtain ⟨C,hC,A,c,hc,H⟩:=d.couplingCurve_C2_exponential_error
  obtain ⟨_,_,_,_,_,Hroot⟩:=d.couplingCurve_eventually
  have Hsmall:∀ᶠp:ℕ in atTop,C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) ≤ d.slope:=
    (tendsto_nat_polynomial_exp C c A hc).eventually (eventually_le_nhds d.slope_pos)
  filter_upwards [H,Hroot,Hsmall] with p hp hr hsmall heven m hm
  have hq:ContDiffAt ℝ ∞ (d.couplingCurve p) m:=(hr heven m hm).2.2.1
  have hell:=d.ell_smooth m hm
  have herror:=hp heven m hm 1 (by norm_num)
  rw [norm_iteratedFDeriv_one,←norm_deriv_eq_norm_fderiv] at herror
  rw [deriv_fun_sub (hq.differentiableAt (by simp)) (hell.differentiableAt (by simp)),Real.norm_eq_abs] at herror
  have hh:=le_abs_self (deriv (d.couplingCurve p) m-
    deriv (pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture)) m)
  exact ⟨hq,by linarith [d.ell_slope m hm]⟩

theorem bifurcatingMass_eventually (d:LimitingStandingData Ξ seed):
    ∀ᶠp:ℕ in atTop,∀heven:Even p,
      StrictAntiOn (d.couplingCurve p) (Icc d.massLower 1) ∧
      ∀lam∈Ioc (d.couplingCurve p 1)
        (pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) 1+d.couplingMargin),
        d.bifurcatingMass p lam∈Ioo d.massLower 1 ∧
        d.couplingCurve p (d.bifurcatingMass p lam)=lam ∧
        (∀m∈Icc d.massLower 1,d.couplingCurve p m=lam→m=d.bifurcatingMass p lam) := by
  obtain ⟨C,hC,A,c,hc,H⟩:=d.couplingCurve_eventually
  have Hsmall:∀ᶠp:ℕ in atTop,C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) < d.couplingMargin:=
    (tendsto_nat_polynomial_exp C c A hc).eventually (eventually_lt_nhds d.couplingMargin_pos)
  filter_upwards [H,d.couplingCurve_slope_eventually,Hsmall] with p hp hs hsmall heven
  have hreg (m:ℝ) (hm:m∈Icc d.massLower 1):ContDiffAt ℝ ∞ (d.couplingCurve p) m:=
    (hs heven m hm).1
  have hanti:StrictAntiOn (d.couplingCurve p) (Icc d.massLower 1):=by
    apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _)
      (fun m hm=>(hreg m hm).continuousAt.continuousWithinAt)
      (f':=deriv (d.couplingCurve p))
    · intro m hm
      rw [interior_Icc] at hm
      exact ((hreg m ⟨hm.1.le,hm.2.le⟩).differentiableAt (by simp)).hasDerivAt.hasDerivWithinAt
    · intro m hm
      rw [interior_Icc] at hm
      exact (hs heven m ⟨hm.1.le,hm.2.le⟩).2.trans_lt (by linarith [d.slope_pos])
  refine ⟨hanti,?_⟩
  intro lam hlam
  let G:ℝ×ℝ→ℝ:=fun w=>w.1-d.couplingCurve p w.2
  have hg (m:ℝ) (hm:m∈Icc d.massLower 1):ContDiffAt ℝ ∞ (fun u=>G (lam,u)) m:=
    contDiffAt_const.sub (hreg m hm)
  have hlow:G (lam,d.massLower) < 0:=by
    have herr:|d.couplingCurve p d.massLower-
        pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) d.massLower| < d.couplingMargin:=
      (hp heven d.massLower ⟨le_rfl,d.massLower_mem.2.le⟩).2.2.2.2.1.trans_lt hsmall
    have hh:=neg_le_abs (d.couplingCurve p d.massLower-
      pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) d.massLower)
    have hgap:=d.couplingMargin_gap
    dsimp only [G]
    linarith [hlam.2,d.couplingMargin_pos]
  have hhigh:0 < G (lam,1):=by dsimp [G];linarith [hlam.1]
  have hd (m:ℝ) (hm:m∈Icc d.massLower 1):0 < deriv (fun u=>G (lam,u)) m:=by
    rw [show (fun u=>G (lam,u))=(fun u=>lam-d.couplingCurve p u) by rfl,
      deriv_const_sub]
    have hh:=(hs heven m hm).2
    linarith [d.slope_pos]
  have hroot:=intervalImplicitRoot_spec G d.massLower_mem.2 lam hg hlow hhigh hd
  have hz:=hroot.2
  change lam-d.couplingCurve p (d.bifurcatingMass p lam)=0 at hz
  refine ⟨hroot.1,by linarith,?_⟩
  intro m hm hmroot
  apply hanti.injOn hm ⟨hroot.1.1.le,hroot.1.2.le⟩
  linarith

end LimitingStandingData
end GeneralDepthPaper
