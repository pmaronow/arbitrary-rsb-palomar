module

public import DepthPaper.StationaryBranchProposition
public import DepthPaper.BranchMassSmallO
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

@[expose] public section


/-! Actual inverse-mass asymptotics for the constructed stationary
coupling curve. Identification with the minimizing Gardner branch is
supplied later by the full stationary contact geometry. -/
noncomputable section
open Set Filter Asymptotics
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 2000000
namespace LimitingStandingData
variable {Ξ:AdmissibleCovariance} {r:ℕ} {seed:AtomicPoint r}

def bifurcationKappa (d:LimitingStandingData Ξ seed) (p:ℕ):ℝ:=
  -(1/2:ℝ)*deriv (d.couplingCurve p) 1

theorem bifurcationKappa_limit (d:LimitingStandingData Ξ seed):
    Tendsto d.bifurcationKappa (atTop⊓𝓟 {p:ℕ|Even p})
      (𝓝 (pressureKappa (scaledThermodynamicPressure Ξ.toEvenMixture))) := by
  let ell:=pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture)
  obtain ⟨C,hC,A,c,hc,H⟩:=d.couplingCurve_C2_exponential_error
  obtain ⟨_,_,_,_,_,Hroot⟩:=d.couplingCurve_eventually
  have hlim:Tendsto (fun p:ℕ=>C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)))
      (atTop⊓𝓟 {p:ℕ|Even p}) (𝓝 0):=(tendsto_nat_polynomial_exp C c A hc).mono_left inf_le_left
  have hb:∀ᶠp:ℕ in atTop⊓𝓟 {p:ℕ|Even p},
      ‖deriv (d.couplingCurve p) 1-deriv ell 1‖≤C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) := by
    rw [eventually_inf_principal]
    filter_upwards [H,Hroot] with p hp hr heven
    have hq:=(hr heven 1 ⟨d.massLower_mem.2.le,le_rfl⟩).2.2.1
    have he:=hp heven 1 ⟨d.massLower_mem.2.le,le_rfl⟩ 1 (by norm_num)
    rw [norm_iteratedFDeriv_one,←norm_deriv_eq_norm_fderiv,
      deriv_fun_sub (hq.differentiableAt (by simp))
        ((d.ell_smooth 1 ⟨d.massLower_mem.2.le,le_rfl⟩).differentiableAt (by simp))] at he
    exact he
  have hz:Tendsto (fun p=>deriv (d.couplingCurve p) 1-deriv ell 1)
      (atTop⊓𝓟 {p:ℕ|Even p}) (𝓝 0):=
    tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (.of_forall fun p=>norm_nonneg _) hb hlim)
  have hd:=hz.add_const (deriv ell 1)
  have hk:=hd.const_mul (-(1/2:ℝ))
  have hEll:=deriv_pressureEll_one (scaledThermodynamicPressure Ξ.toEvenMixture)
    ((d.pressure_smooth 1 ⟨d.massLower_mem.2.le,le_rfl⟩).of_le (by simp))
  simp only [sub_add_cancel,zero_add] at hk
  dsimp only [ell] at hk
  rw [hEll] at hk
  convert hk using 1
  · rfl
  · congr 1
    ring

theorem couplingCurve_second_derivative_bounded (d:LimitingStandingData Ξ seed):
    ∃B:ℝ,0<B ∧ ∀ᶠp:ℕ in atTop,∀heven:Even p,∀m∈Icc d.massLower 1,
      |deriv (deriv (d.couplingCurve p)) m| ≤ B := by
  let ell:=pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture)
  have hcont:ContinuousOn (deriv (deriv ell)) (Icc d.massLower 1):=by
    intro m hm
    exact (((d.ell_smooth m hm).derivWithin (m:=∞) (by simp)).derivWithin
      (m:=∞) (by simp)).continuousAt.continuousWithinAt
  obtain ⟨B,hB⟩:=isCompact_Icc.exists_bound_of_continuousOn hcont
  obtain ⟨C,hC,A,c,hc,H⟩:=d.couplingCurve_C2_exponential_error
  obtain ⟨_,_,_,_,_,Hroot⟩:=d.couplingCurve_eventually
  have Hsmall:∀ᶠp:ℕ in atTop,C*(p:ℝ)^A*Real.exp (-c*(p:ℝ))≤1:=
    (tendsto_nat_polynomial_exp C c A hc).eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨max 0 B+1,by positivity,?_⟩
  filter_upwards [H,Hroot,Hsmall] with p hp hr hsmall heven m hm
  have hq:=(hr heven m hm).2.2.1
  have he:=hp heven m hm 2 (by norm_num)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedDeriv_fun_sub (hq.of_le (by simp)) ((d.ell_smooth m hm).of_le (by simp))] at he
  simp only [iteratedDeriv_succ,iteratedDeriv_zero,Real.norm_eq_abs] at he
  have hbb:=hB m hm
  rw [Real.norm_eq_abs] at hbb
  calc
    |deriv (deriv (d.couplingCurve p)) m| ≤ 
      |deriv (deriv (d.couplingCurve p)) m-deriv (deriv ell) m| + |deriv (deriv ell) m| :=
        by
          have hh:=abs_add_le (deriv (deriv (d.couplingCurve p)) m-deriv (deriv ell) m)
            (deriv (deriv ell) m)
          simpa only [sub_add_cancel] using hh
    _ ≤ 1+B := add_le_add (he.trans hsmall) hbb
    _ ≤ max 0 B+1 := by linarith [le_max_right 0 B]

/-- The true inverse mass has the source's uniform quadratic error. -/
theorem bifurcatingMass_quadratic_law (d:LimitingStandingData Ξ seed):
    ∃C:ℝ,0<C ∧ ∀ᶠp:ℕ in atTop,∀heven:Even p,
      0<d.bifurcationKappa p ∧
      ∀δ∈Ioc (0:ℝ) (d.couplingMargin/2),
        |1-d.bifurcatingMass p (d.couplingCurve p 1+δ)-δ/(2*d.bifurcationKappa p)| ≤ C*δ^2 := by
  obtain ⟨B,hB,HB⟩:=d.couplingCurve_second_derivative_bounded
  obtain ⟨_,_,_,_,_,Hroot⟩:=d.couplingCurve_eventually
  have Hsmall:∀ᶠp:ℕ in atTop,∀heven:Even p,|d.couplingCurve p 1-
      pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) 1|<d.couplingMargin/2:=by
    obtain ⟨C,hC,A,c,hc,H⟩:=d.couplingCurve_eventually
    have hsmall:∀ᶠp:ℕ in atTop,C*(p:ℝ)^A*Real.exp (-c*(p:ℝ))<d.couplingMargin/2:=
      (tendsto_nat_polynomial_exp C c A hc).eventually (eventually_lt_nhds (div_pos d.couplingMargin_pos (by norm_num : (0:ℝ)<2)))
    filter_upwards [H,hsmall] with p hp hs heven
    exact (hp heven 1 ⟨d.massLower_mem.2.le,le_rfl⟩).2.2.2.2.1.trans_lt hs
  refine ⟨B/d.slope^3,div_pos hB (pow_pos d.slope_pos _),?_⟩
  filter_upwards [HB,Hroot,d.couplingCurve_slope_eventually,d.bifurcatingMass_eventually,Hsmall]
    with p hb hr hs hi hsmall heven
  have hreg (m:ℝ) (hm:m∈Icc d.massLower 1):ContDiffAt ℝ 2 (d.couplingCurve p) m:=
    ((hs heven m hm).1).of_le (by simp)
  have hpos:=((hs heven 1 ⟨d.massLower_mem.2.le,le_rfl⟩).2)
  refine ⟨by dsimp only [bifurcationKappa];linarith [d.slope_pos],?_⟩
  intro δ hδ
  let lam:=d.couplingCurve p 1+δ
  have hlam:lam∈Ioc (d.couplingCurve p 1)
      (pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) 1+d.couplingMargin):=by
    refine ⟨by dsimp [lam];linarith [hδ.1],?_⟩
    have hupper:=le_abs_self (d.couplingCurve p 1-pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) 1)
    dsimp only [lam]
    linarith [hδ.2,hsmall heven]
  have hm:=(hi heven).2 lam hlam
  have hlaw:=branch_inverse_quadratic_mass_law (d.couplingCurve p) d.massLower_mem.2 d.slope_pos hB.le
    hreg (fun m hmem=>(hs heven m hmem).2) (hb heven)
    ⟨hm.1.1.le,hm.1.2.le⟩
  have hdiff:d.couplingCurve p (d.bifurcatingMass p lam)-d.couplingCurve p 1=δ:=by
    rw [hm.2.1]
    dsimp [lam]
    ring
  simpa only [hdiff,bifurcationKappa] using hlaw.2

end LimitingStandingData
end DepthPaper
