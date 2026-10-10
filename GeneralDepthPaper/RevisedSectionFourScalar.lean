module

public import GeneralDepthPaper.StationaryPhaseSigns
public import GeneralDepthPaper.StationaryMassPositive
public import GeneralDepthPaper.RevisedAsymptoticsEnvelope
public import GeneralDepthPaper.RevisedNondegeneracyBridge

@[expose] public section

/-! Revised Proposition 4.6: the exact symmetric paper coupling window,
actual scalar objective, and unique constrained scalar minimizer. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 1800000

/-- A strictly increasing derivative determines a unique constrained
minimum, including the boundary case where its value at the right end
is nonpositive. -/
theorem revised_unique_minimum_of_derivative {a b c : ℝ} {F G : ℝ → ℝ}
    (hc : c ∈ Icc a b) (hF : ∀ x ∈ Icc a b, HasDerivAt F (G x) x)
    (hG : StrictMonoOn G (Icc a b))
    (hstationary : (c = b ∧ G c ≤ 0) ∨ G c = 0) :
    IsMinOn F (Icc a b) c ∧ ∀ x ∈ Icc a b, IsMinOn F (Icc a b) x → x = c := by
  have hGc : G c ≤ 0 := hstationary.elim (fun h => h.2) (fun h => h.le)
  have hleft : StrictAntiOn F (Icc a c) := by
    apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _)
      (fun x hx => (hF x ⟨hx.1, hx.2.trans hc.2⟩).continuousAt.continuousWithinAt)
      (f' := G)
    · intro x hx
      exact (hF x ⟨(interior_subset hx).1, (interior_subset hx).2.trans hc.2⟩).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hG ⟨hx.1.le, hx.2.le.trans hc.2⟩ hc hx.2).trans_le hGc
  have hright : StrictMonoOn F (Icc c b) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
      (fun x hx => (hF x ⟨hc.1.trans hx.1, hx.2⟩).continuousAt.continuousWithinAt)
      (f' := G)
    · intro x hx
      exact (hF x ⟨hc.1.trans (interior_subset hx).1, (interior_subset hx).2⟩).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rcases hstationary with h|h
      · linarith [h.1,hx.1,hx.2]
      · rw [← h]
        exact hG hc ⟨hc.1.trans hx.1.le, hx.2.le⟩ hx.1
  have hstrict : ∀ x ∈ Icc a b, x ≠ c → F c < F x := by
    intro x hx hne
    rcases lt_trichotomy x c with h|h|h
    · exact hleft ⟨hx.1,h.le⟩ ⟨hc.1,le_rfl⟩ h
    · exact (hne h).elim
    · exact hright ⟨le_rfl,hc.2⟩ ⟨h.le,hx.2⟩ h
  refine ⟨?_,?_⟩
  · intro x hx
    by_cases h : x = c
    · change F c ≤ F x
      rw [h]
    · exact (hstrict x hx h).le
  · intro x hx hmin
    by_contra hne
    exact (not_lt_of_ge (hmin hc)) (hstrict x hx hne)

namespace LimitingStandingData
variable {Ξ : AdmissibleCovariance} {r : ℕ} {seed : AtomicPoint r}

/-- The printed Section 4 coupling window has width 4η and is centered
at the limiting critical coupling. -/
def revisedCouplingUpper (d : LimitingStandingData Ξ seed) : ℝ :=
  pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) 1 + 2*d.couplingMargin

def revisedCouplingWindow (d : LimitingStandingData Ξ seed) : Set ℝ :=
  Icc d.couplingLower d.revisedCouplingUpper

def revisedParameterWindow (d : LimitingStandingData Ξ seed) : Set (ℝ×ℝ) :=
  d.revisedCouplingWindow ×ˢ Icc d.massLower 1

theorem revisedCouplingUpper_lt_upper (d : LimitingStandingData Ξ seed) :
    d.revisedCouplingUpper < d.couplingUpper := by
  have H := d.ell_strictAnti ⟨le_rfl,d.massLower_mem.2.le⟩
    ⟨d.massLower_mem.2.le,le_rfl⟩ d.massLower_mem.2
  dsimp only [revisedCouplingUpper,couplingUpper]
  linarith

theorem revisedParameterWindow_subset (d : LimitingStandingData Ξ seed) :
    d.revisedParameterWindow ⊆ d.parameterWindow := by
  intro theta ht
  exact ⟨⟨ht.1.1,ht.1.2.trans d.revisedCouplingUpper_lt_upper.le⟩,ht.2⟩

theorem revised_bifurcatingMass_eventually (d : LimitingStandingData Ξ seed) :
    ∀ᶠp:ℕ in atTop,∀he:Even p,
      ∀lam∈Ioc (d.couplingCurve p 1) d.revisedCouplingUpper,
        d.bifurcatingMass p lam∈Ioo d.massLower 1 ∧
        d.couplingCurve p (d.bifurcatingMass p lam)=lam ∧
        (∀m∈Icc d.massLower 1,d.couplingCurve p m=lam→m=d.bifurcatingMass p lam) := by
  obtain ⟨C,hC,A,c,hc,H⟩:=d.couplingCurve_eventually
  have Hsmall:∀ᶠp:ℕ in atTop,C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) < d.couplingMargin:=
    (tendsto_nat_polynomial_exp C c A hc).eventually (eventually_lt_nhds d.couplingMargin_pos)
  filter_upwards [H,d.couplingCurve_slope_eventually,Hsmall,d.bifurcatingMass_eventually]
    with p hp hs hsmall hanti he lam hlam
  have hreg (m:ℝ) (hm:m∈Icc d.massLower 1):ContDiffAt ℝ ∞ (d.couplingCurve p) m:=
    (hs he m hm).1
  let G:ℝ×ℝ→ℝ:=fun w=>w.1-d.couplingCurve p w.2
  have hg (m:ℝ) (hm:m∈Icc d.massLower 1):ContDiffAt ℝ ∞ (fun u=>G (lam,u)) m:=
    contDiffAt_const.sub (hreg m hm)
  have hlow:G (lam,d.massLower) < 0:=by
    have herr:|d.couplingCurve p d.massLower-
        pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) d.massLower| < d.couplingMargin:=
      (hp he d.massLower ⟨le_rfl,d.massLower_mem.2.le⟩).2.2.2.2.1.trans_lt hsmall
    have hh:=neg_le_abs (d.couplingCurve p d.massLower-
      pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) d.massLower)
    have hgap:=d.couplingMargin_gap
    dsimp only [G,revisedCouplingUpper] at *
    linarith [hlam.2,d.couplingMargin_pos]
  have hhigh:0 < G (lam,1):=by dsimp [G];linarith [hlam.1]
  have hd (m:ℝ) (hm:m∈Icc d.massLower 1):0 < deriv (fun u=>G (lam,u)) m:=by
    rw [show (fun u=>G (lam,u))=(fun u=>lam-d.couplingCurve p u) by rfl,deriv_const_sub]
    linarith [(hs he m hm).2,d.slope_pos]
  have hroot:=intervalImplicitRoot_spec G d.massLower_mem.2 lam hg hlow hhigh hd
  have hz:=hroot.2
  change lam-d.couplingCurve p (d.bifurcatingMass p lam)=0 at hz
  refine ⟨hroot.1,by linarith,?_⟩
  intro m hm hmroot
  apply (hanti he).1.injOn hm ⟨hroot.1.1.le,hroot.1.2.le⟩
  linarith

/-- Literal scalar minimizer in the exact paper window, including both
closed endpoints. The interior root is selected by the actual gp. -/
theorem revised_scalar_minimum_eventually (d : LimitingStandingData Ξ seed) :
    ∀ᶠp:ℕ in atTop,∀he:Even p,
      ∀lam∈d.revisedCouplingWindow,
        ∃!m:ℝ,m∈Icc d.massLower 1 ∧
          IsMinOn (fun u=>d.revisedScalarObjective p (lam,u)) (Icc d.massLower 1) m ∧
          (lam≤d.couplingCurve p 1→m=1) ∧
          (d.couplingCurve p 1<lam→m∈Ioo d.massLower 1 ∧
            d.stationaryMassFunction p (lam,m)=0) ∧
          (∀n∈Icc d.massLower 1,
            IsMinOn (fun u=>d.revisedScalarObjective p (lam,u)) (Icc d.massLower 1) n→n=m) := by
  obtain ⟨_,_,_,_,_,Hr⟩:=d.couplingCurve_eventually
  filter_upwards [d.revisedScalarObjective_massDerivative_eventually,
    d.stationaryMassFunction_mass_partial_pos_eventually,
    d.stationary_mass_one_phase_signs,d.revised_bifurcatingMass_eventually,Hr]
    with p hJ hg hsign hmass hr he lam hlam
  have hlold:lam∈Icc d.couplingLower d.couplingUpper:=
    ⟨hlam.1,hlam.2.trans d.revisedCouplingUpper_lt_upper.le⟩
  have hd (m:ℝ) (hm:m∈Icc d.massLower 1):
      HasDerivAt (fun m=>d.stationaryMassFunction p (lam,m))
        (fderiv ℝ (d.stationaryMassFunction p) (lam,m) (0,1)) m :=
    ((hg he (lam,m) ⟨hlold,hm⟩).1.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt m
      ((hasDerivAt_const m lam).prodMk (hasDerivAt_id m))
  have hmono:StrictMonoOn (fun m=>d.stationaryMassFunction p (lam,m)) (Icc d.massLower 1):=by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
      (fun m hm=>(hd m hm).continuousAt.continuousWithinAt)
      (f':=fun m=>fderiv ℝ (d.stationaryMassFunction p) (lam,m) (0,1))
    · intro m hm
      exact (hd m (interior_subset hm)).hasDerivWithinAt
    · intro m hm
      exact (half_pos d.slope_pos).trans_le (hg he (lam,m) ⟨hlold,interior_subset hm⟩).2
  have hJD (m:ℝ) (hm:m∈Icc d.massLower 1):
      HasDerivAt (fun m=>d.revisedScalarObjective p (lam,m)) (d.stationaryMassFunction p (lam,m)) m:=
    hJ he (lam,m) ⟨hlold,hm⟩
  by_cases hphase:lam≤d.couplingCurve p 1
  · have hG: d.stationaryMassFunction p (lam,1)≤0 := by
      rcases hphase.eq_or_lt with h|h
      · exact ((hsign he lam hlold).2.1.mpr h).le
      · exact ((hsign he lam hlold).1.mpr h).le
    have H:=revised_unique_minimum_of_derivative ⟨d.massLower_mem.2.le,le_rfl⟩
      hJD hmono (Or.inl ⟨rfl,hG⟩)
    refine ⟨1,⟨⟨d.massLower_mem.2.le,le_rfl⟩,H.1,fun _=>rfl,?_,H.2⟩,?_⟩
    · intro h
      exact (not_lt_of_ge hphase h).elim
    · intro m hm
      exact H.2 m hm.1 hm.2.1
  · have hphase':d.couplingCurve p 1<lam:=lt_of_not_ge hphase
    obtain ⟨hm,hcurve,_⟩:=hmass he lam ⟨hphase',hlam.2⟩
    have hzero: d.stationaryMassFunction p (lam,d.bifurcatingMass p lam)=0:=by
      have H:=(hr he _ (Ioo_subset_Icc_self hm)).2.1
      rwa [hcurve] at H
    have H:=revised_unique_minimum_of_derivative (Ioo_subset_Icc_self hm) hJD hmono (Or.inr hzero)
    refine ⟨d.bifurcatingMass p lam,⟨Ioo_subset_Icc_self hm,H.1,?_,fun _=>⟨hm,hzero⟩,H.2⟩,?_⟩
    · intro h
      exact (not_le_of_gt hphase' h).elim
    · intro m hmin
      exact H.2 m hmin.1 hmin.2.1


/-- All scalar-bifurcation conclusions in revised 4.6 for a common
constructed branch; the window is exactly centered at the limiting root. -/
theorem revised_scalar_bifurcation_data (d : LimitingStandingData Ξ seed) :
    Tendsto (fun p=>d.couplingCurve p 1) (atTop⊓𝓟 {p:ℕ|Even p})
      (𝓝 (pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) 1)) ∧
    ∀ᶠp:ℕ in atTop,∀he:Even p,
      (d.couplingCurve p 1∈Ioo d.couplingLower d.revisedCouplingUpper) ∧
      d.stationaryMassFunction p (d.couplingCurve p 1,1)=0 ∧
      (∀lam∈d.revisedCouplingWindow,
        (d.stationaryMassFunction p (lam,1)<0↔lam<d.couplingCurve p 1) ∧
        (d.stationaryMassFunction p (lam,1)=0↔lam=d.couplingCurve p 1) ∧
        (0<d.stationaryMassFunction p (lam,1)↔d.couplingCurve p 1<lam)) ∧
      (∀theta∈d.revisedParameterWindow,
        ContDiffAt ℝ ∞ (d.stationaryMassFunction p) theta ∧
        d.slope/2≤fderiv ℝ (d.stationaryMassFunction p) theta (0,1) ∧
        1/4≤fderiv ℝ (d.stationaryMassFunction p) theta (1,0) ∧
        HasDerivAt (fun m=>d.revisedScalarObjective p (theta.1,m))
          (d.stationaryMassFunction p theta) theta.2) ∧
      (∀lam∈d.revisedCouplingWindow,
        ∃!m:ℝ,m∈Icc d.massLower 1 ∧
          IsMinOn (fun u=>d.revisedScalarObjective p (lam,u)) (Icc d.massLower 1) m ∧
          (lam≤d.couplingCurve p 1→m=1) ∧
          (d.couplingCurve p 1<lam→m∈Ioo d.massLower 1 ∧
            d.stationaryMassFunction p (lam,m)=0) ∧
          (∀n∈Icc d.massLower 1,
            IsMinOn (fun u=>d.revisedScalarObjective p (lam,u)) (Icc d.massLower 1) n→n=m)) := by
  obtain ⟨C,hC,A,c,hc,Hcurve⟩:=d.couplingCurve_eventually
  obtain ⟨Cg,hCg,Ag,cg,hcg,Hg⟩:=d.stationaryMassFunction_C2_exponential_error
  have Hsmall:∀ᶠp:ℕ in atTop,C*(p:ℝ)^A*Real.exp (-c*(p:ℝ))<d.couplingMargin:=
    (tendsto_nat_polynomial_exp C c A hc).eventually (eventually_lt_nhds d.couplingMargin_pos)
  have Hgsmall:∀ᶠp:ℕ in atTop,Cg*(p:ℝ)^Ag*Real.exp (-cg*(p:ℝ))≤1/4:=
    (tendsto_nat_polynomial_exp Cg cg Ag hcg).eventually
      (eventually_le_nhds (by norm_num : (0:ℝ)<1/4))
  refine ⟨d.couplingCurve_critical_limit,?_⟩
  filter_upwards [Hcurve,Hsmall,Hg,Hgsmall,d.stationaryMassFunction_mass_partial_pos_eventually,
    d.revisedScalarObjective_massDerivative_eventually,d.stationary_mass_one_phase_signs,
    d.revised_scalar_minimum_eventually] with p hcurve hsmall hg hgsmall hmass hJ hsign hmin he
  have hmone:(1:ℝ)∈Icc d.massLower 1:=⟨d.massLower_mem.2.le,le_rfl⟩
  have herr:|d.couplingCurve p 1-pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) 1|<
      d.couplingMargin:=(hcurve he 1 hmone).2.2.2.2.1.trans_lt hsmall
  have hcritical:d.couplingCurve p 1∈Ioo d.couplingLower d.revisedCouplingUpper:=by
    have hneg:=neg_le_abs (d.couplingCurve p 1-
      pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) 1)
    have hpos:=le_abs_self (d.couplingCurve p 1-
      pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) 1)
    dsimp only [couplingLower,revisedCouplingUpper]
    constructor <;> linarith [d.couplingMargin_pos]
  refine ⟨hcritical,(hcurve he 1 hmone).2.1,?_,?_,hmin he⟩
  · intro lam hlam
    exact hsign he lam ⟨hlam.1,hlam.2.trans d.revisedCouplingUpper_lt_upper.le⟩
  · intro theta htheta
    have ht:=d.revisedParameterWindow_subset htheta
    have h:=hg he theta ht
    have herror:=d.stationaryMassFunction_coupling_partial_error p theta ht h.1 (h.2 1 (by norm_num))
    have hneg:=neg_le_abs (fderiv ℝ (d.stationaryMassFunction p) theta (1,0)-1/2)
    exact ⟨h.1,(hmass he theta ht).2,by linarith,hJ he theta ht⟩

end LimitingStandingData

/-- The seed assumptions are precisely the revised paper's weak
nondegeneracy and separate quadratic subcriticality condition. -/
theorem revised_scalar_bifurcation (Ξ:AdmissibleCovariance) {r:ℕ}
    (seed:AtomicPoint r) (hz:IsAtomicPoint seed) (hND:PaperNondegenerate Ξ seed hz)
    (hsub:Ξ.IsSubcritical) :
    ∃d:LimitingStandingData Ξ seed,
      Tendsto (fun p=>d.couplingCurve p 1) (atTop⊓𝓟 {p:ℕ|Even p})
        (𝓝 (pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) 1)) ∧
      ∀ᶠp:ℕ in atTop,∀he:Even p,
        (d.couplingCurve p 1∈Ioo d.couplingLower d.revisedCouplingUpper) ∧
        d.stationaryMassFunction p (d.couplingCurve p 1,1)=0 ∧
        (∀lam∈d.revisedCouplingWindow,
          (d.stationaryMassFunction p (lam,1)<0↔lam<d.couplingCurve p 1) ∧
          (d.stationaryMassFunction p (lam,1)=0↔lam=d.couplingCurve p 1) ∧
          (0<d.stationaryMassFunction p (lam,1)↔d.couplingCurve p 1<lam)) ∧
        (∀theta∈d.revisedParameterWindow,
          ContDiffAt ℝ ∞ (d.stationaryMassFunction p) theta ∧
          d.slope/2≤fderiv ℝ (d.stationaryMassFunction p) theta (0,1) ∧
          1/4≤fderiv ℝ (d.stationaryMassFunction p) theta (1,0) ∧
          HasDerivAt (fun m=>d.revisedScalarObjective p (theta.1,m))
            (d.stationaryMassFunction p theta) theta.2) ∧
        (∀lam∈d.revisedCouplingWindow,
          ∃!m:ℝ,m∈Icc d.massLower 1 ∧
            IsMinOn (fun u=>d.revisedScalarObjective p (lam,u)) (Icc d.massLower 1) m ∧
            (lam≤d.couplingCurve p 1→m=1) ∧
            (d.couplingCurve p 1<lam→m∈Ioo d.massLower 1 ∧
              d.stationaryMassFunction p (lam,m)=0) ∧
          (∀n∈Icc d.massLower 1,
            IsMinOn (fun u=>d.revisedScalarObjective p (lam,u)) (Icc d.massLower 1) n→n=m)) := by
  obtain ⟨d⟩:=exists_limitingStandingData Ξ seed hz
    (nondegenerate_of_paperNondegenerate Ξ seed hz hND hsub)
  exact ⟨d,d.revised_scalar_bifurcation_data⟩

end GeneralDepthPaper
