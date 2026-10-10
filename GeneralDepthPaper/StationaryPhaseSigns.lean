module

public import GeneralDepthPaper.StationaryBranchProposition
public import GeneralDepthPaper.StationaryCandidateContacts

@[expose] public section


/-! The critical coupling is the genuine unique sign change of the
selected endpoint response. These signs derive from the actual positive
coupling derivative and constructed root, rather than being phase inputs. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 1400000
namespace LimitingStandingData
variable {Ξ : AdmissibleCovariance} {r : ℕ} {seed : AtomicPoint r}

theorem stationaryMassFunction_lambda_strictMono_eventually (d : LimitingStandingData Ξ seed) :
    ∀ᶠp:ℕ in atTop,∀he:Even p,∀m∈Icc d.massLower 1,
      StrictMonoOn (fun lam=>d.stationaryMassFunction p (lam,m))
        (Icc d.couplingLower d.couplingUpper) := by
  obtain ⟨C,hC,A,c,hc,H⟩:=d.stationaryMassFunction_C2_exponential_error
  have Hsmall:∀ᶠp:ℕ in atTop,C*(p:ℝ)^A*Real.exp (-c*(p:ℝ))≤1/4:=
    (tendsto_nat_polynomial_exp C c A hc).eventually
      (eventually_le_nhds (by norm_num : (0:ℝ)<1/4))
  filter_upwards [H,Hsmall] with p hp hsmall he m hm
  have hd (lam:ℝ) (hlam:lam∈Icc d.couplingLower d.couplingUpper) :
      HasDerivAt (fun lam=>d.stationaryMassFunction p (lam,m))
        (fderiv ℝ (d.stationaryMassFunction p) (lam,m) (1,0)) lam := by
    have hs:=(hp he (lam,m) ⟨hlam,hm⟩).1
    exact (hs.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt lam
      ((hasDerivAt_id lam).prodMk (hasDerivAt_const lam m))
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
    (fun lam hlam=>(hd lam hlam).continuousAt.continuousWithinAt)
      (f':=fun lam=>fderiv ℝ (d.stationaryMassFunction p) (lam,m) (1,0))
  · intro lam hlam
    exact (hd lam (interior_subset hlam)).hasDerivWithinAt
  · intro lam hlam
    have hmem:lam∈Icc d.couplingLower d.couplingUpper:=interior_subset hlam
    have hs:=hp he (lam,m) ⟨hmem,hm⟩
    have herror:=d.stationaryMassFunction_coupling_partial_error p (lam,m) ⟨hmem,hm⟩
      hs.1 (hs.2 1 (by norm_num))
    have hh:=neg_le_abs (fderiv ℝ (d.stationaryMassFunction p) (lam,m) (1,0)-1/2)
    linarith

theorem stationary_mass_one_phase_signs (d : LimitingStandingData Ξ seed) :
    ∀ᶠp:ℕ in atTop,∀he:Even p,∀lam∈Icc d.couplingLower d.couplingUpper,
      (d.stationaryMassFunction p (lam,1)<0↔lam<d.couplingCurve p 1) ∧
      (d.stationaryMassFunction p (lam,1)=0↔lam=d.couplingCurve p 1) ∧
      (0<d.stationaryMassFunction p (lam,1)↔d.couplingCurve p 1<lam) := by
  obtain ⟨_,_,_,_,_,Hr⟩:=d.couplingCurve_eventually
  filter_upwards [d.stationaryMassFunction_lambda_strictMono_eventually,Hr] with p hp hr he lam hl
  have hm:(1:ℝ)∈Icc d.massLower 1:=⟨d.massLower_mem.2.le,le_rfl⟩
  have hroot:=hr he 1 hm
  have hmon:=hp he 1 hm
  have hcritical:d.couplingCurve p 1∈Icc d.couplingLower d.couplingUpper:=
    Ioo_subset_Icc_self hroot.1
  have hzero:=hroot.2.1
  have hlt:=hmon.lt_iff_lt hl hcritical
  have heq:=hmon.eq_iff_eq hl hcritical
  have hgt:=hmon.lt_iff_lt hcritical hl
  rw [hzero] at hlt heq hgt
  exact ⟨hlt,heq,hgt⟩

theorem stationary_interior_response_zero (d : LimitingStandingData Ξ seed) :
    ∀ᶠp:ℕ in atTop,∀he:Even p,
      ∀lam∈Ioc (d.couplingCurve p 1)
        (pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) 1+d.couplingMargin),
        d.bifurcatingMass p lam∈Ioo d.massLower 1 ∧
          d.stationaryMassFunction p (lam,d.bifurcatingMass p lam)=0 := by
  obtain ⟨_,_,_,_,_,Hr⟩:=d.couplingCurve_eventually
  filter_upwards [d.bifurcatingMass_eventually,Hr] with p hp hr he lam hl
  have H:=(hp he).2 lam hl
  have hm:=H.1
  have hz:=(hr he _ (Ioo_subset_Icc_self hm)).2.1
  rw [H.2.1] at hz
  exact ⟨hm,hz⟩

end LimitingStandingData
end GeneralDepthPaper
