module

public import GeneralDepthPaper.StationaryGardnerAsymptotics

@[expose] public section

/-! Derivative-ratio normalization for Revision (16), Corollary 5.2.
The derivatives are ordinary derivatives of the actual stationary mass
function on its smooth local extensions. At mass one they consequently
agree with the left derivatives on the closed mass window. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GeneralDepthPaper
namespace LimitingStandingData
variable {Ξ : AdmissibleCovariance} {r : ℕ} {seed : AtomicPoint r}

def revisedCriticalCouplingPartial (d : LimitingStandingData Ξ seed) (p : ℕ) : ℝ :=
  deriv (fun lam => d.stationaryMassFunction p (lam, 1)) (d.couplingCurve p 1)

def revisedCriticalMassPartial (d : LimitingStandingData Ξ seed) (p : ℕ) : ℝ :=
  deriv (fun m => d.stationaryMassFunction p (d.couplingCurve p 1, m)) 1

def revisedBifurcationKappa (d : LimitingStandingData Ξ seed) (p : ℕ) : ℝ :=
  d.revisedCriticalMassPartial p / (2 * d.revisedCriticalCouplingPartial p)

theorem revisedCriticalPartials_eventually (d : LimitingStandingData Ξ seed) :
    ∀ᶠ p : ℕ in atTop, ∀ _he : Even p,
      0 < d.revisedCriticalCouplingPartial p ∧
      0 < d.revisedCriticalMassPartial p ∧
      d.revisedBifurcationKappa p = d.bifurcationKappa p := by
  obtain ⟨_, _, _, _, _, Hr⟩ := d.couplingCurve_eventually
  obtain ⟨C, hC, A, c, hc, Hm⟩ := d.stationaryMassFunction_C2_exponential_error
  have Hsmall : ∀ᶠ p : ℕ in atTop,
      C * (p : ℝ)^A * Real.exp (-c * (p : ℝ)) < 1 / 4 :=
    (tendsto_nat_polynomial_exp C c A hc).eventually
      (eventually_lt_nhds (show (0 : ℝ) < 1 / 4 by norm_num))
  filter_upwards [Hr, Hm, Hsmall, d.couplingCurve_slope_eventually]
    with p hr hm hsmall hs he
  let l := d.couplingCurve p 1
  let G := d.stationaryMassFunction p
  have hroot := hr he 1 ⟨d.massLower_mem.2.le, le_rfl⟩
  have ht : (l, (1 : ℝ)) ∈ d.parameterWindow :=
    ⟨⟨hroot.1.1.le, hroot.1.2.le⟩, ⟨d.massLower_mem.2.le, le_rfl⟩⟩
  have hG : ContDiffAt ℝ ∞ G (l, 1) := (hm he (l, 1) ht).1
  have hGF : HasFDerivAt G (fderiv ℝ G (l, 1)) (l, 1) :=
    (hG.differentiableAt (by simp)).hasFDerivAt
  have hcurve : ContDiffAt ℝ ∞ (d.couplingCurve p) 1 := hroot.2.2.1
  have hiCoupling : HasDerivAt (fun x : ℝ => (x, (1 : ℝ))) (1, 0) l :=
    (hasDerivAt_id l).prodMk (hasDerivAt_const l (1 : ℝ))
  have hcoupling : HasDerivAt (fun x => G (x, 1)) (fderiv ℝ G (l, 1) (1, 0)) l :=
    hGF.comp_hasDerivAt (f := fun x : ℝ => (x, (1 : ℝ))) l hiCoupling
  have hmass : HasDerivAt (fun x => G (l, x)) (fderiv ℝ G (l, 1) (0, 1)) 1 :=
    hGF.comp_hasDerivAt 1
      ((hasDerivAt_const (1 : ℝ) l).prodMk (hasDerivAt_id (1 : ℝ)))
  have hpositive : 0 < fderiv ℝ G (l, 1) (1, 0) := by
    have herr := d.stationaryMassFunction_coupling_partial_error p (l, 1) ht
      hG ((hm he (l, 1) ht).2 1 (by norm_num))
    have hlow := neg_le_abs (fderiv ℝ G (l, 1) (1, 0) - 1 / 2)
    linarith
  have hiCurve : HasDerivAt (fun x : ℝ => (d.couplingCurve p x, x))
      (deriv (d.couplingCurve p) 1, 1) 1 :=
    ((hcurve.differentiableAt (by simp)).hasDerivAt).prodMk (hasDerivAt_id (1 : ℝ))
  have hcompose : HasDerivAt (fun x => G (d.couplingCurve p x, x))
      (fderiv ℝ G (l, 1) (deriv (d.couplingCurve p) 1, 1)) 1 :=
    hGF.comp_hasDerivAt (f := fun x : ℝ => (d.couplingCurve p x, x)) 1 hiCurve
  have hzero : fderiv ℝ G (l, 1) (deriv (d.couplingCurve p) 1, 1) = 0 := by
    have heq : (fun x => G (d.couplingCurve p x, x)) =ᶠ[𝓝 1] fun _ => (0 : ℝ) :=
      hroot.2.2.2.1.mono (fun x hx => hx.2)
    exact hcompose.unique ((hasDerivAt_const 1 (0 : ℝ)).congr_of_eventuallyEq heq)
  have hsplit : fderiv ℝ G (l, 1) (deriv (d.couplingCurve p) 1, 1) =
      deriv (d.couplingCurve p) 1 * fderiv ℝ G (l, 1) (1, 0) +
        fderiv ℝ G (l, 1) (0, 1) := by
    rw [show (deriv (d.couplingCurve p) 1, (1 : ℝ)) =
      deriv (d.couplingCurve p) 1 • ((1, 0) : ℝ × ℝ) + (0, 1) by ext <;> simp,
      map_add, map_smul]
    rfl
  have hslope := (hs he 1 ⟨d.massLower_mem.2.le, le_rfl⟩).2
  have hmasspositive : 0 < fderiv ℝ G (l, 1) (0, 1) := by
    have hneg : deriv (d.couplingCurve p) 1 < 0 := by linarith [d.slope_pos]
    have hprod := mul_neg_of_neg_of_pos hneg hpositive
    rw [hsplit] at hzero
    linarith
  refine ⟨?_, ?_, ?_⟩
  · simpa only [revisedCriticalCouplingPartial, l, G, hcoupling.deriv] using hpositive
  · simpa only [revisedCriticalMassPartial, l, G, hmass.deriv] using hmasspositive
  · dsimp only [revisedBifurcationKappa, revisedCriticalMassPartial,
      revisedCriticalCouplingPartial, bifurcationKappa]
    change deriv (fun x => G (l, x)) 1 / (2 * deriv (fun x => G (x, 1)) l) = _
    rw [hmass.deriv, hcoupling.deriv]
    apply (div_eq_iff (mul_ne_zero (by norm_num) hpositive.ne')).mpr
    rw [hsplit] at hzero
    nlinarith

theorem revisedBifurcationKappa_limit (d : LimitingStandingData Ξ seed) :
    Tendsto d.revisedBifurcationKappa (atTop ⊓ 𝓟 {p : ℕ | Even p})
      (𝓝 (pressureKappa (scaledThermodynamicPressure Ξ.toEvenMixture))) := by
  apply d.bifurcationKappa_limit.congr'
  change ∀ᶠ p in atTop ⊓ 𝓟 {p : ℕ | Even p}, d.bifurcationKappa p = d.revisedBifurcationKappa p
  rw [eventually_inf_principal]
  filter_upwards [d.revisedCriticalPartials_eventually] with p hp he
  exact (hp he).2.2.symm

end LimitingStandingData
end GeneralDepthPaper
