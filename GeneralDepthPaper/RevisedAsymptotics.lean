module

public import GeneralDepthPaper.RevisedAsymptoticsEnvelope
public import GeneralDepthPaper.RevisedAsymptoticsLog

@[expose] public section

/-! Revision (16), Corollary 5.2, on the established covariance and seed
class. The normalization is the displayed derivative ratio, the mass window
is exactly half of the Gardner window, and the location is logarithmic. -/
noncomputable section
open Set Filter MeasureTheory Asymptotics Metric
open scoped Topology NNReal
namespace GeneralDepthPaper
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 64
namespace LimitingStandingData
variable {Ξ:AdmissibleCovariance} {r:ℕ} {seed:AtomicPoint r}

def RevisedGardnerAsymptoticsAt (d:LimitingStandingData Ξ seed) (C:ℝ)
    (p:ℕ) (hp:4≤p) (he:Even p) (hn:p∉Ξ.degrees) : Prop :=
  |d.couplingCurve p 1-d.criticalCoupling|<d.couplingMargin/2 ∧
  0<d.revisedCriticalCouplingPartial p ∧
  0<d.revisedCriticalMassPartial p ∧
  0<d.revisedBifurcationKappa p ∧
  ∀δ∈Ioc (0:ℝ) (d.couplingMargin/2),
    let lam:=d.couplingCurve p 1+δ
    ∃hlam:lam∈d.transitionWindow,
    let X:=Ξ.addHighDegree p hp he hn lam (d.transition_coupling_pos hlam)
    d.interiorCandidate p lam=parisiMinimizer X ∧
    d.newAtomMass p lam=1-d.bifurcatingMass p lam ∧
    |d.newAtomMass p lam-δ/(2*d.revisedBifurcationKappa p)|≤C*δ^2 ∧
    |Real.log (1/(1-(d.interiorTop p lam:ℝ)))
      -d.bifurcatingMass p lam^2*lam*(p:ℝ)/2-(1/2:ℝ)*Real.log (p:ℝ)|≤C

theorem revised_gardner_asymptotics_eventually (d:LimitingStandingData Ξ seed) {gamma:ℝ}
    (hg:0<gamma) (hmargin:∀m:d.MassInterval,d.limitingVariation m d.cutoff≤ -4*gamma)
    (hcost:(1/2:ℝ)*(∫q in d.cutoff..1,(1-q)*Ξ.second q)≤gamma) :
    ∃C:ℝ,1≤C ∧ ∀ᶠp:ℕ in atTop,4≤p ∧ ∀he:Even p,
      ∃hp:4≤p,∃hn:p∉Ξ.degrees,d.RevisedGardnerAsymptoticsAt C p hp he hn := by
  obtain ⟨Cm,hCm,Hmass⟩:=d.bifurcatingMass_quadratic_law
  obtain ⟨b,hb,D,hD,Hroot⟩:=distinguished_endpoint_contact_eventually Ξ
    (isCompact_closedBall seed d.radius) d.ball_valid d.massLower_mem d.couplingLower_pos
    d.couplingLower_le_upper d.cutoff_mem d.ball_below_cutoff
    d.strip_rates.1 d.strip_rates.2.1 d.strip_rates.2.2
  obtain ⟨_,_,_,_,_,Hs⟩:=d.stationaryBranch_eventually
  have Hclose:∀ᶠp:ℕ in atTop,∀he:Even p,
      |d.couplingCurve p 1-d.criticalCoupling|<d.couplingMargin/2 := by
    have H:=d.couplingCurve_critical_limit.eventually
      (Metric.ball_mem_nhds _ (div_pos d.couplingMargin_pos (by norm_num : (0:ℝ)<2)))
    rw [eventually_inf_principal] at H
    simpa only [Metric.mem_ball,Real.dist_eq,criticalCoupling,mem_ofPred_eq] using H
  let C:=max 1 (max (max Cm D) b⁻¹)+1
  have hC1 : 1≤C:=by dsimp only [C];linarith [le_max_left (1:ℝ) (max (max Cm D) b⁻¹)]
  have hC : 0<C:=lt_of_lt_of_le zero_lt_one hC1
  have hCmC:Cm≤C:=by dsimp only [C];linarith [le_max_left Cm D,le_max_left (max Cm D) b⁻¹,le_max_right (1:ℝ) (max (max Cm D) b⁻¹)]
  have hDC:D≤C:=by dsimp only [C];linarith [le_max_right Cm D,le_max_left (max Cm D) b⁻¹,le_max_right (1:ℝ) (max (max Cm D) b⁻¹)]
  have hCb:b⁻¹≤C:=by dsimp only [C];linarith [le_max_right (max Cm D) b⁻¹,le_max_right (1:ℝ) (max (max Cm D) b⁻¹)]
  have hCi:C⁻¹≤b:=by
    have hh:=one_div_le_one_div_of_le (inv_pos.mpr hb) hCb
    simpa only [one_div,inv_inv] using hh
  refine ⟨C,hC1,?_⟩
  filter_upwards [d.gardner_interior_geometry hg hmargin hcost,Hmass,Hroot,Hs,Hclose,
    d.stationary_interior_response_zero,d.revisedCriticalPartials_eventually]
    with p hgeo hmass hroot hs hclose hzero hpartials
  refine ⟨hgeo.1,?_⟩
  intro he
  obtain ⟨hp,hn,Hgeo⟩:=hgeo.2 he
  obtain ⟨hp',hn',Hr⟩:=hroot.2 he
  have hpart:=hpartials he
  refine ⟨hp,hn,hclose he,hpart.1,hpart.2.1,?_,?_⟩
  · rw [hpart.2.2]
    exact (hmass he).1
  · intro δ hδ
    let lam:=d.couplingCurve p 1+δ
    have hlam:lam∈d.transitionWindow:=by
      dsimp only [transitionWindow,lam]
      have hab:=abs_lt.mp (hclose he)
      constructor <;> linarith [hδ.1,hδ.2,hab.1,hab.2,d.couplingMargin_pos]
    have habove:d.couplingCurve p 1<lam:=by dsimp only [lam];linarith [hδ.1]
    let m:=d.bifurcatingMass p lam
    obtain ⟨hz,H⟩:=Hgeo lam hlam habove
    have hm:m∈Ioo d.massLower 1:=(hzero he lam ⟨habove,hlam.2⟩).1
    have ht:(lam,m)∈d.parameterWindow:=⟨d.transitionWindow_subset hlam,Ioo_subset_Icc_self hm⟩
    let z:=d.stationaryBranch p (lam,m)
    have hbz:z∈closedBall seed d.radius:=ball_subset_closedBall (hs he (lam,m) ht).1
    have Hrt:=Hr (z,(m,lam)) hbz (Ioo_subset_Icc_self hm) ht.1
    have hmassid:d.newAtomMass p lam=1-m:=by
      rw [newAtomMass,d.interiorCandidate_eq p lam hz]
      exact twoLevelMeasure_top_mass z hz m ⟨H.1.1.le,H.1.2.le⟩ _ H.2.1
    refine ⟨hlam,?_,hmassid,?_,?_⟩
    · rw [d.interiorCandidate_eq p lam hz]
      exact H.2.2.2.1
    · rw [hmassid]
      rw [hpart.2.2]
      exact ((hmass he).2 δ hδ).trans
        (mul_le_mul_of_nonneg_right hCmC (sq_nonneg δ))
    · have hlo := (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCi (Real.rpow_nonneg (Nat.cast_nonneg p) _))
            (Real.exp_pos _).le).trans Hrt.2.2.2.2.1
      have hhi := Hrt.2.2.2.2.2.1.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hDC (Real.rpow_nonneg (Nat.cast_nonneg p) _))
            (Real.exp_pos _).le)
      have hpPos : 0 < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
      apply logarithmic_location_of_two_sided hpPos hC1
      · simpa only [interiorTop,m,z,lam,neg_mul,neg_div] using hlo
      · simpa only [interiorTop,m,z,lam,neg_mul,neg_div] using hhi

theorem revised_newAtomMass_diagonal_small_o (d:LimitingStandingData Ξ seed)
    {C:ℝ} (hC:0≤C)
    (H:∀ᶠp:ℕ in atTop,4≤p ∧ ∀he:Even p,∃hp:4≤p,∃hn:p∉Ξ.degrees,
      d.RevisedGardnerAsymptoticsAt C p hp he hn)
    (p:ℕ→ℕ) (δ:ℕ→ℝ) (hp:Tendsto p atTop atTop)
    (he:∀ᶠj in atTop,Even (p j)) (hδ:Tendsto δ atTop (𝓝 0))
    (hpos:∀ᶠj in atTop,0<δ j) :
    (fun j=>d.newAtomMass (p j) (d.couplingCurve (p j) 1+δ j)-
      δ j/(2*pressureKappa (scaledThermodynamicPressure Ξ.toEvenMixture)))=o[atTop] δ := by
  have hκ : Tendsto (fun j=>d.revisedBifurcationKappa (p j)) atTop
      (𝓝 (pressureKappa (scaledThermodynamicPressure Ξ.toEvenMixture))) := by
    simpa only [inf_idem,Function.comp_def] using
      d.revisedBifurcationKappa_limit.comp (hp.inf (tendsto_principal.mpr he))
  apply branch_mass_diagonal_small_o δ
    (fun j=>d.newAtomMass (p j) (d.couplingCurve (p j) 1+δ j))
    (fun j=>d.revisedBifurcationKappa (p j)) d.pressureKappa_positive hC hδ hκ hpos
  filter_upwards [hp.eventually H,he,hpos,hδ.eventually
    (eventually_lt_nhds (div_pos d.couplingMargin_pos (by norm_num : (0:ℝ)<2)))] with j hj heven hpositive hsmall
  obtain ⟨hpj,hnj,Hj⟩:=hj.2 heven
  obtain ⟨hlam,_,_,Hmass,_⟩:=Hj.2.2.2.2 (δ j) ⟨hpositive,hsmall.le⟩
  exact Hmass

end LimitingStandingData

def RevisedGardnerAsymptoticsTarget (Ξ:AdmissibleCovariance) {r:ℕ}
    (seed:AtomicPoint r) : Prop :=
  ∃d:LimitingStandingData Ξ seed,
    d.couplingMargin∈Ioo (0:ℝ) d.criticalCoupling ∧
    0<pressureKappa (scaledThermodynamicPressure Ξ.toEvenMixture) ∧
    (∀ᶠ p : ℕ in atTop, ∀ _he : Even p, ∀ theta ∈ d.parameterWindow,
      HasDerivAt (fun m => d.revisedScalarObjective p (theta.1, m))
        (d.stationaryMassFunction p theta) theta.2) ∧
    Tendsto d.revisedBifurcationKappa (atTop⊓𝓟 {p:ℕ|Even p})
      (𝓝 (pressureKappa (scaledThermodynamicPressure Ξ.toEvenMixture))) ∧
    ∃C:ℝ,1≤C ∧
    (∀ᶠp:ℕ in atTop,4≤p ∧ ∀he:Even p,∃hp:4≤p,∃hn:p∉Ξ.degrees,
      d.RevisedGardnerAsymptoticsAt C p hp he hn) ∧
    (∀p:ℕ→ℕ,∀δ:ℕ→ℝ,Tendsto p atTop atTop→(∀ᶠj in atTop,Even (p j))→
      Tendsto δ atTop (𝓝 0)→(∀ᶠj in atTop,0<δ j)→
      (fun j=>d.newAtomMass (p j) (d.couplingCurve (p j) 1+δ j)-
        δ j/(2*pressureKappa (scaledThermodynamicPressure Ξ.toEvenMixture)))=o[atTop] δ)

/-- The revised Corollary 5.2 normalization and parameter window, with
all asymptotic conclusions about the actual minimizing new atom. -/
theorem revised_gardner_asymptotics (Ξ:AdmissibleCovariance) {r:ℕ}
    (seed:AtomicPoint r) (hz:IsAtomicPoint seed) (hnd:Nondegenerate Ξ seed hz) :
    RevisedGardnerAsymptoticsTarget Ξ seed := by
  obtain ⟨d,gamma,hg,_,htail,hcost⟩:=exists_standing_cutoff_data Ξ seed hz hnd
  obtain ⟨C,hC,H⟩:=d.revised_gardner_asymptotics_eventually hg
    (fun m=>htail m d.cutoff ⟨le_rfl,d.cutoff_mem.2.le⟩) hcost
  exact ⟨d,d.couplingMargin_mem,d.pressureKappa_positive,d.revisedScalarObjective_massDerivative_eventually,
    d.revisedBifurcationKappa_limit,C,hC,H,
    fun p δ hp he hδ hpos=>d.revised_newAtomMass_diagonal_small_o (by linarith) H p δ hp he hδ hpos⟩

end GeneralDepthPaper
