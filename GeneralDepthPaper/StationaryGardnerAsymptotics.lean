module

public import GeneralDepthPaper.GardnerTransition
public import GeneralDepthPaper.StationaryAtomMassAsymptotics

@[expose] public section


/-! Literal Corollary 5.2: the new atom belongs to the actual minimizing
measure, and both its mass and its position obey the asserted asymptotics. -/
noncomputable section
open Set Filter MeasureTheory Asymptotics Metric
open scoped Topology NNReal
namespace GeneralDepthPaper
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 64

theorem twoLevelMeasure_top_mass {r:ℕ} (z:AtomicPoint r) (hz:IsAtomicPoint z)
    (m:ℝ) (hm:m∈Icc (0:ℝ) 1) (Q:Overlap)
    (hQ:atomicLocation z (Fin.last r)<(Q:ℝ)) :
    ((twoLevelMeasure z hz m Q:Measure Overlap) {Q}).toReal=1-m := by
  have hzero:=atomicMeasure_top_mass_zero z hz Q hQ
  change (((Paper.parisiMix (Measure.dirac Q).toProbabilityMeasure (atomicMeasure z hz) m:
    Measure Overlap) {Q}).toReal)=1-m
  rw [Paper.parisiMix_measure _ _ _ hm]
  change (ENNReal.ofReal (1-m)*(Measure.dirac Q {Q})+
    ENNReal.ofReal m*(atomicMeasure z hz:Measure Overlap) {Q}).toReal=1-m
  rw [hzero]
  simp [ENNReal.toReal_ofReal (sub_nonneg.mpr hm.2)]

namespace LimitingStandingData
variable {Ξ:AdmissibleCovariance} {r:ℕ} {seed:AtomicPoint r}

theorem pressureKappa_positive (d:LimitingStandingData Ξ seed) :
    0<pressureKappa (scaledThermodynamicPressure Ξ.toEvenMixture) := by
  have h:=d.ell_slope 1 ⟨d.massLower_mem.2.le,le_rfl⟩
  rw [deriv_pressureEll_one _
    ((d.pressure_smooth 1 ⟨d.massLower_mem.2.le,le_rfl⟩).of_le (by simp))] at h
  linarith [d.slope_pos]

def newAtomMass (d:LimitingStandingData Ξ seed) (p:ℕ) (lam:ℝ) : ℝ :=
  ((d.interiorCandidate p lam:Measure Overlap) {d.interiorTop p lam}).toReal

def GardnerAsymptoticsAt (d:LimitingStandingData Ξ seed) (C eta0:ℝ)
    (p:ℕ) (hp:4≤p) (he:Even p) (hn:p∉Ξ.degrees) : Prop :=
  |d.couplingCurve p 1-d.criticalCoupling|<d.couplingMargin/2 ∧
  0<d.bifurcationKappa p ∧
  ∀δ∈Ioc (0:ℝ) eta0,
    let lam:=d.couplingCurve p 1+δ
    ∃hlam:lam∈d.transitionWindow,
    let X:=Ξ.addHighDegree p hp he hn lam (d.transition_coupling_pos hlam)
    d.interiorCandidate p lam=parisiMinimizer X ∧
    d.newAtomMass p lam=1-d.bifurcatingMass p lam ∧
    |d.newAtomMass p lam-δ/(2*d.bifurcationKappa p)|≤C*δ^2 ∧
    C⁻¹*(p:ℝ)^(-(1/2:ℝ))*Real.exp (-d.bifurcatingMass p lam^2*lam*(p:ℝ)/2)
      ≤1-(d.interiorTop p lam:ℝ) ∧
    1-(d.interiorTop p lam:ℝ)≤
      C*(p:ℝ)^(-(1/2:ℝ))*Real.exp (-d.bifurcatingMass p lam^2*lam*(p:ℝ)/2)

theorem gardner_asymptotics_eventually (d:LimitingStandingData Ξ seed) {gamma:ℝ}
    (hg:0<gamma) (hmargin:∀m:d.MassInterval,d.limitingVariation m d.cutoff≤ -4*gamma)
    (hcost:(1/2:ℝ)*(∫q in d.cutoff..1,(1-q)*Ξ.second q)≤gamma) :
    ∃eta0:ℝ,eta0∈Ioo (0:ℝ) (d.couplingMargin/2) ∧
    ∃C:ℝ,0<C ∧ ∀ᶠp:ℕ in atTop,4≤p ∧ ∀he:Even p,
      ∃hp:4≤p,∃hn:p∉Ξ.degrees,d.GardnerAsymptoticsAt C eta0 p hp he hn := by
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
    simpa only [Metric.mem_ball,Real.dist_eq,criticalCoupling,mem_setOf_eq] using H
  let C:=max (max Cm D) b⁻¹+1
  have hC : 0<C:=by dsimp only [C];positivity
  have hCmC:Cm≤C:=by dsimp only [C];linarith [le_max_left Cm D,le_max_left (max Cm D) b⁻¹]
  have hDC:D≤C:=by dsimp only [C];linarith [le_max_right Cm D,le_max_left (max Cm D) b⁻¹]
  have hCb:b⁻¹≤C:=by dsimp only [C];linarith [le_max_right (max Cm D) b⁻¹]
  have hCi:C⁻¹≤b:=by
    have hh:=one_div_le_one_div_of_le (inv_pos.mpr hb) hCb
    simpa only [one_div,inv_inv] using hh
  refine ⟨d.couplingMargin/4,⟨div_pos d.couplingMargin_pos (by norm_num),
    by linarith [d.couplingMargin_pos]⟩,C,hC,?_⟩
  filter_upwards [d.gardner_interior_geometry hg hmargin hcost,Hmass,Hroot,Hs,Hclose,
    d.stationary_interior_response_zero] with p hgeo hmass hroot hs hclose hzero
  refine ⟨hgeo.1,?_⟩
  intro he
  obtain ⟨hp,hn,Hgeo⟩:=hgeo.2 he
  obtain ⟨hp',hn',Hr⟩:=hroot.2 he
  refine ⟨hp,hn,hclose he,(hmass he).1,?_⟩
  intro δ hδ
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
  refine ⟨hlam,?_,hmassid,?_,?_,?_⟩
  · rw [d.interiorCandidate_eq p lam hz]
    exact H.2.2.2.1
  · rw [hmassid]
    exact ((hmass he).2 δ ⟨hδ.1,by linarith [hδ.2,d.couplingMargin_pos]⟩).trans
      (mul_le_mul_of_nonneg_right hCmC (sq_nonneg δ))
  · exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCi (Real.rpow_nonneg (Nat.cast_nonneg p) _))
        (Real.exp_pos _).le).trans Hrt.2.2.2.2.1
  · exact Hrt.2.2.2.2.2.1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hDC (Real.rpow_nonneg (Nat.cast_nonneg p) _))
        (Real.exp_pos _).le)

theorem newAtomMass_diagonal_small_o (d:LimitingStandingData Ξ seed)
    {eta0 C:ℝ} (hη:0<eta0) (hC:0≤C)
    (H:∀ᶠp:ℕ in atTop,4≤p ∧ ∀he:Even p,∃hp:4≤p,∃hn:p∉Ξ.degrees,
      d.GardnerAsymptoticsAt C eta0 p hp he hn)
    (p:ℕ→ℕ) (δ:ℕ→ℝ) (hp:Tendsto p atTop atTop)
    (he:∀ᶠj in atTop,Even (p j)) (hδ:Tendsto δ atTop (𝓝 0))
    (hpos:∀ᶠj in atTop,0<δ j) :
    (fun j=>d.newAtomMass (p j) (d.couplingCurve (p j) 1+δ j)-
      δ j/(2*pressureKappa (scaledThermodynamicPressure Ξ.toEvenMixture)))=o[atTop] δ := by
  have hκ : Tendsto (fun j=>d.bifurcationKappa (p j)) atTop
      (𝓝 (pressureKappa (scaledThermodynamicPressure Ξ.toEvenMixture))) := by
    simpa only [inf_idem,Function.comp_def] using
      d.bifurcationKappa_limit.comp (hp.inf (tendsto_principal.mpr he))
  apply branch_mass_diagonal_small_o δ
    (fun j=>d.newAtomMass (p j) (d.couplingCurve (p j) 1+δ j))
    (fun j=>d.bifurcationKappa (p j)) d.pressureKappa_positive hC hδ hκ hpos
  filter_upwards [hp.eventually H,he,hpos,hδ.eventually
    (eventually_lt_nhds hη)] with j hj heven hpositive hsmall
  obtain ⟨hpj,hnj,Hj⟩:=hj.2 heven
  obtain ⟨hlam,_,_,Hmass,_⟩:=Hj.2.2 (δ j) ⟨hpositive,hsmall.le⟩
  exact Hmass

end LimitingStandingData

def GardnerAsymptoticsTarget (Ξ:AdmissibleCovariance) {r:ℕ} (seed:AtomicPoint r) : Prop :=
  ∃d:LimitingStandingData Ξ seed,
    d.couplingMargin∈Ioo (0:ℝ) d.criticalCoupling ∧
    0<pressureKappa (scaledThermodynamicPressure Ξ.toEvenMixture) ∧
    Tendsto d.bifurcationKappa (atTop⊓𝓟 {p:ℕ|Even p})
      (𝓝 (pressureKappa (scaledThermodynamicPressure Ξ.toEvenMixture))) ∧
    ∃eta0:ℝ,eta0∈Ioo (0:ℝ) (d.couplingMargin/2) ∧
    ∃C:ℝ,0<C ∧
    (∀ᶠp:ℕ in atTop,4≤p ∧ ∀he:Even p,∃hp:4≤p,∃hn:p∉Ξ.degrees,
      d.GardnerAsymptoticsAt C eta0 p hp he hn) ∧
    (∀p:ℕ→ℕ,∀δ:ℕ→ℝ,Tendsto p atTop atTop→(∀ᶠj in atTop,Even (p j))→
      Tendsto δ atTop (𝓝 0)→(∀ᶠj in atTop,0<δ j)→
      (fun j=>d.newAtomMass (p j) (d.couplingCurve (p j) 1+δ j)-
        δ j/(2*pressureKappa (scaledThermodynamicPressure Ξ.toEvenMixture)))=o[atTop] δ)

/-- Corollary 5.2 with the actual selected minimizing atom, including the
uniform quadratic mass law, the two-sided location law, and diagonal o(delta). -/
theorem gardner_asymptotics (Ξ:AdmissibleCovariance) {r:ℕ} (seed:AtomicPoint r)
    (hz:IsAtomicPoint seed) (hnd:Nondegenerate Ξ seed hz) : GardnerAsymptoticsTarget Ξ seed := by
  obtain ⟨d,gamma,hg,_,htail,hcost⟩:=exists_standing_cutoff_data Ξ seed hz hnd
  obtain ⟨eta0,hη,C,hC,H⟩:=d.gardner_asymptotics_eventually hg
    (fun m=>htail m d.cutoff ⟨le_rfl,d.cutoff_mem.2.le⟩) hcost
  exact ⟨d,d.couplingMargin_mem,d.pressureKappa_positive,d.bifurcationKappa_limit,
    eta0,hη,C,hC,H,fun p δ hp he hδ hpos=>d.newAtomMass_diagonal_small_o hη.1 hC.le H p δ hp he hδ hpos⟩

end GeneralDepthPaper
