module

public import GeneralDepthPaper.RevisedGeometryLocation

@[expose] public section

/-! Revision (16), Theorem 4.12, with a common support cutoff and endpoint
constant. This assembles the retained phase theorem with its actual support,
zero-mass critical contact, and location estimates. The input covariance and
nondegeneracy classes remain the established classes of this development. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace GeneralDepthPaper
namespace LimitingStandingData
variable {Ξ : AdmissibleCovariance} {r : ℕ} {seed : AtomicPoint r}

def RevisedGardnerGeometryAt (d : LimitingStandingData Ξ seed) (C : ℝ)
    (p : ℕ) (hp : 4 ≤ p) (he : Even p) (hn : p ∉ Ξ.degrees)
    (lam : ℝ) (hlam : lam ∈ d.transitionWindow) : Prop :=
  let X := Ξ.addHighDegree p hp he hn lam (d.transition_coupling_pos hlam)
  let critical := d.couplingCurve p 1
  d.GardnerOptimizerAt p hp he hn lam hlam ∧
  d.GardnerNondegenerateAt p hp he hn lam hlam ∧
  (lam ≤ critical →
    FRSB.parisiSupport (parisiMinimizer X) ⊆ Icc (0 : ℝ) d.cutoff ∧
    (d.massOneTop p lam : ℝ) ∈ Ioo d.cutoff 1 ∧
    GardnerLocationScale C p 1 lam (d.massOneTop p lam)) ∧
  (lam = critical →
    (∀ q ∈ Icc (0 : ℝ) 1, firstVariation X (parisiMinimizer X) q ≤ 0) ∧
    {q ∈ Icc (0 : ℝ) 1 | firstVariation X (parisiMinimizer X) q = 0} =
      FRSB.parisiSupport (parisiMinimizer X) ∪ {(d.massOneTop p lam : ℝ)} ∧
    (d.massOneTop p lam : ℝ) ∉ FRSB.parisiSupport (parisiMinimizer X) ∧
    (parisiMinimizer X : Measure Overlap) {d.massOneTop p lam} = 0) ∧
  (critical < lam →
    ∃ hz : IsAtomicPoint (d.stationaryBranch p (lam, d.bifurcatingMass p lam)),
    let z := d.stationaryBranch p (lam, d.bifurcatingMass p lam)
    let m := d.bifurcatingMass p lam
    parisiMinimizer X = twoLevelMeasure z hz m (d.interiorTop p lam) ∧
    m ∈ Ioo (0 : ℝ) 1 ∧
    IsFiniteRSB r (atomicMeasure z hz) ∧
    FRSB.parisiSupport (atomicMeasure z hz) ⊆ Icc (0 : ℝ) d.cutoff ∧
    (d.interiorTop p lam : ℝ) ∈ Ioo d.cutoff 1 ∧
    GardnerLocationScale C p m lam (d.interiorTop p lam))

theorem revised_gardner_geometry_eventually (d : LimitingStandingData Ξ seed) {gamma : ℝ}
    (hg : 0 < gamma)
    (hmargin : ∀ m : d.MassInterval, d.limitingVariation m d.cutoff ≤ -4 * gamma)
    (hcost : (1 / 2 : ℝ) * (∫ q in d.cutoff..1, (1 - q) * Ξ.second q) ≤ gamma) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ p : ℕ in atTop, 4 ≤ p ∧ ∀ he : Even p,
      ∃ hp : 4 ≤ p, ∃ hn : p ∉ Ξ.degrees,
        d.couplingCurve p 1 ∈ Ioo (d.criticalCoupling - d.couplingMargin)
          (d.criticalCoupling + d.couplingMargin) ∧
        ∀ lam : ℝ, ∀ hlam : lam ∈ d.transitionWindow,
          d.RevisedGardnerGeometryAt C p hp he hn lam hlam := by
  obtain ⟨C, hC, Hloc⟩ := d.revisedCandidateLocation_eventually
  refine ⟨C, hC, ?_⟩
  filter_upwards [d.gardner_optimizer hg hmargin hcost,
    d.gardner_nondegenerate hg hmargin hcost,
    d.gardner_mass_one_geometry hg hmargin hcost,
    d.gardner_interior_geometry hg hmargin hcost,
    d.stationary_interior_response_zero, Hloc] with p hop hnd hmass hinter hzero hloc
  refine ⟨hop.1, ?_⟩
  intro he
  obtain ⟨hp, hn, hcrit, Hop⟩ := hop.2 he
  obtain ⟨hpnd, hnnd, Hnd⟩ := hnd.2 he
  obtain ⟨hpm, hnm, Hmass⟩ := hmass.2 he
  obtain ⟨hpi, hni, Hinter⟩ := hinter.2 he
  refine ⟨hp, hn, hcrit, ?_⟩
  intro lam hlam
  let X := Ξ.addHighDegree p hp he hn lam (d.transition_coupling_pos hlam)
  have Ho := Hop lam hlam
  have Hn := Hnd lam hlam
  obtain ⟨hz, Hm⟩ := Hmass lam hlam
  have ht : (lam, (1 : ℝ)) ∈ d.parameterWindow :=
    ⟨d.transitionWindow_subset hlam, ⟨d.massLower_mem.2.le, le_rfl⟩⟩
  have Hl := hloc he (lam, 1) ht hz
  have hmeasure := d.massOneCandidate_eq p lam hz
  have hlow (hle : lam ≤ d.couplingCurve p 1) :
      atomicMeasure (d.stationaryBranch p (lam, 1)) hz = parisiMinimizer X :=
    hmeasure.symm.trans (Ho.1 hle).1
  refine ⟨Ho, Hn, ?_, ?_, ?_⟩
  · intro hle
    rw [←hlow hle]
    exact Hl
  · intro heq
    have Hcritical := Hm.2.2 heq
    rw [←hlow heq.le]
    refine ⟨Hcritical.1, Hcritical.2.1, ?_, Hcritical.2.2⟩
    intro hsupport
    have hbound := Hl.1 hsupport
    exact (not_le_of_gt Hl.2.1.1) hbound.2
  · intro habove
    obtain ⟨hzi, Hi⟩ := Hinter lam hlam habove
    let m := d.bifurcatingMass p lam
    have hm : m ∈ Ioo d.massLower 1 := (hzero he lam ⟨habove, hlam.2⟩).1
    have hti : (lam, m) ∈ d.parameterWindow :=
      ⟨d.transitionWindow_subset hlam, Ioo_subset_Icc_self hm⟩
    have Hli := hloc he (lam, m) hti hzi
    refine ⟨hzi, ?_, Hi.1, atomicMeasure_isFiniteRSB _ _, Hli⟩
    exact Hi.2.2.2.1.symm

end LimitingStandingData

def RevisedGardnerGeometryTarget (Ξ : AdmissibleCovariance) {r : ℕ}
    (seed : AtomicPoint r) : Prop :=
  ∃ d : LimitingStandingData Ξ seed,
    d.couplingMargin ∈ Ioo (0 : ℝ) d.criticalCoupling ∧
    d.cutoff ∈ Ioo (0 : ℝ) 1 ∧
    d.criticalCoupling = 2 * ((scaledThermodynamicPressure Ξ.toEvenMixture) 1 -
      deriv (scaledThermodynamicPressure Ξ.toEvenMixture) 1) ∧
    Tendsto (fun p : ℕ => d.couplingCurve p 1) (atTop ⊓ 𝓟 {p : ℕ | Even p})
      (𝓝 d.criticalCoupling) ∧
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ p : ℕ in atTop, 4 ≤ p ∧ ∀ he : Even p,
      ∃ hp : 4 ≤ p, ∃ hn : p ∉ Ξ.degrees,
        d.couplingCurve p 1 ∈ Ioo (d.criticalCoupling - d.couplingMargin)
          (d.criticalCoupling + d.couplingMargin) ∧
        ∀ lam : ℝ, ∀ hlam : lam ∈ d.transitionWindow,
          d.RevisedGardnerGeometryAt C p hp he hn lam hlam

/-- The retained Gardner theorem with all revised support, critical-contact,
and common location constants assembled explicitly. -/
theorem revised_gardner_geometry (Ξ : AdmissibleCovariance) {r : ℕ}
    (seed : AtomicPoint r) (hz : IsAtomicPoint seed) (hnd : Nondegenerate Ξ seed hz) :
    RevisedGardnerGeometryTarget Ξ seed := by
  obtain ⟨d, gamma, hg, _, htail, hcost⟩ := exists_standing_cutoff_data Ξ seed hz hnd
  obtain ⟨C, hC, H⟩ := d.revised_gardner_geometry_eventually hg
    (fun m => htail m d.cutoff ⟨le_rfl, d.cutoff_mem.2.le⟩) hcost
  exact ⟨d, d.couplingMargin_mem, d.cutoff_mem, d.criticalCoupling_eq_entropy,
    d.couplingCurve_critical_limit, C, hC, H⟩

end GeneralDepthPaper
