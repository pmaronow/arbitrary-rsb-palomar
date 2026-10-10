module

public import GeneralDepthPaper.RevisedNondegeneracyBridge
public import GeneralDepthPaper.RevisedGeometry
public import GeneralDepthPaper.RevisedAsymptotics

@[expose] public section

/-! Universal high-degree Gardner transition for the revised paper's
admissible covariance class. Active degrees are positive even integers
at least two. The only origin assumption is Ξ''(0)<1, and the seed
hypothesis is the paper's nondegeneracy condition. The positive atomic
Hessian is derived internally rather than supplied by the caller. -/
noncomputable section
open Set Filter
open scoped Topology
namespace GeneralDepthPaper

/-- Revised Theorem 4.12 for every admissible finite polynomial covariance
with a nondegenerate finite-step Parisi measure. The target includes
actual optimizer identification, support and critical zero-mass contact,
phase nondegeneracy, and a common endpoint-location constant. -/
theorem revised_gardner_geometry_of_paper_nondegenerate
    (Ξ : AdmissibleCovariance) {r : ℕ} (seed : AtomicPoint r)
    (hz : IsAtomicPoint seed) (hsub : Ξ.IsSubcritical)
    (hND : PaperNondegenerate Ξ seed hz) :
    RevisedGardnerGeometryTarget Ξ seed :=
  revised_gardner_geometry Ξ seed hz
    (nondegenerate_of_paperNondegenerate Ξ seed hz hND hsub)

/-- Revised Corollary 5.2 with its actual derivative-ratio normalization,
half-window mass asymptotics, logarithmic atom location, and diagonal
small-o law, on the full admissible covariance and paper seed class. -/
theorem revised_gardner_asymptotics_of_paper_nondegenerate
    (Ξ : AdmissibleCovariance) {r : ℕ} (seed : AtomicPoint r)
    (hz : IsAtomicPoint seed) (hsub : Ξ.IsSubcritical)
    (hND : PaperNondegenerate Ξ seed hz) :
    RevisedGardnerAsymptoticsTarget Ξ seed :=
  revised_gardner_asymptotics Ξ seed hz
    (nondegenerate_of_paperNondegenerate Ξ seed hz hND hsub)

/-- The universal revised transition and its finite-degree asymptotics.
There is no positive-Hessian premise and no exclusion of quadratic terms. -/
theorem universal_gardner_transition
    (Ξ : AdmissibleCovariance) {r : ℕ} (seed : AtomicPoint r)
    (hz : IsAtomicPoint seed) (hsub : Ξ.IsSubcritical)
    (hND : PaperNondegenerate Ξ seed hz) :
    RevisedGardnerGeometryTarget Ξ seed ∧ RevisedGardnerAsymptoticsTarget Ξ seed :=
  ⟨revised_gardner_geometry_of_paper_nondegenerate Ξ seed hz hsub hND,
    revised_gardner_asymptotics_of_paper_nondegenerate Ξ seed hz hsub hND⟩

/-- Literal revised Theorem 1.2. The pressure is the actual thermodynamic
pressure of b²Ξ; every phase assertion concerns its actual Parisi
minimizer. The critical threshold is unique in the stated open window. -/
theorem gardner_transition_theorem_1_2
    (Ξ : AdmissibleCovariance) {r : ℕ} (seed : AtomicPoint r)
    (hz : IsAtomicPoint seed) (hsub : Ξ.IsSubcritical)
    (hND : PaperNondegenerate Ξ seed hz) :
    let pressure := scaledThermodynamicPressure Ξ.toEvenMixture
    let s := pressure 1-deriv pressure 1
    0<s ∧ ∃η : ℝ,η∈Ioo (0 : ℝ) (2*s) ∧ ∃critical : ℕ→ℝ,
      Tendsto critical (atTop⊓𝓟 {p : ℕ|Even p}) (𝓝 (2*s)) ∧
      ∀ᶠp : ℕ in atTop,∀he : Even p,∃hp : 4≤p,∃hn : p∉Ξ.degrees,
        critical p∈Ioo (2*s-η) (2*s+η) ∧
        (∀lam : ℝ,∀hlam : lam∈Icc (2*s-η) (2*s+η),0<lam ∧ ∀hpos : 0<lam,
          let X := Ξ.addHighDegree p hp he hn lam hpos
          (IsFiniteRSB r (parisiMinimizer X) ↔ lam≤critical p) ∧
          (IsFiniteRSB (r+1) (parisiMinimizer X) ↔ critical p<lam)) ∧
        (∀c∈Ioo (2*s-η) (2*s+η),
          (∀lam : ℝ,∀hlam : lam∈Icc (2*s-η) (2*s+η),∀hpos : 0<lam,
            let X := Ξ.addHighDegree p hp he hn lam hpos
            (IsFiniteRSB r (parisiMinimizer X) ↔ lam≤c) ∧
            (IsFiniteRSB (r+1) (parisiMinimizer X) ↔ c<lam)) → c=critical p) := by
  dsimp only
  obtain ⟨d,hη,_,hentropy,hlimit,C,hC,H⟩ :=
    revised_gardner_geometry_of_paper_nondegenerate Ξ seed hz hsub hND
  have hs : 0<scaledThermodynamicPressure Ξ.toEvenMixture 1-
      deriv (scaledThermodynamicPressure Ξ.toEvenMixture) 1 := by
    linarith [hη.1,hη.2]
  refine ⟨hs,d.couplingMargin,?_,fun p=>d.couplingCurve p 1,?_,?_⟩
  · exact ⟨hη.1,by linarith [hη.2]⟩
  · simpa only [hentropy] using hlimit
  · filter_upwards [H] with p hpdata
    intro he
    obtain ⟨hp,hn,hcrit,Hgeo⟩ := hpdata.2 he
    have hcrit' : d.couplingCurve p 1∈Ioo
        (2*(scaledThermodynamicPressure Ξ.toEvenMixture 1-
          deriv (scaledThermodynamicPressure Ξ.toEvenMixture) 1)-d.couplingMargin)
        (2*(scaledThermodynamicPressure Ξ.toEvenMixture 1-
          deriv (scaledThermodynamicPressure Ξ.toEvenMixture) 1)+d.couplingMargin) := by
      simpa only [hentropy] using hcrit
    refine ⟨hp,hn,hcrit',?_,?_⟩
    · intro lam hlam
      have hlamd : lam∈d.transitionWindow := by
        change lam∈Icc (d.criticalCoupling-d.couplingMargin)
          (d.criticalCoupling+d.couplingMargin)
        simpa only [hentropy] using hlam
      refine ⟨d.transition_coupling_pos hlamd,?_⟩
      intro hpos
      have Hopt := (Hgeo lam hlamd).1
      exact ⟨Hopt.2.2.2.2.1,Hopt.2.2.2.2.2⟩
    · intro c hc Hc
      have hcd : c∈d.transitionWindow := by
        change c∈Icc (d.criticalCoupling-d.couplingMargin)
          (d.criticalCoupling+d.couplingMargin)
        simpa only [hentropy] using Ioo_subset_Icc_self hc
      have hcriticald : d.couplingCurve p 1∈d.transitionWindow :=
        Ioo_subset_Icc_self hcrit
      have hcle : c≤d.couplingCurve p 1 := by
        have Hopt := (Hgeo c hcd).1
        exact Hopt.2.2.2.2.1.mp
          ((Hc c (Ioo_subset_Icc_self hc) (d.transition_coupling_pos hcd)).1.mpr le_rfl)
      have hcge : d.couplingCurve p 1≤c := by
        have Hopt := (Hgeo (d.couplingCurve p 1) hcriticald).1
        exact (Hc (d.couplingCurve p 1) (Ioo_subset_Icc_self hcrit')
          (d.transition_coupling_pos hcriticald)).1.mp (Hopt.2.2.2.2.1.mpr le_rfl)
      exact le_antisymm hcle hcge

end GeneralDepthPaper
