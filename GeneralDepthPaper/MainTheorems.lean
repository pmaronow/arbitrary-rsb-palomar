module

public import GeneralDepthPaper.AllDepthIteration

@[expose] public section


/-! Open-phase existence and the original development's existential
all-depth transition conclusion. The coefficient families and Parisi
optimizers are the actual mixed-even objects. Revision (16) strengthens
Theorem 1.2 to a universal statement; see COVERAGE.md for its restrictions. -/
noncomputable section
open Set
open scoped Topology BigOperators
namespace GeneralDepthPaper
set_option maxHeartbeats 1800000

def ArbitraryDepthOpenTarget (k : ℕ) : Prop :=
  ∃p:Fin (k+1)→ℕ,∃hp:∀i,4≤p i,∃he:∀i,Even (p i),StrictMono p ∧ p 0=4 ∧
    ∃O:Set (Fin (k+1)→ℝ),IsOpen O ∧ O.Nonempty ∧ O⊆positiveCoefficientDomain k ∧
      ∀c∈O,∃hc:c∈positiveCoefficientDomain k,
        let X:=indexedCovariance p hp he c hc
        IsFiniteRSB k (parisiMinimizer X) ∧
          ∃z:AtomicPoint k,∃hz:IsAtomicPoint z,Nondegenerate X z hz

/-- Theorem 1.1. This proves the stronger formulation including depth zero. -/
theorem arbitrary_finite_depth_open_set (k : ℕ) : ArbitraryDepthOpenTarget k := by
  obtain ⟨D,z,hz,hnd⟩:=arbitrary_depth_iteration k
  let O:=nondegenerateCoefficientLocus D.exponent D.exponent_ge_four D.exponent_even k
  have hO : IsOpen O:=isOpen_nondegenerateCoefficientLocus _ _ _ _
  have hnon : O.Nonempty:=nondegenerate_coefficient_locus_nonempty D.covariance D.exponent
    D.exponent_ge_four D.exponent_even D.increasing.injective D.degrees_eq z hz hnd
  refine ⟨D.exponent,D.exponent_ge_four,D.exponent_even,D.increasing,D.first_exponent,
    O,hO,hnon,?_,?_⟩
  · rintro c ⟨hc,_,_,_⟩
    exact hc
  · intro c hc
    obtain ⟨hpos,w,hw,Hw⟩:=hc
    refine ⟨hpos,?_,w,hw,Hw⟩
    rw [←parisiMinimizer_unique _ _ Hw.1]
    exact atomicMeasure_isFiniteRSB w hw

def ArbitraryDepthTransitionTarget (r : ℕ) : Prop :=
  ∃X:AdmissibleCovariance,∃z:AtomicPoint r,∃hz:IsAtomicPoint z,
    IsFiniteRSB r (parisiMinimizer X) ∧ Nondegenerate X z hz ∧
    0<(scaledThermodynamicPressure X.toEvenMixture) 1-
      deriv (scaledThermodynamicPressure X.toEvenMixture) 1 ∧
    GardnerTransitionTarget X z

/-- The earlier manuscript's existential Theorem 1.2: a Gardner transition
starts at some constructed covariance at every finite depth, with positive
physical entropy critical coupling. Revision (16)'s Theorem 1.2 is universal
in the supplied admissible base; this declaration is its narrower
existential occurrence conclusion. See `gardner_transition` and COVERAGE.md. -/
theorem arbitrary_depth_gardner_transition (r : ℕ) : ArbitraryDepthTransitionTarget r := by
  obtain ⟨D,z,hz,hnd⟩:=arbitrary_depth_iteration r
  have H:=gardner_transition D.covariance z hz hnd
  have hentropy : 0<(scaledThermodynamicPressure D.covariance.toEvenMixture) 1-
      deriv (scaledThermodynamicPressure D.covariance.toEvenMixture) 1 := by
    obtain ⟨d,heta,heq,_⟩:=H
    rw [heq] at heta
    linarith [heta.1,heta.2]
  refine ⟨D.covariance,z,hz,?_,hnd,hentropy,H⟩
  rw [←parisiMinimizer_unique _ _ hnd.1]
  exact atomicMeasure_isFiniteRSB z hz

end GeneralDepthPaper
