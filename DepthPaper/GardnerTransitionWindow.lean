module

public import DepthPaper.StationaryPhaseSigns

@[expose] public section


/-! The literal transition window and its critical coupling are derived
from the actual pressure corner and the constructed finite-degree roots. -/
noncomputable section
open Set Filter
open scoped Topology
namespace DepthPaper
namespace LimitingStandingData
variable {Ξ : AdmissibleCovariance} {r : ℕ} {seed : AtomicPoint r}

def criticalCoupling (d : LimitingStandingData Ξ seed) : ℝ :=
  pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) 1

def transitionWindow (d : LimitingStandingData Ξ seed) : Set ℝ :=
  Icc (d.criticalCoupling-d.couplingMargin) (d.criticalCoupling+d.couplingMargin)

theorem couplingMargin_mem (d : LimitingStandingData Ξ seed) :
    d.couplingMargin∈Ioo (0:ℝ) d.criticalCoupling := by
  refine ⟨d.couplingMargin_pos,?_⟩
  dsimp only [criticalCoupling]
  linarith [d.couplingMargin_pos,d.couplingMargin_small]

theorem transitionWindow_subset (d : LimitingStandingData Ξ seed) :
    d.transitionWindow⊆Icc d.couplingLower d.couplingUpper := by
  intro lam hlam
  dsimp only [transitionWindow,criticalCoupling] at hlam
  dsimp only [couplingLower,couplingUpper]
  constructor <;> linarith [d.couplingMargin_pos,d.couplingMargin_gap,hlam.1,hlam.2]

theorem criticalCoupling_in_transition_eventually (d : LimitingStandingData Ξ seed) :
    ∀ᶠp:ℕ in atTop,∀he:Even p,
      d.couplingCurve p 1∈Ioo (d.criticalCoupling-d.couplingMargin)
        (d.criticalCoupling+d.couplingMargin) := by
  obtain ⟨C,_,A,c,hc,H⟩:=d.couplingCurve_eventually
  have Hsmall:∀ᶠp:ℕ in atTop,C*(p:ℝ)^A*Real.exp (-c*(p:ℝ))<d.couplingMargin :=
    (tendsto_nat_polynomial_exp C c A hc).eventually
      (eventually_lt_nhds d.couplingMargin_pos)
  filter_upwards [H,Hsmall] with p hp hsmall he
  have hh:=(hp he 1 ⟨d.massLower_mem.2.le,le_rfl⟩).2.2.2.2.1.trans_lt hsmall
  have ha:=abs_lt.mp hh
  dsimp only [criticalCoupling]
  constructor <;> linarith [ha.1,ha.2]

theorem transition_coupling_pos (d : LimitingStandingData Ξ seed) {lam : ℝ}
    (hlam : lam∈d.transitionWindow) : 0<lam :=
  d.couplingLower_pos.trans_le (d.transitionWindow_subset hlam).1

end LimitingStandingData
end DepthPaper
