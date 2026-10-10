module

public import GeneralDepthPaper.GardnerTransition
public import GeneralDepthPaper.OrderedCovarianceModels

@[expose] public section


/-! Genuine iteration of the actual Gardner transition. Every finite
depth is attained by a positive finite mixed-even polynomial, with ordered
exponents beginning at four and a nondegenerate actual Parisi measure. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace GeneralDepthPaper
set_option maxHeartbeats 2600000

theorem exists_larger_nondegenerate_model {k : ℕ} (D : OrderedCovarianceModel k)
    (z : AtomicPoint k) (hz : IsAtomicPoint z) (hnd : Nondegenerate D.covariance z hz) :
    ∃E:OrderedCovarianceModel (k+1),∃w:AtomicPoint (k+1),∃hw:IsAtomicPoint w,
      Nondegenerate E.covariance w hw := by
  obtain ⟨d,heta,_,_,H⟩:=gardner_transition D.covariance z hz hnd
  obtain ⟨N,hN⟩:=eventually_atTop.mp H
  let p : ℕ:=2*(max N (D.exponent (Fin.last k))+1)
  have hpN:N≤p:=by dsimp only [p];omega
  have hpD:D.exponent (Fin.last k)<p:=by dsimp only [p];omega
  have he : Even p:=⟨max N (D.exponent (Fin.last k))+1,by dsimp only [p];omega⟩
  obtain ⟨hp,hn,hcritical,Hp⟩:=(hN p hpN).2 he
  let lam:=d.criticalCoupling+d.couplingMargin
  have hlam : lam∈d.transitionWindow:=⟨by dsimp only [lam];linarith [heta.1],le_rfl⟩
  have hlpos:0<lam:=d.transition_coupling_pos hlam
  have hlt:d.couplingCurve p 1<lam:=hcritical.2
  obtain ⟨hw,Hw⟩:=(Hp lam hlam).2.2 hlt
  exact ⟨D.extend p hpD he lam hlpos,_,hw,Hw⟩

/-- Proposition 5.1 of Revision (16), numbered 6.1 in the earlier manuscript:
the actual covariance, ordered degrees and atomic optimizer are constructed
at every natural-number depth. -/
theorem arbitrary_depth_iteration (k : ℕ) :
    ∃D:OrderedCovarianceModel k,∃z:AtomicPoint k,∃hz:IsAtomicPoint z,
      Nondegenerate D.covariance z hz := by
  induction k with
  | zero =>
    exact ⟨quarticOrderedModel,0,isAtomicPoint_zero_depth,quarticSeed_nondegenerate⟩
  | succ k hk =>
    obtain ⟨D,z,hz,hnd⟩:=hk
    exact exists_larger_nondegenerate_model D z hz hnd

def ArbitraryDepthPolynomialTarget (k : ℕ) : Prop :=
  ∃p:Fin (k+1)→ℕ,∃c:Fin (k+1)→ℝ,StrictMono p ∧ p 0=4 ∧
    (∀i,Even (p i)) ∧ (∀i,0<c i) ∧
    ∃X:AdmissibleCovariance,(∀q:ℝ,X.value q=∑i,c i*q^(p i)) ∧
      IsFiniteRSB k (parisiMinimizer X) ∧
      ∃z:AtomicPoint k,∃hz:IsAtomicPoint z,Nondegenerate X z hz

theorem arbitrary_depth_polynomial (k : ℕ) : ArbitraryDepthPolynomialTarget k := by
  obtain ⟨D,z,hz,hnd⟩:=arbitrary_depth_iteration k
  refine ⟨D.exponent,D.coefficients,D.increasing,D.first_exponent,D.exponent_even,D.coefficient_pos,
    D.covariance,D.value_eq,?_,z,hz,hnd⟩
  rw [←parisiMinimizer_unique D.covariance _ hnd.1]
  exact atomicMeasure_isFiniteRSB z hz

end GeneralDepthPaper
