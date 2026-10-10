module

public import DepthPaper.CutoffErrorCoordinateJets
public import DepthPaper.TwoParameterMultilinearBounds

@[expose] public section


/-! Uniform bounds on actual ordered Banach coordinate jets. Point values
and the first three actual spatial derivatives identify the terminal norm. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal BoundedContinuousFunction BigOperators
namespace DepthPaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

theorem small_logarithmicWordDerivative (w : List (Fin 2))
    (e : LogDeficitExpr MassResidualNormalizerExpr) (he : e.Small) :
    (logarithmicWordDerivative w e).Small := by
  induction w with
  | nil => exact he
  | cons i w ih =>
    fin_cases i
    · exact (logarithmicWordDerivative w e).small_differentiate
        MassResidualNormalizerExpr.dm deficitBaseExpr.lift.dm 1 ih
    · exact (logarithmicWordDerivative w e).small_differentiate
        MassResidualNormalizerExpr.dV deficitBaseExpr.lift.dV 0 ih

theorem terminalJet_cutoffError_coordinateWordJet
    (w : List (Fin 2)) {p : ℝ×ℝ} (hp : p∈cutoffErrorDomain) (i : Fin 3) (x : ℝ) :
    terminalJet (coordinateWordJet (fun q:ℝ×ℝ=>cutoffErrorTerminal q.1 q.2) w p) i x=
      (LogDeficitExpr.massDx^[((i:ℕ)+1)]
        (logarithmicWordDerivative w errorMassBaseExpr)).physicalEval p.1 p.2 x := by
  let J:=coordinateWordJet (fun q:ℝ×ℝ=>cutoffErrorTerminal q.1 q.2) w p
  let e:=logarithmicWordDerivative w errorMassBaseExpr
  have hv:terminalValue J=e.physicalEval p.1 p.2 :=
    funext (terminalValue_cutoffError_coordinateWordJet w hp)
  have h0 (y:ℝ):terminalJet J 0 y=e.massDx.physicalEval p.1 p.2 y := by
    exact (hasDerivAt_terminalValue J y).unique
      (hv.symm ▸ e.hasDerivAt_physicalEval_space hp.1 hp.2 y)
  have h1 (y:ℝ):terminalJet J 1 y=e.massDx.massDx.physicalEval p.1 p.2 y := by
    have he:(terminalJet J 0:ℝ→ℝ)=e.massDx.physicalEval p.1 p.2 :=funext h0
    exact (hasDerivAt_terminalJet_zero J y).unique
      (he.symm ▸ e.massDx.hasDerivAt_physicalEval_space hp.1 hp.2 y)
  have h2 (y:ℝ):terminalJet J 2 y=e.massDx.massDx.massDx.physicalEval p.1 p.2 y := by
    have he:(terminalJet J 1:ℝ→ℝ)=e.massDx.massDx.physicalEval p.1 p.2 :=funext h1
    exact (hasDerivAt_terminalJet_one J y).unique
      (he.symm ▸ e.massDx.massDx.hasDerivAt_physicalEval_space hp.1 hp.2 y)
  fin_cases i
  · exact h0 x
  · exact h1 x
  · exact h2 x

theorem cutoffError_coordinateWordJet_exponential_bound
    (w : List (Fin 2)) {ε : ℝ} (hε : 0<ε) :
    ∃C:ℝ,0<C ∧ ∃D:ℕ,∀m∈Icc ε 1,∀V>1,
      ‖coordinateWordJet (fun p:ℝ×ℝ=>cutoffErrorTerminal p.1 p.2) w (m,V)‖≤
        C*V^D*Real.exp (-(ε^2)*V/2) := by
  let e:=logarithmicWordDerivative w errorMassBaseExpr
  have he:e.Small:=small_logarithmicWordDerivative w _ (Or.inr trivial)
  let E (i:Fin 4):=LogDeficitExpr.massDx^[(i:ℕ)] e
  have hE(i:Fin 4):(E i).Small:=e.small_massDx_iterate he i
  obtain ⟨C,hC,D,hb⟩:=four_logarithmic_sections_exponential_bound E hE hε
  refine ⟨C,hC,D,?_⟩
  intro m hm V hV
  have hp:(m,V)∈cutoffErrorDomain:=⟨⟨hε.trans_le hm.1,hm.2.trans_lt (by norm_num)⟩,
    zero_lt_one.trans hV⟩
  let J:=coordinateWordJet (fun p:ℝ×ℝ=>cutoffErrorTerminal p.1 p.2) w (m,V)
  let B:=C*V^D*Real.exp (-(ε^2)*V/2)
  have hB:0≤B:=by dsimp only [B];positivity
  change ‖(J:TerminalJetData)‖≤B
  apply norm_prod_le_iff.mpr
  constructor
  · change ‖J.1.1‖≤B
    rw [←terminalValue_zero J]
    rw [terminalValue_cutoffError_coordinateWordJet w hp]
    exact hb m hm V hV.le 0 0
  · apply (pi_norm_le_iff_of_nonneg hB).mpr
    intro i
    apply (BoundedContinuousFunction.norm_le hB).mpr
    intro x
    change ‖terminalJet J i x‖≤B
    rw [terminalJet_cutoffError_coordinateWordJet w hp i x]
    exact hb m hm V hV.le ⟨i+1,by omega⟩ x

end DepthPaper
