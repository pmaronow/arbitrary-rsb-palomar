module

public import GeneralDepthPaper.TerminalOperators

@[expose] public section


/-! Reconstruction identifies the compatible Banach jets with the actual C³
terminal functions, and the inherited norm is equivalent to the sum norm in
Appendix A. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 32

@[simp] theorem terminalValue_zeroDatum (x : ℝ) : terminalValue (0:TerminalSpace) x=0 := by
  simp [terminalValue]

theorem norm_le_terminalSumNorm (g : TerminalSpace) : ‖g‖≤terminalSumNorm g := by
  change ‖g.1‖≤_
  rw [norm_prod_le_iff]
  have hs : 0≤∑i:Fin 3,‖terminalJet g i‖ := Finset.sum_nonneg fun _ _=>norm_nonneg _
  refine ⟨by unfold terminalSumNorm; linarith,?_⟩
  apply (pi_norm_le_iff_of_nonneg (show 0≤terminalSumNorm g by unfold terminalSumNorm; positivity)).mpr
  intro i
  have hi := Finset.single_le_sum (fun j (_:j∈(Finset.univ:Finset (Fin 3)))=>norm_nonneg (terminalJet g j))
    (Finset.mem_univ i)
  change ‖terminalJet g i‖≤terminalSumNorm g
  unfold terminalSumNorm
  linarith [norm_nonneg g.1.1]

def terminalSpaceOfJets (f : ℝ→ℝ) (J : Fin 3→ℝ →ᵇ ℝ)
    (h01 : ∀x,HasDerivAt (J 0) (J 1 x) x)
    (h12 : ∀x,HasDerivAt (J 1) (J 2 x) x) (hU : UniformContinuous (J 2)) : TerminalSpace :=
  ⟨(f 0,J),h01,h12,hU⟩

theorem terminalValue_terminalSpaceOfJets (f : ℝ→ℝ) (J : Fin 3→ℝ →ᵇ ℝ)
    (h0 : ∀x,HasDerivAt f (J 0 x) x)
    (h01 : ∀x,HasDerivAt (J 0) (J 1 x) x)
    (h12 : ∀x,HasDerivAt (J 1) (J 2 x) x) (hU : UniformContinuous (J 2)) (x : ℝ) :
    terminalValue (terminalSpaceOfJets f J h01 h12 hU) x=f x := by
  change f 0+(∫y in (0:ℝ)..x,J 0 y)=_
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _=>h0 y)
    ((J 0).continuous.intervalIntegrable _ _)]
  ring

theorem terminalValue_injective : Function.Injective terminalValue := by
  intro g h he
  have h0 : g.1.1=h.1.1 := by simpa using congrFun he 0
  have hJ0 : terminalJet g 0=terminalJet h 0 := by
    ext x
    exact (hasDerivAt_terminalValue g x).unique (he.symm ▸ hasDerivAt_terminalValue h x)
  have hJ1 : terminalJet g 1=terminalJet h 1 := by
    ext x
    exact (hasDerivAt_terminalJet_zero g x).unique (hJ0.symm ▸ hasDerivAt_terminalJet_zero h x)
  have hJ2 : terminalJet g 2=terminalJet h 2 := by
    ext x
    exact (hasDerivAt_terminalJet_one g x).unique (hJ1.symm ▸ hasDerivAt_terminalJet_one h x)
  apply Subtype.ext
  apply Prod.ext h0
  funext i
  fin_cases i
  · exact hJ0
  · exact hJ1
  · exact hJ2

end GeneralDepthPaper
