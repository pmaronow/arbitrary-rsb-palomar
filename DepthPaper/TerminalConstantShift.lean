module

public import DepthPaper.TruncatedSpatialFields

@[expose] public section


/-! Spatial jets of the actual recursion are invariant under terminal
constant shifts. This is essential when Appendix A.2 assumes only derivative
convergence, rather than convergence of the terminal value at zero. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace DepthPaper
open ColeHopfFoundation.ProbabilityTheory
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000

def terminalConstant (c : ℝ) : TerminalSpace :=
  terminalSpaceOfJets (fun _ => c) 0 (fun x => hasDerivAt_const x 0)
    (fun x => hasDerivAt_const x 0) uniformContinuous_const

@[simp] theorem terminalValue_constant (c x : ℝ) : terminalValue (terminalConstant c) x = c := by
  simp [terminalConstant,terminalValue,terminalSpaceOfJets]

@[simp] theorem terminalJet_constant (c : ℝ) (j : Fin 3) : terminalJet (terminalConstant c) j = 0 := rfl

@[simp] theorem terminalJet_add_constant (g : TerminalSpace) (c : ℝ) (j : Fin 3) :
    terminalJet (g+terminalConstant c) j = terminalJet g j := by
  ext x
  change terminalJet g j x+terminalJet (terminalConstant c) j x = terminalJet g j x
  simp only [terminalJet_constant,BoundedContinuousFunction.coe_zero,Pi.zero_apply,add_zero]

theorem terminal_decompose (g : TerminalSpace) : g = terminalNormalize g+terminalConstant g.1.1 := by
  apply Subtype.ext
  apply Prod.ext
  · simp [terminalNormalize,terminalConstant,terminalSpaceOfJets]
  · simp [terminalNormalize,terminalConstant,terminalSpaceOfJets]

theorem coleHopfTerminal_add_constant (a V : ℝ) (hV : 0 ≤ V) (g : TerminalSpace) (c : ℝ) :
    coleHopfTerminal ((a,V),g+terminalConstant c) = coleHopfTerminal ((a,V),g)+terminalConstant c := by
  apply terminalValue_injective
  funext x
  rw [terminalValue_coleHopfTerminal_nonneg _ hV,terminalValue_add,terminalValue_constant]
  have he : terminalValue (g+terminalConstant c) = fun y => terminalValue g y+c := by
    funext y
    rw [terminalValue_add,terminalValue_constant]
  rw [he,coleHopf_add_const (hasLinearGrowth_terminalValue g)
    (contDiff_terminalValue g).continuous.measurable,terminalValue_coleHopfTerminal_nonneg _ hV]

theorem coleHopfRecursion_add_constant (L : ℕ) (step : Fin L → ℝ×ℝ)
    (hV : ∀i,0 ≤ (step i).2) (g : TerminalSpace) (c : ℝ) :
    coleHopfRecursion L (step,g+terminalConstant c) = coleHopfRecursion L (step,g)+terminalConstant c := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change coleHopfTerminal (step 0,coleHopfRecursion L (fun i => step i.succ,g+terminalConstant c)) = _
    rw [ih (fun i => step i.succ) (fun i => hV i.succ)]
    exact coleHopfTerminal_add_constant _ _ (hV 0) _ c

def normalizedTruncatedParameter {L : ℕ} {qc : ℝ} (p : TruncatedRecursionParameter L qc) :
    TruncatedRecursionParameter L qc := (p.1,(p.2.1,(p.2.2.1,terminalNormalize p.2.2.2)))

theorem truncatedSpatialField_normalized {L : ℕ} {qc : ℝ} (hqc : 0 ≤ qc)
    (p : TruncatedRecursionParameter L qc) (hm : Monotone p.1) (j : Fin 3) :
    truncatedSpatialField hqc (normalizedTruncatedParameter p) j = truncatedSpatialField hqc p j := by
  ext qx
  rw [truncatedSpatialField_apply,truncatedSpatialField_apply]
  have hg := terminal_decompose p.2.2.2
  have hv : ∀i,0 ≤ (truncatedStepData p (projIcc 0 qc hqc qx.1) i).2 :=
    truncatedStepData_nonneg p hm _
  change terminalJet (coleHopfRecursion L (truncatedStepData p _,terminalNormalize p.2.2.2)) j qx.2 =
    terminalJet (coleHopfRecursion L (truncatedStepData p _,p.2.2.2)) j qx.2
  conv_rhs => rw [hg]
  rw [coleHopfRecursion_add_constant L _ hv,terminalJet_add_constant]

end DepthPaper
