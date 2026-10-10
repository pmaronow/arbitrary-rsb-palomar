module

public import DepthPaper.RevisedEntropyRecursion

@[expose] public section

/-! The actual derivative cancellation in the entropy proof: varying the
recursion levels in both terms cancels, leaving exactly the derivative in
the scaled log-cosh terminal datum. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace DepthPaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

def revisedMassRecursionData {L : ℕ} (d : Fin L → ℝ × ℝ) (m : ℝ) : Fin L → ℝ × ℝ :=
  fun i => (m * (d i).1, (d i).2)

theorem revisedMassRecursionData_one {L : ℕ} (d : Fin L → ℝ × ℝ) :
    revisedMassRecursionData d 1 = d := by
  funext i
  simp only [revisedMassRecursionData, one_mul, Prod.mk.eta]

def revisedMassTerminalRecursion (L : ℕ) (d : Fin L → ℝ × ℝ)
    (p : ℝ × TerminalSpace) : TerminalSpace :=
  coleHopfRecursion L (revisedMassRecursionData d p.1, p.2)

theorem contDiffAt_revisedMassTerminalRecursion
    (L : ℕ) (d : Fin L → ℝ × ℝ) (hv : ∀ i, 0 < (d i).2)
    (m : ℝ) (g : TerminalSpace) :
    ContDiffAt ℝ ∞ (revisedMassTerminalRecursion L d) (m, g) := by
  change ContDiffAt ℝ ∞ (fun p : ℝ × TerminalSpace =>
    coleHopfRecursion L (revisedMassRecursionData d p.1, p.2)) (m, g)
  apply (contDiffAt_coleHopfRecursion L (revisedMassRecursionData d m, g) hv).comp (m, g)
  rw [contDiffAt_prod_iff]
  constructor
  · rw [contDiffAt_pi]
    intro i
    unfold revisedMassRecursionData
    fun_prop
  · exact contDiffAt_snd

theorem hasDerivAt_revisedMass_terminal_difference
    (L : ℕ) (d : Fin L → ℝ × ℝ) (hv : ∀ i, 0 < (d i).2) :
    HasDerivAt (fun m : ℝ =>
      terminalValue (coleHopfRecursion L (revisedMassRecursionData d m, scaledLogCoshTerminal m)) 0 -
      terminalValue (coleHopfRecursion L (revisedMassRecursionData d m, logCoshTerminal)) 0)
      (terminalValue (revisedColeHopfRecursionDerivative L d logCoshTerminal
        revisedEntropyTerminalDirection) 0) 1 := by
  let p : ℝ × TerminalSpace := (1, logCoshTerminal)
  let R := revisedMassTerminalRecursion L d
  let D := fderiv ℝ R p
  have hR : HasFDerivAt R D p :=
    (contDiffAt_revisedMassTerminalRecursion L d hv 1 logCoshTerminal).differentiableAt
      (by simp) |>.hasFDerivAt
  have hfirst : HasDerivAt (fun m : ℝ => (m, scaledLogCoshTerminal m))
      (1, revisedEntropyTerminalDirection) 1 :=
    (hasDerivAt_id (1 : ℝ)).prodMk hasDerivAt_scaledLogCoshTerminal_one
  have hsecond : HasDerivAt (fun m : ℝ => (m, logCoshTerminal)) (1, 0) 1 :=
    (hasDerivAt_id (1 : ℝ)).prodMk (hasDerivAt_const (1 : ℝ) logCoshTerminal)
  have hRfirst : HasFDerivAt R D (1, scaledLogCoshTerminal 1) := by
    simpa only [scaledLogCoshTerminal_one] using hR
  have hd1 := (terminalEvalCLM 0).hasFDerivAt.comp_hasDerivAt 1
    (hRfirst.comp_hasDerivAt 1 hfirst)
  have hd2 := (terminalEvalCLM 0).hasFDerivAt.comp_hasDerivAt 1
    (hR.comp_hasDerivAt 1 hsecond)
  have hfixed : HasFDerivAt (fun g : TerminalSpace => coleHopfRecursion L (d, g))
      (D.comp ((0 : TerminalSpace →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ TerminalSpace)))
      logCoshTerminal := by
    have harg := (hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) logCoshTerminal).prodMk
      (hasFDerivAt_id (𝕜 := ℝ) logCoshTerminal)
    have h := hR.comp logCoshTerminal harg
    apply h.congr_of_eventuallyEq
    exact Eventually.of_forall fun g => by
      dsimp only [Function.comp_def, R, revisedMassTerminalRecursion]
      rw [revisedMassRecursionData_one]
  have hD : D (0, revisedEntropyTerminalDirection) =
      revisedColeHopfRecursionDerivative L d logCoshTerminal revisedEntropyTerminalDirection := by
    rw [revisedColeHopfRecursionDerivative, hfixed.fderiv]
    simp
  have hd := hd1.sub hd2
  apply hd.congr_deriv
  change terminalValue (D (1, revisedEntropyTerminalDirection)) 0 -
    terminalValue (D (1, 0)) 0 = _
  rw [← terminalValue_sub, ← map_sub]
  simp only [Prod.mk_sub_mk, sub_self, sub_zero, hD]

end DepthPaper
