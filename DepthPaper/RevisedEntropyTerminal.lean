module

public import DepthPaper.CutoffTerminalSmooth
public import DepthPaper.ScaledLogCoshJetBounds

@[expose] public section

/-! The terminal derivative in Revision (16)'s entropy identity is an actual
derivative in the complete compatible-jet Banach space. Evaluating that
derivative gives the literal function `x * tanh x - log (cosh x)`.
-/

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace DepthPaper

def revisedSpinEntropy (x : ℝ) : ℝ :=
  Real.log 2 + Real.log (Real.cosh x) - x * Real.tanh x

def revisedEntropyTerminalDirection : TerminalSpace :=
  deriv scaledLogCoshTerminal 1

theorem scaledLogCoshTerminal_one : scaledLogCoshTerminal 1 = logCoshTerminal := by
  apply terminalValue_injective
  funext x
  rw [terminalValue_scaledLogCoshTerminal 1 one_ne_zero x, terminalValue_logCoshTerminal]
  simp

theorem hasDerivAt_scaledLogCoshTerminal_one :
    HasDerivAt scaledLogCoshTerminal revisedEntropyTerminalDirection 1 := by
  exact (contDiffAt_scaledLogCoshTerminal (by norm_num)).differentiableAt
    (by simp) |>.hasDerivAt

theorem hasDerivAt_scaledLogCoshTerminal_value {m : ℝ}
    (hm : m ∈ Ioo (0 : ℝ) 2) (x : ℝ) :
    HasDerivAt (fun b => terminalValue (scaledLogCoshTerminal b) x)
      (-(m ^ 2)⁻¹ * Real.log (Real.cosh (m * x)) +
        m⁻¹ * (Real.tanh (m * x) * x)) m := by
  have hlog := (Paper.hasDerivAt_log_cosh (m * x)).comp m
    ((hasDerivAt_id m).mul_const x)
  have hd := ((hasDerivAt_inv hm.1.ne').mul hlog)
  simp only [Function.comp_apply, id_eq, one_mul] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hm] with b hb
  exact terminalValue_scaledLogCoshTerminal b hb.1.ne' x

theorem terminalValue_scaledLogCoshTerminal_deriv {m : ℝ}
    (hm : m ∈ Ioo (0 : ℝ) 2) (x : ℝ) :
    terminalValue (deriv scaledLogCoshTerminal m) x =
      -(m ^ 2)⁻¹ * Real.log (Real.cosh (m * x)) +
        m⁻¹ * (Real.tanh (m * x) * x) := by
  have hd := (contDiffAt_scaledLogCoshTerminal hm).differentiableAt
    (by simp) |>.hasDerivAt
  have he := (terminalEvalCLM x).hasFDerivAt.comp_hasDerivAt m hd
  exact he.unique (hasDerivAt_scaledLogCoshTerminal_value hm x)

theorem terminalValue_revisedEntropyTerminalDirection (x : ℝ) :
    terminalValue revisedEntropyTerminalDirection x =
      x * Real.tanh x - Real.log (Real.cosh x) := by
  rw [revisedEntropyTerminalDirection,
    terminalValue_scaledLogCoshTerminal_deriv (by norm_num : (1 : ℝ) ∈ Ioo 0 2)]
  norm_num
  ring

theorem revisedSpinEntropy_eq_terminalDirection (x : ℝ) :
    revisedSpinEntropy x =
      Real.log 2 - terminalValue revisedEntropyTerminalDirection x := by
  rw [terminalValue_revisedEntropyTerminalDirection]
  unfold revisedSpinEntropy
  ring

end DepthPaper
