module

public import GeneralDepthPaper.CutoffEndpointErrorBound

@[expose] public section


/-! Genuine large-remaining-variance approximation of the actual terminal
Cole–Hopf gradient by tanh(mx), uniform in the spatial argument. -/
noncomputable section
open Set
open scoped NNReal BoundedContinuousFunction
namespace GeneralDepthPaper
open ColeHopfFoundation.ProbabilityTheory
set_option maxHeartbeats 900000

theorem terminalJet_cutoffTerminal_zero (m V:ℝ) (hV:0≤V) (x:ℝ):
    terminalJet (cutoffTerminal m V) 0 x=
      deriv (coleHopf m V.toNNReal (fun y=>Real.log (Real.cosh y))) x:=by
  have hd:=(hasDerivAt_terminalValue (cutoffTerminal m V) x).add_const (cutoffLeadingConstant m V)
  have he:(fun y=>terminalValue (cutoffTerminal m V) y+cutoffLeadingConstant m V)=
      coleHopf m V.toNNReal (fun y=>Real.log (Real.cosh y)):=by
    funext y
    rw [terminalValue_cutoffTerminal m V hV y]
    ring
  rw [he] at hd
  exact hd.deriv.symm

theorem coleHopf_gradient_scaled_tanh_error (m V x:ℝ) (hV:0≤V):
    |deriv (coleHopf m V.toNNReal (fun y=>Real.log (Real.cosh y))) x-Real.tanh (m*x)|≤
      ‖cutoffErrorTerminal m V‖:=by
  have hp:terminalJet (cutoffErrorTerminal m V) 0 x=
      deriv (coleHopf m V.toNNReal (fun y=>Real.log (Real.cosh y))) x-Real.tanh (m*x):=by
    change terminalJet (cutoffTerminal m V) 0 x-terminalJet (scaledLogCoshTerminal m) 0 x=_
    rw [terminalJet_cutoffTerminal_zero m V hV,terminalJet_scaledLogCoshTerminal_zero]
  rw [←hp,←Real.norm_eq_abs]
  exact ((terminalJet (cutoffErrorTerminal m V) 0).norm_coe_le_norm x).trans
    (norm_terminalJet_le _ _)

theorem coleHopf_gradient_uniform_exponential_error {ε:ℝ} (hε:0 < ε):
    ∃C:ℝ,0 < C ∧ ∀m∈Icc ε 1,∀V>1,∀x:ℝ,
      |deriv (coleHopf m V.toNNReal (fun y=>Real.log (Real.cosh y))) x-Real.tanh (m*x)|≤
        C*Real.exp (-(ε^2)*V/4):=by
  obtain ⟨C,hC,hb⟩:=cutoffError_low_order_pure_exponential_bound hε 0
  refine ⟨C,hC,?_⟩
  intro m hm V hV x
  have hh:=hb 0 le_rfl m hm V hV
  rw [norm_iteratedFDeriv_zero] at hh
  exact (coleHopf_gradient_scaled_tanh_error m V x (zero_le_one.trans hV.le)).trans hh

end GeneralDepthPaper
