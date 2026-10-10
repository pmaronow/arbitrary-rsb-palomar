module

public import DepthPaper.ColeHopfRecursion
public import Paper.RSFunctional
public import Paper.TanhPolynomial

@[expose] public section


/-! The manuscript's literal log-cosh terminal condition is an actual member
of the compatible-jet Banach space, with first-derivative norm at most one. -/
noncomputable section
open Set Filter
open scoped Topology NNReal BoundedContinuousFunction Polynomial
namespace DepthPaper
set_option maxSynthPendingDepth 64

def tanhPolynomialBCF (P : ℝ[X]) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x=>P.eval (Real.tanh x))
    (Paper.continuous_tanhPolynomial P) (Classical.choose (Paper.tanhPolynomial_bounded P))
    (Classical.choose_spec (Paper.tanhPolynomial_bounded P)).2

@[simp] theorem tanhPolynomialBCF_apply (P:ℝ[X]) (x:ℝ) :
    tanhPolynomialBCF P x=P.eval (Real.tanh x) := rfl

theorem uniformContinuous_tanhPolynomialBCF (P:ℝ[X]) : UniformContinuous (tanhPolynomialBCF P) := by
  apply LipschitzWith.uniformContinuous
  apply lipschitzWith_of_nnnorm_deriv_le (C:=‖tanhPolynomialBCF (Paper.tanhPolynomialDeriv P)‖₊)
    (fun x=>(Paper.hasDerivAt_tanhPolynomial P x).differentiableAt)
  intro x
  rw [(Paper.hasDerivAt_tanhPolynomial P x).deriv]
  exact BoundedContinuousFunction.nnnorm_coe_le_nnnorm
    (tanhPolynomialBCF (Paper.tanhPolynomialDeriv P)) x

def logCoshJetPolynomial : ℕ→ℝ[X]
  | 0=>Polynomial.X
  | n+1=>Paper.tanhPolynomialDeriv (logCoshJetPolynomial n)

def logCoshTerminal : TerminalSpace :=
  terminalSpaceOfJets (fun x=>Real.log (Real.cosh x))
    (fun i:Fin 3=>tanhPolynomialBCF (logCoshJetPolynomial i))
    (fun x=>Paper.hasDerivAt_tanhPolynomial (logCoshJetPolynomial 0) x)
    (fun x=>Paper.hasDerivAt_tanhPolynomial (logCoshJetPolynomial 1) x)
    (uniformContinuous_tanhPolynomialBCF _)

theorem terminalValue_logCoshTerminal (x:ℝ) :
    terminalValue logCoshTerminal x=Real.log (Real.cosh x) := by
  apply terminalValue_terminalSpaceOfJets
  intro y
  simpa only [tanhPolynomialBCF_apply,logCoshJetPolynomial,Polynomial.eval_X] using
    Paper.hasDerivAt_log_cosh y

theorem terminalJet_logCoshTerminal_zero (x:ℝ) :
    terminalJet logCoshTerminal 0 x=Real.tanh x := by
  simp [terminalJet,logCoshTerminal,terminalSpaceOfJets,tanhPolynomialBCF_apply,logCoshJetPolynomial]

theorem norm_terminalJet_logCoshTerminal_le_one : ‖terminalJet logCoshTerminal 0‖≤1 := by
  apply (BoundedContinuousFunction.norm_le (by norm_num : (0:ℝ)≤1)).mpr
  intro x
  rw [terminalJet_logCoshTerminal_zero,Real.norm_eq_abs]
  exact (Real.abs_tanh_lt_one x).le

end DepthPaper
