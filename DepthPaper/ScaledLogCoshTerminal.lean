module

public import DepthPaper.LogCoshTerminal

@[expose] public section


/-! The literal lower terminal datum ψ_m(x)=m⁻¹ log cosh(mx), as an
actual compatible-jet Banach datum. Field dilation also applies to every
terminal datum, and its reconstruction commutes with the dilation. -/
noncomputable section
open Set Filter
open scoped Topology NNReal BoundedContinuousFunction
namespace DepthPaper
set_option maxSynthPendingDepth 64

def fieldScaledJet (m : ℝ) (g : TerminalSpace) (i : Fin 3) : ℝ →ᵇ ℝ :=
  m^(i:ℕ) • (terminalJet g i).compContinuous ⟨fun x=>m*x,by fun_prop⟩

@[simp] theorem fieldScaledJet_apply (m : ℝ) (g : TerminalSpace) (i : Fin 3) (x : ℝ) :
    fieldScaledJet m g i x=m^(i:ℕ)*terminalJet g i (m*x) := rfl

theorem fieldScaledJet_compatible (m : ℝ) (g : TerminalSpace) :
    (∀x,HasDerivAt (fieldScaledJet m g 0) (fieldScaledJet m g 1 x) x) ∧
    (∀x,HasDerivAt (fieldScaledJet m g 1) (fieldScaledJet m g 2 x) x) ∧
    UniformContinuous (fieldScaledJet m g 2) := by
  refine ⟨fun x=>?_,fun x=>?_,?_⟩
  · change HasDerivAt (fun y=>m^0*terminalJet g 0 (m*y))
      (m^1*terminalJet g 1 (m*x)) x
    have hd:=(hasDerivAt_terminalJet_zero g (m*x)).comp x ((hasDerivAt_id x).const_mul m)
    simpa only [pow_zero,pow_one,one_mul,Function.comp_def,mul_one,mul_comm] using hd
  · have hd:=((hasDerivAt_terminalJet_one g (m*x)).comp x
      ((hasDerivAt_id x).const_mul m)).const_mul m
    change HasDerivAt (fun y=>m^1*terminalJet g 1 (m*y))
      (m^2*terminalJet g 2 (m*x)) x
    convert! hd using 1
    · funext y
      simp only [pow_one,Function.comp_def]
    · ring
  · change UniformContinuous (fun x=>m^2*terminalJet g 2 (m*x))
    exact ((uniformContinuous_terminalJet g 2).comp
      (uniformContinuous_id.const_smul m)).const_smul (m^2)

def fieldScaledTerminal (m : ℝ) (g : TerminalSpace) : TerminalSpace :=
  terminalSpaceOfJets (fun x=>m⁻¹*terminalValue g (m*x)) (fieldScaledJet m g)
    (fieldScaledJet_compatible m g).1 (fieldScaledJet_compatible m g).2.1
    (fieldScaledJet_compatible m g).2.2

@[simp] theorem terminalJet_fieldScaledTerminal (m : ℝ) (g : TerminalSpace) (i : Fin 3) :
    terminalJet (fieldScaledTerminal m g) i=fieldScaledJet m g i := rfl

theorem terminalValue_fieldScaledTerminal (m : ℝ) (hm : m≠0) (g : TerminalSpace) (x : ℝ) :
    terminalValue (fieldScaledTerminal m g) x=m⁻¹*terminalValue g (m*x) := by
  apply terminalValue_terminalSpaceOfJets
  intro y
  have hd:=((hasDerivAt_terminalValue g (m*y)).comp y
    ((hasDerivAt_id y).const_mul m)).const_mul m⁻¹
  convert! hd using 1
  simp only [fieldScaledJet_apply,Fin.val_zero,pow_zero,one_mul]
  field_simp

def scaledLogCoshTerminal (m : ℝ) : TerminalSpace := fieldScaledTerminal m logCoshTerminal

theorem terminalValue_scaledLogCoshTerminal (m : ℝ) (hm : m≠0) (x : ℝ) :
    terminalValue (scaledLogCoshTerminal m) x=m⁻¹*Real.log (Real.cosh (m*x)) := by
  rw [scaledLogCoshTerminal,terminalValue_fieldScaledTerminal m hm,terminalValue_logCoshTerminal]

@[simp] theorem terminalValue_scaledLogCoshTerminal_zero (m : ℝ) :
    terminalValue (scaledLogCoshTerminal m) 0=0 := by
  rw [terminalValue_zero]
  change m⁻¹*terminalValue logCoshTerminal (m*0)=0
  simp only [mul_zero,terminalValue_logCoshTerminal,Real.cosh_zero,Real.log_one]

theorem terminalJet_scaledLogCoshTerminal_zero (m x : ℝ) :
    terminalJet (scaledLogCoshTerminal m) 0 x=Real.tanh (m*x) := by
  simp [scaledLogCoshTerminal,terminalJet_fieldScaledTerminal,fieldScaledJet_apply,
    terminalJet_logCoshTerminal_zero]

theorem norm_terminalJet_scaledLogCoshTerminal_le_one (m : ℝ) :
    ‖terminalJet (scaledLogCoshTerminal m) 0‖≤1 := by
  apply (BoundedContinuousFunction.norm_le (by norm_num : (0:ℝ)≤1)).mpr
  intro x
  rw [terminalJet_scaledLogCoshTerminal_zero,Real.norm_eq_abs]
  exact (Real.abs_tanh_lt_one _).le

theorem lipschitzWith_scaledLogCoshTerminal (m : ℝ) :
    LipschitzWith 1 (terminalValue (scaledLogCoshTerminal m)) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun x=>(hasDerivAt_terminalValue (scaledLogCoshTerminal m) x).differentiableAt)
  intro x
  rw [(hasDerivAt_terminalValue (scaledLogCoshTerminal m) x).deriv]
  exact_mod_cast (BoundedContinuousFunction.norm_coe_le_norm
    (terminalJet (scaledLogCoshTerminal m) 0) x).trans (norm_terminalJet_scaledLogCoshTerminal_le_one m)

end DepthPaper
