module

public import GeneralDepthPaper.ScaledLogCoshTerminal

@[expose] public section


/-! Fixed field dilation is an actual continuous linear map of compatible
terminal data. It is used to extend mass regularity across mass one. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal BoundedContinuousFunction
namespace GeneralDepthPaper
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 64

def terminalDoubleFieldCLM : TerminalSpace→L[ℝ]TerminalSpace :=
  LinearMap.mkContinuous
    {toFun:=fieldScaledTerminal 2
     map_add':=by
       intro g h
       apply Subtype.ext
       apply Prod.ext
       · change (2:ℝ)⁻¹*terminalValue (g+h) (2*0)=
           (2:ℝ)⁻¹*terminalValue g (2*0)+(2:ℝ)⁻¹*terminalValue h (2*0)
         rw [terminalValue_add]
         ring
       · funext i
         ext x
         change (2:ℝ)^(i:ℕ)*terminalJet (g+h) i (2*x)=
           (2:ℝ)^(i:ℕ)*terminalJet g i (2*x)+(2:ℝ)^(i:ℕ)*terminalJet h i (2*x)
         change (2:ℝ)^(i:ℕ)*(terminalJet g i (2*x)+terminalJet h i (2*x))=_
         ring
     map_smul':=by
       intro c g
       apply Subtype.ext
       apply Prod.ext
       · change (2:ℝ)⁻¹*terminalValue (c•g) (2*0)=c*((2:ℝ)⁻¹*terminalValue g (2*0))
         rw [terminalValue_smul]
         ring
       · funext i
         ext x
         change (2:ℝ)^(i:ℕ)*terminalJet (c•g) i (2*x)=
           c*((2:ℝ)^(i:ℕ)*terminalJet g i (2*x))
         change (2:ℝ)^(i:ℕ)*(c*terminalJet g i (2*x))=_
         ring}
    4 (by
      intro g
      change ‖(fieldScaledTerminal 2 g:TerminalJetData)‖≤4*‖g‖
      apply norm_prod_le_iff.mpr
      constructor
      · change ‖(2:ℝ)⁻¹*terminalValue g (2*0)‖≤4*‖g‖
        rw [mul_zero,terminalValue_zero,norm_mul]
        norm_num
        have hh:=norm_fst_le (g:TerminalJetData)
        rw [Real.norm_eq_abs] at hh
        exact (mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤1/2)).trans
          (mul_le_mul_of_nonneg_right (by norm_num : (1/2:ℝ)≤4)
            (norm_nonneg (g:TerminalJetData)))
      · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
        intro i
        change ‖fieldScaledJet 2 g i‖≤4*‖g‖
        rw [fieldScaledJet,norm_smul]
        have hb:=BoundedContinuousFunction.norm_compContinuous_le (terminalJet g i)
          (⟨fun x=>(2:ℝ)*x,by fun_prop⟩:C(ℝ,ℝ))
        have hi : ‖(2:ℝ)^(i:ℕ)‖≤4 := by fin_cases i <;> norm_num
        exact (mul_le_mul hi hb (norm_nonneg _) (by norm_num)).trans
          (mul_le_mul_of_nonneg_left (norm_terminalJet_le g i) (by norm_num)))

theorem terminalDoubleFieldCLM_scaledLogCosh (m : ℝ) (hm : m≠0) :
    terminalDoubleFieldCLM (scaledLogCoshTerminal (m/2))=scaledLogCoshTerminal m := by
  apply terminalValue_injective
  funext x
  change terminalValue (fieldScaledTerminal 2 (scaledLogCoshTerminal (m/2))) x=_
  rw [terminalValue_fieldScaledTerminal 2 (by norm_num),
    terminalValue_scaledLogCoshTerminal (m/2) (by exact div_ne_zero hm (by norm_num)),
    terminalValue_scaledLogCoshTerminal m hm]
  rw [show (m/2)*(2*x)=m*x by ring]
  field_simp

end GeneralDepthPaper
