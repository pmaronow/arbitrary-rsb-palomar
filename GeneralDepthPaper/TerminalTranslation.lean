module

public import GeneralDepthPaper.UniformBCFTranslation
public import GeneralDepthPaper.TerminalReconstruction

@[expose] public section


/-! Translation of an actual terminal datum is strongly continuous in its
Banach norm. Highest-jet uniform continuity is exactly the necessary input. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64

def terminalTranslate (r : ℝ) (g : TerminalSpace) : TerminalSpace :=
  terminalSpaceOfJets (fun x=>terminalValue g (x+r))
    (fun i=>bcfSpatialTranslate r (terminalJet g i))
    (fun x=>by
      change HasDerivAt (fun y:ℝ=>terminalJet g 0 (y+r)) (terminalJet g 1 (x+r)) x
      simpa only [Function.comp_def,id_eq,mul_one] using
        (hasDerivAt_terminalJet_zero g (x+r)).comp x ((hasDerivAt_id x).add_const r))
    (fun x=>by
      change HasDerivAt (fun y:ℝ=>terminalJet g 1 (y+r)) (terminalJet g 2 (x+r)) x
      simpa only [Function.comp_def,id_eq,mul_one] using
        (hasDerivAt_terminalJet_one g (x+r)).comp x ((hasDerivAt_id x).add_const r))
    ((uniformContinuous_terminalJet g 2).comp
      (uniformContinuous_id.add uniformContinuous_const))

@[simp] theorem terminalJet_translate (r : ℝ) (g : TerminalSpace) (i : Fin 3) :
    terminalJet (terminalTranslate r g) i=bcfSpatialTranslate r (terminalJet g i) := rfl

theorem terminalValue_translate (r : ℝ) (g : TerminalSpace) (x : ℝ) :
    terminalValue (terminalTranslate r g) x=terminalValue g (x+r) := by
  change terminalValue g (0+r)+(∫y in (0:ℝ)..x,terminalJet g 0 (y+r))=_
  have hd (y : ℝ) : HasDerivAt (fun y=>terminalValue g (y+r)) (terminalJet g 0 (y+r)) y := by
    simpa only [Function.comp_def,id_eq,mul_one] using
      (hasDerivAt_terminalValue g (y+r)).comp y ((hasDerivAt_id y).add_const r)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _=>hd y)
    (((terminalJet g 0).continuous.comp (continuous_id.add continuous_const)).intervalIntegrable _ _)]
  simp

@[simp] theorem terminalTranslate_zero (g : TerminalSpace) : terminalTranslate 0 g=g := by
  apply Subtype.ext
  apply Prod.ext
  · simpa only [terminalTranslate,terminalSpaceOfJets,zero_add] using terminalValue_zero g
  · funext i
    exact bcfSpatialTranslate_zero (terminalJet g i)

theorem continuous_terminalTranslate (g : TerminalSpace) : Continuous (fun r:ℝ=>terminalTranslate r g) := by
  have hv := (contDiff_terminalValue g).continuous
  have hj : Continuous (fun r:ℝ=>fun i:Fin 3=>bcfSpatialTranslate r (terminalJet g i)) :=
    continuous_pi fun i=>continuous_bcfSpatialTranslate _ (uniformContinuous_terminalJet g i)
  have hm (r:ℝ) : (terminalValue g r,fun i=>bcfSpatialTranslate r (terminalJet g i))∈terminalJetSubmodule := by
    simpa only [terminalTranslate,terminalSpaceOfJets,zero_add] using (terminalTranslate r g).property
  convert! (hv.prodMk hj).subtype_mk hm using 1
  simp only [terminalTranslate,terminalSpaceOfJets,zero_add]

end GeneralDepthPaper
