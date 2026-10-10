module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.MeanValue

set_option backward.privateInPublic true

@[expose] public section


/-! The Banach terminal-data space used by Appendix A. A datum is its value
at zero and its first three bounded continuous jets. Compatibility and uniform
continuity form a closed linear subspace; reconstruction by an actual primitive
recovers the original function. The inherited max norm is equivalent to the
paper's sum norm. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace DepthPaper

abbrev TerminalJetData := ℝ×(Fin 3→ℝ →ᵇ ℝ)

def terminalJetSubmodule : Submodule ℝ TerminalJetData where
  carrier := {z | (∀x,HasDerivAt (z.2 0) (z.2 1 x) x) ∧
    (∀x,HasDerivAt (z.2 1) (z.2 2 x) x) ∧ UniformContinuous (z.2 2)}
  zero_mem' := by
    refine ⟨fun x=>?_,fun x=>?_,?_⟩
    · exact hasDerivAt_const x 0
    · exact hasDerivAt_const x 0
    · exact uniformContinuous_const
  add_mem' := by
    intro z w hz hw
    exact ⟨fun x=>(hz.1 x).add (hw.1 x),fun x=>(hz.2.1 x).add (hw.2.1 x),
      hz.2.2.add hw.2.2⟩
  smul_mem' := by
    intro c z hz
    exact ⟨fun x=>(hz.1 x).const_smul c,fun x=>(hz.2.1 x).const_smul c,
      hz.2.2.const_smul c⟩

private theorem tendsto_terminalJet {z : ℕ→TerminalJetData} {Z : TerminalJetData}
    (h : Tendsto z atTop (𝓝 Z)) (i : Fin 3) :
    Tendsto (fun n=>(z n).2 i) atTop (𝓝 (Z.2 i)) :=
  ((continuous_apply i).comp continuous_snd).continuousAt.tendsto.comp h

theorem isClosed_terminalJetSubmodule : IsClosed (terminalJetSubmodule : Set TerminalJetData) := by
  apply isSeqClosed_iff_isClosed.mp
  intro z Z hz hZ
  have ht (i : Fin 3) := tendsto_terminalJet hZ i
  have hu (i : Fin 3) := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp (ht i)
  refine ⟨?_,?_,?_⟩
  · intro x
    exact hasDerivAt_of_tendstoUniformly (hu 1)
      (.of_forall fun n=> (hz n).1) (fun y=>(hu 0).tendsto_at y) x
  · intro x
    exact hasDerivAt_of_tendstoUniformly (hu 2)
      (.of_forall fun n=> (hz n).2.1) (fun y=>(hu 1).tendsto_at y) x
  · exact (hu 2).uniformContinuous (Filter.Eventually.frequently (.of_forall fun n=>(hz n).2.2))

abbrev TerminalSpace := terminalJetSubmodule

instance : CompleteSpace TerminalSpace := isClosed_terminalJetSubmodule.completeSpace_coe

def terminalValue (g : TerminalSpace) (x : ℝ) : ℝ :=
  g.1.1+∫y in (0:ℝ)..x,g.1.2 0 y

def terminalJet (g : TerminalSpace) (i : Fin 3) : ℝ →ᵇ ℝ := g.1.2 i

@[simp] theorem terminalValue_zero (g : TerminalSpace) : terminalValue g 0=g.1.1 := by
  simp [terminalValue]

theorem hasDerivAt_terminalValue (g : TerminalSpace) (x : ℝ) :
    HasDerivAt (terminalValue g) (terminalJet g 0 x) x := by
  have h := intervalIntegral.integral_hasDerivAt_right
    (f := (terminalJet g 0 : ℝ→ℝ))
    ((terminalJet g 0).continuous.intervalIntegrable (0:ℝ) x)
    ((terminalJet g 0).continuous.stronglyMeasurableAtFilter volume (𝓝 x))
    (terminalJet g 0).continuous.continuousAt
  convert! h.const_add g.1.1 using 1

theorem hasDerivAt_terminalJet_zero (g : TerminalSpace) (x : ℝ) :
    HasDerivAt (terminalJet g 0) (terminalJet g 1 x) x := g.2.1 x

theorem hasDerivAt_terminalJet_one (g : TerminalSpace) (x : ℝ) :
    HasDerivAt (terminalJet g 1) (terminalJet g 2 x) x := g.2.2.1 x

theorem uniformContinuous_terminalJet (g : TerminalSpace) (i : Fin 3) :
    UniformContinuous (terminalJet g i) := by
  fin_cases i
  · apply LipschitzWith.uniformContinuous
    apply lipschitzWith_of_nnnorm_deriv_le (C := ‖terminalJet g 1‖₊)
      (fun x=>(hasDerivAt_terminalJet_zero g x).differentiableAt)
    intro x
    rw [(hasDerivAt_terminalJet_zero g x).deriv]
    exact BoundedContinuousFunction.nnnorm_coe_le_nnnorm _ _
  · apply LipschitzWith.uniformContinuous
    apply lipschitzWith_of_nnnorm_deriv_le (C := ‖terminalJet g 2‖₊)
      (fun x=>(hasDerivAt_terminalJet_one g x).differentiableAt)
    intro x
    rw [(hasDerivAt_terminalJet_one g x).deriv]
    exact BoundedContinuousFunction.nnnorm_coe_le_nnnorm _ _
  · exact g.2.2.2

end DepthPaper
