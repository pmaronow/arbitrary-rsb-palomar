module

public import GeneralDepthPaper.ColeHopfClosedVariance

@[expose] public section


/-! Removing the terminal value at zero makes the topology depend only on
the three derivative jets, exactly as in the observable-continuity lemma. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64

def terminalNormalize (g : TerminalSpace) : TerminalSpace :=
  ⟨(0,g.1.2),g.2⟩

@[simp] theorem terminalJet_normalize (g : TerminalSpace) (i : Fin 3) :
    terminalJet (terminalNormalize g) i = terminalJet g i := rfl

@[simp] theorem terminalValue_normalize (g : TerminalSpace) (x : ℝ) :
    terminalValue (terminalNormalize g) x = terminalValue g x-terminalValue g 0 := by
  simp only [terminalValue,terminalNormalize,intervalIntegral.integral_same,add_zero,zero_add]
  ring

def terminalNormalizeCLM : TerminalSpace →L[ℝ] TerminalSpace :=
  LinearMap.mkContinuous
    { toFun := terminalNormalize
      map_add' := fun g h => by apply Subtype.ext; simp [terminalNormalize]
      map_smul' := fun c g => by apply Subtype.ext; simp [terminalNormalize] }
    1 (fun g => by
      change ‖((0:ℝ),g.1.2)‖ ≤ 1*‖g.1‖
      rw [one_mul,norm_prod_le_iff]
      exact ⟨by simp,norm_snd_le g.1⟩)

theorem tendsto_terminalNormalize_iff {P : Type*} {L : Filter P}
    (g : P → TerminalSpace) (G : TerminalSpace) :
    Tendsto (fun p => terminalNormalize (g p)) L (𝓝 (terminalNormalize G)) ↔
      ∀i : Fin 3,Tendsto (fun p => terminalJet (g p) i) L (𝓝 (terminalJet G i)) := by
  have he : (fun p => (terminalNormalize (g p) : TerminalJetData)) =
      fun p => ((0:ℝ),fun i : Fin 3 => terminalJet (g p) i) := rfl
  rw [tendsto_subtype_rng,he]
  change Tendsto (fun p => ((0:ℝ),fun i : Fin 3 => terminalJet (g p) i)) L
    (𝓝 ((0:ℝ),fun i : Fin 3 => terminalJet G i)) ↔ _
  rw [nhds_prod_eq,Filter.tendsto_prod_iff']
  change Tendsto (fun _ : P => (0:ℝ)) L (𝓝 0) ∧
    Tendsto (fun p => fun i : Fin 3 => terminalJet (g p) i) L (𝓝 (fun i => terminalJet G i)) ↔ _
  simp only [tendsto_const_nhds,true_and,tendsto_pi_nhds]

end GeneralDepthPaper
