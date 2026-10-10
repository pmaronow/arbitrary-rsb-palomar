module

public import DepthPaper.RevisedAppendixAStep
public import DepthPaper.RevisedAppendixAClosedJets

@[expose] public section

/-! All genuine intermediate outputs of a finite backward recursion, with
uniform smooth operator bounds and preservation of one-Lipschitz terminals. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
namespace DepthPaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

def revisedColeHopfOutputs : (L : ℕ) → ColeHopfRecursionParameter L → Fin (L+1) → TerminalSpace
  | 0,p => fun _ => p.2
  | L+1,p => Fin.cases (coleHopfRecursion (L+1) p)
      (revisedColeHopfOutputs L (coleHopfTailCLM L p))

@[simp] theorem revisedColeHopfOutputs_zero (L : ℕ) (p : ColeHopfRecursionParameter L) :
    revisedColeHopfOutputs L p 0 = coleHopfRecursion L p := by
  cases L <;> rfl

theorem revisedColeHopfOutputs_one_lipschitz (L : ℕ) (p : ColeHopfRecursionParameter L)
    (hV : ∀i,0 ≤ (p.1 i).2) (hg : ‖terminalJet p.2 0‖ ≤ 1) :
    ∀i, LipschitzWith 1 (terminalValue (revisedColeHopfOutputs L p i)) := by
  induction L with
  | zero => intro i; exact (lipschitzWith_terminalValue _).weaken (by exact_mod_cast hg)
  | succ L ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (lipschitzWith_terminalValue _).weaken
        (by exact_mod_cast (norm_terminalJet_coleHopfRecursion_nonneg (L+1) p hV).trans hg)
    · exact ih (coleHopfTailCLM L p) (fun j => hV j.succ) hg j

theorem revised_boundedSmoothOn_coleHopfOutputs (L : ℕ) (A Vlo Vhi B : ℝ)
    (hA : 0 ≤ A) (hVlo : 0 < Vlo) (hV : Vlo ≤ Vhi) (hB : 0 ≤ B) :
    BoundedSmoothOn (revisedColeHopfOutputs L) (coleHopfRecursionBall L A Vlo Vhi B) := by
  induction L with
  | zero =>
    apply BoundedSmoothOn.pi
    intro i
    exact BoundedSmoothOn.linear (ContinuousLinearMap.snd ℝ (Fin 0→ℝ×ℝ) TerminalSpace)
      _ _ ((hA.trans (le_max_left _ _)).trans (le_max_left _ _))
      (norm_coleHopfRecursionBall_le 0 A Vlo Vhi B hA hVlo hV)
  | succ L ih =>
    let s := coleHopfRecursionBall (L+1) A Vlo Vhi B
    let C := max (max A Vhi) B
    have hC : 0 ≤ C := (hA.trans (le_max_left _ _)).trans (le_max_left _ _)
    have htail := BoundedSmoothOn.linear (coleHopfTailCLM L) s C hC
      (norm_coleHopfRecursionBall_le (L+1) A Vlo Vhi B hA hVlo hV)
    have hrest := ih.comp htail (fun p hp => ⟨fun i => hp.1 i.succ,hp.2⟩)
    apply BoundedSmoothOn.pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact boundedSmoothOn_coleHopfRecursion (L+1) A Vlo Vhi B hA hVlo hV hB
    · exact hrest.compCLM (ContinuousLinearMap.proj j)

end DepthPaper
