module

public import GeneralDepthPaper.ColeHopfTerminalBounds

@[expose] public section


/-! Uniform actual derivatives for every finite depth of the manuscript's
Cole–Hopf recursion. Intermediate terminal norms are controlled recursively. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction ContDiff
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64

def coleHopfRecursionBall (L : ℕ) (A Vlo Vhi B : ℝ) : Set (ColeHopfRecursionParameter L) :=
  {p|(∀i,‖(p.1 i).1‖≤A ∧ Vlo≤(p.1 i).2 ∧ (p.1 i).2≤Vhi) ∧ ‖p.2‖≤B}

theorem norm_coleHopfRecursionBall_le (L : ℕ) (A Vlo Vhi B : ℝ)
    (hA : 0≤A) (hVlo : 0<Vlo) (hV : Vlo≤Vhi)
    (p : ColeHopfRecursionParameter L) (hp : p∈coleHopfRecursionBall L A Vlo Vhi B) :
    ‖p‖≤max (max A Vhi) B := by
  have hfirst : ‖p.1‖≤max A Vhi := by
    apply (pi_norm_le_iff_of_nonneg (hA.trans (le_max_left _ _))).mpr
    intro i
    rw [Prod.norm_def,Real.norm_of_nonneg (hVlo.trans_le (hp.1 i).2.1).le]
    exact max_le ((hp.1 i).1.trans (le_max_left _ _)) ((hp.1 i).2.2.trans (le_max_right _ _))
  rw [Prod.norm_def]
  exact max_le (hfirst.trans (le_max_left _ _)) (hp.2.trans (le_max_right _ _))

def coleHopfTailCLM (L : ℕ) : ColeHopfRecursionParameter (L+1)→L[ℝ] ColeHopfRecursionParameter L :=
  (ContinuousLinearMap.pi (fun i:Fin L=>(ContinuousLinearMap.proj i.succ).comp
    (ContinuousLinearMap.fst ℝ (Fin (L+1)→ℝ×ℝ) TerminalSpace))).prod
      (ContinuousLinearMap.snd ℝ (Fin (L+1)→ℝ×ℝ) TerminalSpace)

@[simp] theorem coleHopfTailCLM_apply (L : ℕ) (p : ColeHopfRecursionParameter (L+1)) :
    coleHopfTailCLM L p=(fun i:Fin L=>p.1 i.succ,p.2) := rfl

theorem boundedSmoothOn_coleHopfRecursion (L : ℕ) (A Vlo Vhi B : ℝ)
    (hA : 0≤A) (hVlo : 0<Vlo) (hV : Vlo≤Vhi) (hB : 0≤B) :
    BoundedSmoothOn (coleHopfRecursion L) (coleHopfRecursionBall L A Vlo Vhi B) := by
  induction L generalizing B with
  | zero =>
    exact BoundedSmoothOn.linear (ContinuousLinearMap.snd ℝ (Fin 0→ℝ×ℝ) TerminalSpace)
      _ _ ((hA.trans (le_max_left _ _)).trans (le_max_left _ _))
      (norm_coleHopfRecursionBall_le 0 A Vlo Vhi B hA hVlo hV)
  | succ L ih =>
    let s := coleHopfRecursionBall (L+1) A Vlo Vhi B
    let C := max (max A Vhi) B
    have hC : 0≤C := (hA.trans (le_max_left _ _)).trans (le_max_left _ _)
    have hball : ∀p∈s,‖p‖≤C := norm_coleHopfRecursionBall_le (L+1) A Vlo Vhi B hA hVlo hV
    have htail := BoundedSmoothOn.linear (coleHopfTailCLM L) s C hC hball
    have hrec := (ih B hB).comp htail (fun p hp=>⟨fun i=>hp.1 i.succ,hp.2⟩)
    obtain ⟨R,hR,hRb⟩:=hrec.bound 0
    have hRb' : ∀p∈s,‖coleHopfRecursion L (coleHopfTailCLM L p)‖≤R := by
      simpa only [norm_iteratedFDeriv_zero,Function.comp_def] using hRb
    have hfirst := BoundedSmoothOn.linear
      ((ContinuousLinearMap.proj (0:Fin (L+1))).comp
        (ContinuousLinearMap.fst ℝ (Fin (L+1)→ℝ×ℝ) TerminalSpace)) s C hC hball
    have hstep := (boundedSmoothOn_coleHopfTerminal A Vlo Vhi R hA hVlo hV hR).comp
      (hfirst.prodMk hrec) (fun p hp=>⟨(hp.1 0).1,(hp.1 0).2.1,(hp.1 0).2.2,hRb' p hp⟩)
    exact hstep

end GeneralDepthPaper
