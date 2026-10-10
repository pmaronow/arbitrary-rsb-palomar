module

public import GeneralDepthPaper.ColeHopfRecursionBounds

@[expose] public section


/-! Appendix A.1, including its quantitative clauses and every finite-depth
recursion. The terminal-space max norm is equivalent to the manuscript's
sum norm; all bounds are actual multilinear operator bounds. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction ContDiff
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64

local instance (L : ℕ) : Bornology (ColeHopfRecursionParameter L) :=
  PseudoMetricSpace.toBornology

theorem terminalSumNorm_equivalent (g : TerminalSpace) :
    ‖g‖≤terminalSumNorm g ∧ terminalSumNorm g≤4*‖g‖ :=
  ⟨norm_le_terminalSumNorm g,terminalSumNorm_le_four_norm g⟩

def coleHopfDomain (Vlo Vhi : ℝ) : Set ColeHopfParameter :=
  {p|‖p.1.1‖<2 ∧ Vlo<p.1.2 ∧ p.1.2<Vhi ∧ ‖terminalJet p.2 0‖<2}

def coleHopfRecursionDomain (L : ℕ) (Vlo Vhi : ℝ) : Set (ColeHopfRecursionParameter L) :=
  {p|(∀i,‖(p.1 i).1‖<2 ∧ Vlo<(p.1 i).2 ∧ (p.1 i).2<Vhi) ∧ ‖terminalJet p.2 0‖<2}

theorem cole_hopf_smooth (Vlo Vhi : ℝ) (hVlo : 0<Vlo) (hV : Vlo<Vhi) :
    ContDiffOn ℝ ∞ centeredColeHopfTerminal (coleHopfDomain Vlo Vhi) ∧
    (∀B:ℝ,∀n:ℕ,∃C:ℝ,0≤C ∧ ∀p : ColeHopfParameter, p∈coleHopfDomain Vlo Vhi→‖p.2‖≤B→
      ‖iteratedFDeriv ℝ n centeredColeHopfTerminal p‖≤C) ∧
    (∀p∈coleHopfDomain Vlo Vhi,
      ‖terminalJet (coleHopfTerminal p) 0‖≤‖terminalJet p.2 0‖) ∧
    (∀L:ℕ,ContDiffOn ℝ ∞ (coleHopfRecursion L) (coleHopfRecursionDomain L Vlo Vhi) ∧
      ∀s:Set (ColeHopfRecursionParameter L),Bornology.IsBounded s→
        s⊆coleHopfRecursionDomain L Vlo Vhi→BoundedSmoothOn (coleHopfRecursion L) s) := by
  refine ⟨fun p hp=>(contDiffAt_centeredColeHopfTerminal p (hVlo.trans hp.2.1)).contDiffWithinAt,
    ?_,fun p hp=>norm_terminalJet_coleHopfTerminal_le p (hVlo.trans hp.2.1),?_⟩
  · intro B n
    obtain ⟨C,hC,hb⟩:=
      (boundedSmoothOn_centeredColeHopfTerminal 2 Vlo Vhi (max B 0) (by norm_num)
        hVlo hV.le (le_max_right _ _)).bound n
    exact ⟨C,hC,fun p hp hg=>hb p
      ⟨hp.1.le,hp.2.1.le,hp.2.2.1.le,hg.trans (le_max_left _ _)⟩⟩
  · intro L
    refine ⟨fun p hp=>(contDiffAt_coleHopfRecursion L p
      (fun i=>hVlo.trans (hp.1 i).2.1)).contDiffWithinAt,?_⟩
    intro s hs hsub
    obtain ⟨B,hB,hb⟩:=hs.exists_pos_norm_le
    apply (boundedSmoothOn_coleHopfRecursion L 2 Vlo Vhi B (by norm_num) hVlo hV.le hB.le).mono
    intro p hp
    exact ⟨fun i=>⟨((hsub hp).1 i).1.le,((hsub hp).1 i).2.1.le,((hsub hp).1 i).2.2.le⟩,
      (norm_snd_le p).trans (hb p hp)⟩

end GeneralDepthPaper
