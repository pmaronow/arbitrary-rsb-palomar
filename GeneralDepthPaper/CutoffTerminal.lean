module

public import GeneralDepthPaper.CutoffData
public import GeneralDepthPaper.TerminalConstantShift
public import GeneralDepthPaper.LargeVarianceLemma

@[expose] public section


/-! The actual terminal datum χ in the cutoff splitting lemma. It is an
element of the complete compatible terminal space, with its true value and
jets, rather than a scalar function declared to have the desired norm. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal BoundedContinuousFunction
namespace GeneralDepthPaper
open ColeHopfFoundation.ProbabilityTheory
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

def cutoffLeadingConstant (m V : ℝ) : ℝ :=
  m*V/2+(1/m-1)*Real.log 2

def cutoffTerminal (m V : ℝ) : TerminalSpace :=
  coleHopfTerminal ((m,V),logCoshTerminal)+terminalConstant (-cutoffLeadingConstant m V)

theorem terminalValue_cutoffTerminal (m V : ℝ) (hV : 0≤V) (x : ℝ) :
    terminalValue (cutoffTerminal m V) x=
      coleHopf m V.toNNReal (fun y => Real.log (Real.cosh y)) x-
        cutoffLeadingConstant m V := by
  rw [cutoffTerminal,terminalValue_add,terminalValue_constant,
    terminalValue_coleHopfTerminal_nonneg _ hV]
  rw [show terminalValue logCoshTerminal=(fun y => Real.log (Real.cosh y)) from
    funext terminalValue_logCoshTerminal]
  ring

theorem norm_terminalJet_cutoffTerminal_le_one (m V : ℝ) (hV : 0≤V) :
    ‖terminalJet (cutoffTerminal m V) 0‖≤1 := by
  rw [cutoffTerminal,terminalJet_add_constant]
  exact (norm_terminalJet_coleHopfTerminal_nonneg ((m,V),logCoshTerminal) hV).trans
    norm_terminalJet_logCoshTerminal_le_one

def terminalConstantCLM : ℝ→L[ℝ] TerminalSpace :=
  LinearMap.mkContinuous
    { toFun := terminalConstant
      map_add' := by
        intro a b
        apply Subtype.ext
        apply Prod.ext <;> simp [terminalConstant,terminalSpaceOfJets]
      map_smul' := by
        intro a b
        apply Subtype.ext
        apply Prod.ext <;> simp [terminalConstant,terminalSpaceOfJets] }
    1 (by
      intro c
      change ‖(c,(0:Fin 3→ℝ→ᵇℝ))‖≤1*‖c‖
      simp)

theorem contDiffAt_cutoffTerminal {m V : ℝ} (hm : m≠0) (hV : 0<V) :
    ContDiffAt ℝ ∞ (fun p : ℝ×ℝ => cutoffTerminal p.1 p.2) (m,V) := by
  have harg : ContDiffAt ℝ ∞
      (fun p : ℝ×ℝ => ((p.1,p.2),logCoshTerminal)) (m,V) := by fun_prop
  have hch := (contDiffAt_coleHopfTerminal ((m,V),logCoshTerminal) hV).comp (m,V) harg
  have hlead : ContDiffAt ℝ ∞
      (fun p : ℝ×ℝ => -cutoffLeadingConstant p.1 p.2) (m,V) := by
    unfold cutoffLeadingConstant
    fun_prop
  exact hch.add (terminalConstantCLM.contDiff.contDiffAt.comp (m,V) hlead)

def cutoffCandidateConstant (Ξ : AdmissibleCovariance) (m : ℝ) (Q : Overlap) (qc : ℝ) : ℝ :=
  (Ξ.first 1-Ξ.first Q)/2+cutoffLeadingConstant m (Ξ.first Q-Ξ.first qc)

theorem potential_twoLevelMeasure_at_cutoff (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (Q : Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc)
    (hcQ : qc≤(Q:ℝ)) (x : ℝ) :
    potential Ξ (twoLevelMeasure z hz m Q) qc x=
      cutoffCandidateConstant Ξ m Q qc+
        terminalValue (cutoffTerminal m (Ξ.first Q-Ξ.first qc)) x := by
  have hc0 := cutoff_pos z hz qc hc
  have hV : 0≤Ξ.first Q-Ξ.first qc := sub_nonneg.mpr
    (Ξ.first_strictMonoOn.monotoneOn hc0.le Q.property.1 hcQ)
  rw [potential_twoLevelMeasure_top_solution Ξ z hz m hm Q (hc.le.trans hcQ)
    qc ⟨hc.le,hcQ⟩ x,terminalValue_cutoffTerminal m _ hV x,cutoffCandidateConstant]
  ring

theorem terminalValue_cutoffTerminal_error (m : ℝ) (hm : m∈Ioc (0:ℝ) 1)
    (V : ℝ≥0) (x : ℝ) :
    terminalValue (cutoffTerminal m V) x=
      Real.log (Real.cosh (m*x))/m+largeVarianceError m V x := by
  rw [terminalValue_cutoffTerminal m V V.coe_nonneg x,Real.toNNReal_coe,
    coleHopf_largeVariance_expansion m V x]
  unfold cutoffLeadingConstant
  ring

end GeneralDepthPaper
