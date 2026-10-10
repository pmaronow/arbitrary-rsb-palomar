module

public import GeneralDepthPaper.CutoffComparisonPotential
public import GeneralDepthPaper.CutoffTerminalSmooth
public import GeneralDepthPaper.HighDegreeRegularity

@[expose] public section


/-! An actual open smooth extension of the lower cutoff recursion. Masses
are unrestricted real parameters in the recursion; the selected physical
candidate is identified on its genuine probability domain, including mass one. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BoundedContinuousFunction
namespace GeneralDepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

 def cutoffRecursionSteps (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (m qc : ℝ) : Fin (r+1) → ℝ × ℝ := fun i =>
  (m*atomicLevel z i, Ξ.first (cutoffAtomicNode z qc i.succ)-
    Ξ.first (cutoffAtomicNode z qc i.castSucc))

 def cutoffRecursionTerminal (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (m qc : ℝ) (g : TerminalSpace) : TerminalSpace :=
  coleHopfRecursion (r+1) (cutoffRecursionSteps Ξ z m qc,g)

 theorem contDiff_cutoffAtomicNode {r : ℕ} (qc : ℝ) (i : Fin (r+2)) :
    ContDiff ℝ ∞ (fun z : AtomicPoint r => cutoffAtomicNode z qc i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [cutoffAtomicNode_last] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : AtomicPoint r => qc))
  · simpa only [cutoffAtomicNode_castSucc] using contDiff_atomicLocation j

 theorem cutoffRecursionSteps_variance_pos (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m qc : ℝ)
    (hc : atomicLocation z (Fin.last r) < qc) (i : Fin (r+1)) :
    0 < (cutoffRecursionSteps Ξ z m qc i).2 := by
  apply sub_pos.mpr
  exact Ξ.first_strictMonoOn
    (cutoffAtomicNode_mem z hz qc hc i.castSucc).1
    (cutoffAtomicNode_mem z hz qc hc i.succ).1
    ((cutoffAtomicNode_strictMono z hz qc hc) i.castSucc_lt_succ)

 theorem cutoffTruncatedData_initial_eq_recursion (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc)
    (g : TerminalSpace) (hg : ‖terminalJet g 0‖ ≤ 1) (x : ℝ) :
    (cutoffTruncatedData Ξ z hz m hm qc hc g hg).potential 0 x =
      terminalValue (cutoffRecursionTerminal Ξ z m qc g) x := by
  let d := cutoffTruncatedData Ξ z hz m hm qc hc g hg
  let q : TruncatedClockDomain qc := ⟨0,⟨le_rfl,(cutoff_pos z hz qc hc).le⟩⟩
  have he : truncatedStepData d.parameter q = cutoffRecursionSteps Ξ z m qc := by
    funext i
    have hq : q ≤ d.node i.castSucc := (cutoffAtomicNode_mem z hz qc hc i.castSucc).1
    dsimp only [truncatedStepData,TruncatedParisiData.parameter]
    rw [truncatedClamp_eq_lower_of_le d.node d.node_strictMono.monotone i q hq]
    change (m*atomicLevel z i, cutoffCovarianceJetMap Ξ qc 1 (d.node i.succ)-
      cutoffCovarianceJetMap Ξ qc 1 (d.node i.castSucc)) = _
    simp only [cutoffCovarianceJetMap_one]
    rfl
  change terminalValue (truncatedPotentialTerminal d.parameter
    (projIcc 0 qc d.qc_pos.le 0)) x = _
  rw [projIcc_of_mem d.qc_pos.le q.property]
  change terminalValue (coleHopfRecursion (r+1) (truncatedStepData d.parameter q,g)) x = _
  rw [he]
  rfl

namespace SmoothCovarianceFamily
variable {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]

 theorem contDiffAt_cutoffRecursionSteps (F : SmoothCovarianceFamily Θ) {θ : Θ}
    (hθ : θ∈F.domain) {r : ℕ} (z : AtomicPoint r) (m qc : ℝ) :
    ContDiffAt ℝ ∞ (fun p : Θ × (AtomicPoint r × ℝ) =>
      cutoffRecursionSteps (F.covariance p.1) p.2.1 p.2.2 qc) (θ,(z,m)) := by
  rw [contDiffAt_pi]
  intro i
  have hn (j : Fin (r+2)) : ContDiffAt ℝ ∞
      (fun p : Θ × (AtomicPoint r × ℝ) => (p.1,cutoffAtomicNode p.2.1 qc j)) (θ,(z,m)) :=
    contDiffAt_fst.prodMk ((contDiff_cutoffAtomicNode qc j).contDiffAt.comp _
      (contDiffAt_fst.comp _ contDiffAt_snd))
  have hu := (F.contDiffAt_first hθ (cutoffAtomicNode z qc i.succ)).comp (θ,(z,m)) (hn i.succ)
  have hl := (F.contDiffAt_first hθ (cutoffAtomicNode z qc i.castSucc)).comp (θ,(z,m)) (hn i.castSucc)
  have hm : ContDiffAt ℝ ∞ (fun p : Θ × (AtomicPoint r × ℝ) => p.2.2) (θ,(z,m)) := by fun_prop
  have ha := (contDiff_atomicLevel i).contDiffAt.comp (θ,(z,m))
    (contDiffAt_fst.comp _ contDiffAt_snd)
  exact (hm.mul ha).prodMk (hu.sub hl)

 theorem contDiffAt_cutoffRecursionTerminal (F : SmoothCovarianceFamily Θ) {θ : Θ}
    (hθ : θ∈F.domain) {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (m qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc) (g : TerminalSpace) :
    ContDiffAt ℝ ∞ (fun p : (Θ × (AtomicPoint r × ℝ)) × TerminalSpace =>
      cutoffRecursionTerminal (F.covariance p.1.1) p.1.2.1 p.1.2.2 qc p.2)
        ((θ,(z,m)),g) := by
  exact (GeneralDepthPaper.contDiffAt_coleHopfRecursion (r+1)
    (cutoffRecursionSteps (F.covariance θ) z m qc,g)
    (cutoffRecursionSteps_variance_pos _ z hz m qc hc)).comp ((θ,(z,m)),g)
      (((F.contDiffAt_cutoffRecursionSteps hθ z m qc).comp ((θ,(z,m)),g) contDiffAt_fst).prodMk contDiffAt_snd)

end SmoothCovarianceFamily
end GeneralDepthPaper
