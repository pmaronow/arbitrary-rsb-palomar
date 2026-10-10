module

public import GeneralDepthPaper.TerminalNormalization
public import Mathlib.Topology.ContinuousMap.Compact

@[expose] public section


/-! A clamped Gaussian recursion gives an actual jointly continuous potential
jet at every overlap, including moving grid boundaries and flat covariance
clocks. No strictly positive variance is required. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000

abbrev TruncatedClockDomain (qc : ℝ) := Icc (0:ℝ) qc
abbrev TruncatedRecursionParameter (L : ℕ) (qc : ℝ) :=
  C(TruncatedClockDomain qc,ℝ) ×
    ((Fin (L+1) → TruncatedClockDomain qc) × ((Fin L → ℝ) × TerminalSpace))

def truncatedClamp {L : ℕ} {qc : ℝ} (node : Fin (L+1) → TruncatedClockDomain qc)
    (i : Fin L) (q : TruncatedClockDomain qc) : TruncatedClockDomain qc :=
  ⟨min (max (q:ℝ) (node i.castSucc)) (node i.succ),
    ⟨le_min (le_max_of_le_left q.property.1) (node i.succ).property.1,
      (min_le_right _ _).trans (node i.succ).property.2⟩⟩

@[simp] theorem truncatedClamp_apply {L : ℕ} {qc : ℝ}
    (node : Fin (L+1) → TruncatedClockDomain qc) (i : Fin L) (q : TruncatedClockDomain qc) :
    (truncatedClamp node i q : ℝ) = min (max (q:ℝ) (node i.castSucc)) (node i.succ) := rfl

theorem continuous_truncatedClamp {L : ℕ} {qc : ℝ} (i : Fin L) :
    Continuous (fun p : (Fin (L+1) → TruncatedClockDomain qc) × TruncatedClockDomain qc =>
      truncatedClamp p.1 i p.2) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_snd).max
    (continuous_subtype_val.comp ((continuous_apply i.castSucc).comp continuous_fst)) |>.min
      (continuous_subtype_val.comp ((continuous_apply i.succ).comp continuous_fst))

def truncatedStepData {L : ℕ} {qc : ℝ} (p : TruncatedRecursionParameter L qc)
    (q : TruncatedClockDomain qc) : Fin L → ℝ × ℝ := fun i =>
  (p.2.2.1 i,p.1 (p.2.1 i.succ)-p.1 (truncatedClamp p.2.1 i q))

def truncatedPotentialTerminal {L : ℕ} {qc : ℝ} (p : TruncatedRecursionParameter L qc)
    (q : TruncatedClockDomain qc) : TerminalSpace :=
  coleHopfRecursion L (truncatedStepData p q,p.2.2.2)

theorem continuous_truncatedPotentialTerminal {L : ℕ} {qc : ℝ} :
    Continuous (fun pq : TruncatedRecursionParameter L qc × TruncatedClockDomain qc =>
      truncatedPotentialTerminal pq.1 pq.2) := by
  apply (continuous_coleHopfRecursion L).comp
  refine Continuous.prodMk ?_ (by fun_prop)
  apply continuous_pi
  intro i
  have hnode : Continuous (fun pq : TruncatedRecursionParameter L qc × TruncatedClockDomain qc =>
      pq.1.2.1 i.succ) := by fun_prop
  have hclamp : Continuous (fun pq : TruncatedRecursionParameter L qc × TruncatedClockDomain qc =>
      truncatedClamp pq.1.2.1 i pq.2) := by
    have ht : Continuous (fun pq : TruncatedRecursionParameter L qc × TruncatedClockDomain qc =>
        (pq.1.2.1,pq.2)) := by fun_prop
    exact (continuous_truncatedClamp (qc:=qc) i).comp ht
  have hf : Continuous (fun pq : TruncatedRecursionParameter L qc × TruncatedClockDomain qc => pq.1.1) := by
    fun_prop
  have hupper : Continuous (fun pq : TruncatedRecursionParameter L qc × TruncatedClockDomain qc =>
      pq.1.1 (pq.1.2.1 i.succ)) := continuous_eval.comp (hf.prodMk hnode)
  have hlower : Continuous (fun pq : TruncatedRecursionParameter L qc × TruncatedClockDomain qc =>
      pq.1.1 (truncatedClamp pq.1.2.1 i pq.2)) :=
    continuous_eval.comp (hf.prodMk hclamp)
  exact (show Continuous (fun pq : TruncatedRecursionParameter L qc × TruncatedClockDomain qc =>
    pq.1.2.2.1 i) by fun_prop).prodMk (hupper.sub hlower)

def truncatedPotentialFamily {L : ℕ} {qc : ℝ} (p : TruncatedRecursionParameter L qc) :
    C(TruncatedClockDomain qc,TerminalSpace) :=
  ⟨truncatedPotentialTerminal p,continuous_truncatedPotentialTerminal.comp
    (continuous_const.prodMk continuous_id)⟩

theorem continuous_truncatedPotentialFamily {L : ℕ} {qc : ℝ} :
    Continuous (truncatedPotentialFamily (L:=L) (qc:=qc)) :=
  ContinuousMap.continuous_of_continuous_uncurry _ continuous_truncatedPotentialTerminal

theorem tendsto_truncatedPotentialFamily {L : ℕ} {qc : ℝ} {P : Type*} {F : Filter P}
    (p : P → TruncatedRecursionParameter L qc) (p0 : TruncatedRecursionParameter L qc)
    (hp : Tendsto p F (𝓝 p0)) :
    Tendsto (fun j => truncatedPotentialFamily (p j)) F (𝓝 (truncatedPotentialFamily p0)) :=
  continuous_truncatedPotentialFamily.continuousAt.tendsto.comp hp

end GeneralDepthPaper
