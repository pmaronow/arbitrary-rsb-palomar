module

public import GeneralDepthPaper.TruncatedRecursionContinuity

@[expose] public section


/-! The clamped recursion satisfies the literal one-cell Cole–Hopf equation,
so its global continuity is a statement about the genuine truncated solution
rather than about a merely chosen interpolation of grid values. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000

theorem coleHopfTerminal_of_zero_variance (p : ColeHopfParameter) (hv : p.1.2 = 0) :
    coleHopfTerminal p = p.2 := by
  have he : p = ((p.1.1,0),p.2) := by ext <;> simp_all
  rw [he,coleHopfTerminal_zero_variance]

theorem coleHopfRecursion_succ_of_first_zero {L : ℕ} (d : Fin (L+1) → ℝ×ℝ)
    (g : TerminalSpace) (hv : (d 0).2 = 0) :
    coleHopfRecursion (L+1) (d,g) = coleHopfRecursion L (fun i => d i.succ,g) :=
  coleHopfTerminal_of_zero_variance _ hv

theorem coleHopfRecursion_eq_terminal_of_zero {L : ℕ} (d : Fin L → ℝ×ℝ)
    (g : TerminalSpace) (hv : ∀i,(d i).2 = 0) : coleHopfRecursion L (d,g) = g := by
  induction L with
  | zero => rfl
  | succ L ih =>
    rw [coleHopfRecursion_succ_of_first_zero d g (hv 0)]
    exact ih (fun i => d i.succ) (fun i => hv i.succ)

theorem coleHopfRecursion_eq_step_of_zero_prefix {L : ℕ}
    (d e : Fin L → ℝ×ℝ) (g : TerminalSpace) (i : Fin L)
    (hprefix : ∀j,j < i → (d j).2 = 0 ∧ (e j).2 = 0)
    (hi : (e i).2 = 0) (htail : ∀j,i < j → d j = e j) :
    coleHopfRecursion L (d,g) = coleHopfTerminal (d i,coleHopfRecursion L (e,g)) := by
  induction L with
  | zero => exact Fin.elim0 i
  | succ L ih =>
    cases i using Fin.cases with
    | zero =>
      have he : (fun j : Fin L => d j.succ) = fun j => e j.succ := by
        funext j
        apply htail
        simp
      rw [coleHopfRecursion_succ_of_first_zero e g hi]
      change coleHopfTerminal (d 0,coleHopfRecursion L (fun j => d j.succ,g)) = _
      rw [he]
    | succ i =>
      have hz := hprefix 0 (by simp)
      rw [coleHopfRecursion_succ_of_first_zero d g hz.1,
        coleHopfRecursion_succ_of_first_zero e g hz.2]
      exact ih (fun j => d j.succ) (fun j => e j.succ) i
        (fun j hj => hprefix j.succ (by simpa using hj)) hi
        (fun j hj => htail j.succ (by simpa using hj))

theorem truncatedStepData_nonneg {L : ℕ} {qc : ℝ}
    (p : TruncatedRecursionParameter L qc) (hm : Monotone p.1) (q : TruncatedClockDomain qc)
    (i : Fin L) : 0 ≤ (truncatedStepData p q i).2 :=
  sub_nonneg.mpr (hm (show truncatedClamp p.2.1 i q ≤ p.2.1 i.succ from
    min_le_right (max (q:ℝ) (p.2.1 i.castSucc)) (p.2.1 i.succ)))

theorem norm_terminalJet_truncatedPotentialTerminal_le {L : ℕ} {qc : ℝ}
    (p : TruncatedRecursionParameter L qc) (hm : Monotone p.1) (q : TruncatedClockDomain qc) :
    ‖terminalJet (truncatedPotentialTerminal p q) 0‖ ≤ ‖terminalJet p.2.2.2 0‖ :=
  norm_terminalJet_coleHopfRecursion_nonneg L _ (fun i => truncatedStepData_nonneg p hm q i)

theorem truncatedPotentialTerminal_at_top {L : ℕ} {qc : ℝ}
    (p : TruncatedRecursionParameter L qc) (hq : 0 ≤ qc) :
    truncatedPotentialTerminal p ⟨qc,⟨hq,le_rfl⟩⟩ = p.2.2.2 := by
  apply coleHopfRecursion_eq_terminal_of_zero
  intro i
  change p.1 (p.2.1 i.succ)-p.1 (truncatedClamp p.2.1 i ⟨qc,⟨hq,le_rfl⟩⟩) = 0
  have he : truncatedClamp p.2.1 i ⟨qc,⟨hq,le_rfl⟩⟩ = p.2.1 i.succ := by
    apply Subtype.ext
    change min (max qc _) _ = _
    rw [max_eq_left (p.2.1 i.castSucc).property.2,min_eq_right (p.2.1 i.succ).property.2]
  rw [he,sub_self]

theorem truncatedClamp_eq_upper_of_le {L : ℕ} {qc : ℝ}
    (node : Fin (L+1) → TruncatedClockDomain qc) (i : Fin L) (q : TruncatedClockDomain qc)
    (hq : node i.succ ≤ q) : truncatedClamp node i q = node i.succ := by
  apply Subtype.ext
  change min (max (q:ℝ) (node i.castSucc)) (node i.succ) = _
  exact min_eq_right (hq.trans (le_max_left _ _))

theorem truncatedClamp_eq_lower_of_le {L : ℕ} {qc : ℝ}
    (node : Fin (L+1) → TruncatedClockDomain qc) (hn : Monotone node)
    (i : Fin L) (q : TruncatedClockDomain qc) (hq : q ≤ node i.castSucc) :
    truncatedClamp node i q = node i.castSucc := by
  apply Subtype.ext
  change min (max (q:ℝ) (node i.castSucc)) (node i.succ) = _
  have hqR : (q:ℝ) ≤ (node i.castSucc:ℝ) := hq
  have hnR : (node i.castSucc:ℝ) ≤ (node i.succ:ℝ) := hn i.castSucc_lt_succ.le
  rw [max_eq_right hqR,min_eq_left hnR]

theorem truncatedClamp_eq_self {L : ℕ} {qc : ℝ}
    (node : Fin (L+1) → TruncatedClockDomain qc) (i : Fin L) (q : TruncatedClockDomain qc)
    (hq : q ∈ Icc (node i.castSucc) (node i.succ)) : truncatedClamp node i q = q := by
  apply Subtype.ext
  change min (max (q:ℝ) (node i.castSucc)) (node i.succ) = _
  have hqL : (node i.castSucc:ℝ) ≤ (q:ℝ) := hq.1
  have hqR : (q:ℝ) ≤ (node i.succ:ℝ) := hq.2
  rw [max_eq_left hqL,min_eq_left hqR]

theorem truncatedPotentialTerminal_cell {L : ℕ} {qc : ℝ}
    (p : TruncatedRecursionParameter L qc) (hn : Monotone p.2.1)
    (i : Fin L) (q : TruncatedClockDomain qc) (hq : q ∈ Icc (p.2.1 i.castSucc) (p.2.1 i.succ)) :
    truncatedPotentialTerminal p q = coleHopfTerminal
      ((p.2.2.1 i,p.1 (p.2.1 i.succ)-p.1 q),truncatedPotentialTerminal p (p.2.1 i.succ)) := by
  have hprefix (j : Fin L) (hji : j < i) :
      (truncatedStepData p q j).2 = 0 ∧
        (truncatedStepData p (p.2.1 i.succ) j).2 = 0 := by
    have hnj : j.succ ≤ i.castSucc := by
      change j.val+1 ≤ i.val
      exact Nat.succ_le_iff.mpr hji
    have hleft : p.2.1 j.succ ≤ q := (hn hnj).trans hq.1
    have hright : p.2.1 j.succ ≤ p.2.1 i.succ :=
      (hn hnj).trans (hn i.castSucc_lt_succ.le)
    simp only [truncatedStepData,truncatedClamp_eq_upper_of_le _ _ _ hleft,
      truncatedClamp_eq_upper_of_le _ _ _ hright,sub_self,and_self]
  have hi : (truncatedStepData p (p.2.1 i.succ) i).2 = 0 := by
    simp only [truncatedStepData,truncatedClamp_eq_upper_of_le _ _ _ le_rfl,sub_self]
  have htail (j : Fin L) (hij : i < j) :
      truncatedStepData p q j = truncatedStepData p (p.2.1 i.succ) j := by
    have hnj : i.succ ≤ j.castSucc := by
      change i.val+1 ≤ j.val
      exact Nat.succ_le_iff.mpr hij
    have hright : p.2.1 i.succ ≤ p.2.1 j.castSucc := hn hnj
    have hleft : q ≤ p.2.1 j.castSucc := hq.2.trans hright
    simp only [truncatedStepData,truncatedClamp_eq_lower_of_le _ hn _ _ hleft,
      truncatedClamp_eq_lower_of_le _ hn _ _ hright]
  have h := coleHopfRecursion_eq_step_of_zero_prefix
    (truncatedStepData p q) (truncatedStepData p (p.2.1 i.succ)) p.2.2.2 i hprefix hi htail
  simpa only [truncatedPotentialTerminal,truncatedStepData,truncatedClamp_eq_self _ _ _ hq] using h

theorem terminalValue_truncatedPotential_cell {L : ℕ} {qc : ℝ}
    (p : TruncatedRecursionParameter L qc) (hn : Monotone p.2.1) (hm : Monotone p.1)
    (i : Fin L) (q : TruncatedClockDomain qc) (hq : q ∈ Icc (p.2.1 i.castSucc) (p.2.1 i.succ))
    (x : ℝ) : terminalValue (truncatedPotentialTerminal p q) x =
      ColeHopfFoundation.ProbabilityTheory.coleHopf (p.2.2.1 i)
        (p.1 (p.2.1 i.succ)-p.1 q).toNNReal
        (terminalValue (truncatedPotentialTerminal p (p.2.1 i.succ))) x := by
  rw [truncatedPotentialTerminal_cell p hn i q hq]
  exact terminalValue_coleHopfTerminal_nonneg _ (sub_nonneg.mpr (hm hq.2)) x

end GeneralDepthPaper
