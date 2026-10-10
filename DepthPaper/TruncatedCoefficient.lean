module

public import DepthPaper.TruncatedRecursionContinuity
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section


/-! Genuine finite-grid coefficients. Levels need not be monotone: the
truncated observable lemma assumes only that every level lies in [0,1]. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace DepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

def truncatedCoefficient {L : ℕ} {qc : ℝ} (p : TruncatedRecursionParameter L qc) (t : ℝ) : ℝ :=
  ∑i : Fin L,if t ∈ Ico (p.2.1 i.castSucc : ℝ) (p.2.1 i.succ : ℝ) then p.2.2.1 i else 0

theorem measurable_truncatedCoefficient {L : ℕ} {qc : ℝ} (p : TruncatedRecursionParameter L qc) :
    Measurable (truncatedCoefficient p) := by
  unfold truncatedCoefficient
  exact Finset.measurable_sum _ fun i _ => Measurable.ite measurableSet_Ico measurable_const measurable_const

theorem truncatedCoefficient_active_unique {L : ℕ} {qc : ℝ}
    (p : TruncatedRecursionParameter L qc) (hn : Monotone p.2.1) (t : ℝ) (i j : Fin L)
    (hi : t ∈ Ico (p.2.1 i.castSucc : ℝ) (p.2.1 i.succ : ℝ))
    (hj : t ∈ Ico (p.2.1 j.castSucc : ℝ) (p.2.1 j.succ : ℝ)) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hindex : i.succ ≤ j.castSucc := Nat.succ_le_iff.mpr hij
    have hh : (p.2.1 i.succ : ℝ) ≤ (p.2.1 j.castSucc : ℝ) := hn hindex
    linarith [hi.2,hj.1]
  · have hindex : j.succ ≤ i.castSucc := Nat.succ_le_iff.mpr hji
    have hh : (p.2.1 j.succ : ℝ) ≤ (p.2.1 i.castSucc : ℝ) := hn hindex
    linarith [hj.2,hi.1]

theorem truncatedCoefficient_eq_level {L : ℕ} {qc : ℝ}
    (p : TruncatedRecursionParameter L qc) (hn : Monotone p.2.1) (t : ℝ) (i : Fin L)
    (hi : t ∈ Ico (p.2.1 i.castSucc : ℝ) (p.2.1 i.succ : ℝ)) :
    truncatedCoefficient p t = p.2.2.1 i := by
  classical
  unfold truncatedCoefficient
  rw [Finset.sum_eq_single i]
  · simp only [if_pos hi]
  · intro j hj hji
    have hjnot : t ∉ Ico (p.2.1 j.castSucc : ℝ) (p.2.1 j.succ : ℝ) :=
      fun h => hji (truncatedCoefficient_active_unique p hn t j i h hi)
    exact if_neg hjnot
  · simp

theorem truncatedCoefficient_mem_Icc {L : ℕ} {qc : ℝ}
    (p : TruncatedRecursionParameter L qc) (hn : Monotone p.2.1)
    (ha : ∀i,p.2.2.1 i ∈ Icc (0:ℝ) 1) (t : ℝ) : truncatedCoefficient p t ∈ Icc (0:ℝ) 1 := by
  classical
  by_cases h : ∃i : Fin L,t ∈ Ico (p.2.1 i.castSucc : ℝ) (p.2.1 i.succ : ℝ)
  · obtain ⟨i,hi⟩ := h
    rw [truncatedCoefficient_eq_level p hn t i hi]
    exact ha i
  · have he : truncatedCoefficient p t = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact if_neg (fun hi => h ⟨i,hi⟩)
    rw [he]
    exact ⟨le_rfl,zero_le_one⟩

theorem tendsto_truncatedCoefficient_at_nonnode {L : ℕ} {qc : ℝ}
    (p : ℕ → TruncatedRecursionParameter L qc) (p0 : TruncatedRecursionParameter L qc)
    (hp : Tendsto p atTop (𝓝 p0)) (t : ℝ) (ht : ∀j : Fin (L+1),t ≠ (p0.2.1 j : ℝ)) :
    Tendsto (fun n => truncatedCoefficient (p n) t) atTop (𝓝 (truncatedCoefficient p0 t)) := by
  classical
  apply tendsto_finset_sum
  intro i hi
  have hnode (j : Fin (L+1)) : Tendsto (fun n => ((p n).2.1 j : ℝ)) atTop (𝓝 (p0.2.1 j : ℝ)) := by
    have hh : Continuous (fun pp : TruncatedRecursionParameter L qc => (pp.2.1 j : ℝ)) := by fun_prop
    exact hh.continuousAt.tendsto.comp hp
  have ha : Tendsto (fun n => (p n).2.2.1 i) atTop (𝓝 (p0.2.2.1 i)) := by
    have hh : Continuous (fun pp : TruncatedRecursionParameter L qc => pp.2.2.1 i) := by fun_prop
    exact hh.continuousAt.tendsto.comp hp
  by_cases hm : t ∈ Ico (p0.2.1 i.castSucc : ℝ) (p0.2.1 i.succ : ℝ)
  · have hleft : (p0.2.1 i.castSucc : ℝ) < t := lt_of_le_of_ne hm.1 (ht i.castSucc).symm
    have he : ∀ᶠ n in atTop,t ∈ Ico ((p n).2.1 i.castSucc : ℝ) ((p n).2.1 i.succ : ℝ) := by
      filter_upwards [(hnode i.castSucc).eventually (gt_mem_nhds hleft),
        (hnode i.succ).eventually (lt_mem_nhds hm.2)] with n hn hl
      exact ⟨hn.le,hl⟩
    simp only [if_pos hm]
    exact ha.congr' (he.mono fun n hn => (if_pos hn).symm)
  · have hc : t < (p0.2.1 i.castSucc : ℝ) ∨ (p0.2.1 i.succ : ℝ) < t := by
      simp only [mem_Ico,not_and_or,not_le,not_lt] at hm
      rcases hm with hl | hr
      · exact Or.inl hl
      · exact Or.inr (lt_of_le_of_ne hr (ht i.succ).symm)
    have he : ∀ᶠ n in atTop,t ∉ Ico ((p n).2.1 i.castSucc : ℝ) ((p n).2.1 i.succ : ℝ) := by
      rcases hc with hl | hr
      · filter_upwards [(hnode i.castSucc).eventually (lt_mem_nhds hl)] with n hn
        exact fun hh => (not_lt_of_ge hh.1) hn
      · filter_upwards [(hnode i.succ).eventually (gt_mem_nhds hr)] with n hn
        exact fun hh => (not_lt_of_ge hn.le) hh.2
    simp only [if_neg hm]
    exact tendsto_const_nhds.congr' (he.mono fun n hn => (if_neg hn).symm)

end DepthPaper
