module

public import FRSB.FiniteSchemeRepresentation

@[expose] public section


/-! Closed-cell induction on genuine finite RSB overlap nodes. Empty and
repeated-node cells are retained. -/

open Set
namespace FRSB
open SpinGlass.Targets

theorem finite_closed_interval_induction (N : ℕ) (T : ℕ → ℝ) (hT : Monotone T)
    (P : ℝ → Prop) (hbase : P (T 0))
    (hstep : ∀ i < N, P (T i) → ∀ t ∈ Icc (T i) (T (i + 1)), P t) :
    ∀ t ∈ Icc (T 0) (T N), P t := by
  have haux : ∀ i ≤ N, ∀ t ∈ Icc (T 0) (T i), P t := by
    intro i
    induction i with
    | zero =>
      intro _ t ht
      have he : t = T 0 := le_antisymm ht.2 ht.1
      exact he ▸ hbase
    | succ i ih =>
      intro hi t ht
      have hiN : i ≤ N := by omega
      by_cases hti : t ≤ T i
      · exact ih hiN t ⟨ht.1, hti⟩
      · exact hstep i (by omega) (ih hiN (T i) ⟨hT (Nat.zero_le i), le_rfl⟩)
          t ⟨(not_le.mp hti).le, ht.2⟩
  exact haux N le_rfl

def backwardSchemeClock {k : ℕ} (s : RSBScheme k) (β : ℝ) (i : ℕ) : ℝ :=
  β ^ 2 * (1 - s.q (k + 2 - min i (k + 2)))

theorem backwardSchemeClock_monotone {k : ℕ} (s : RSBScheme k) (β : ℝ) :
    Monotone (backwardSchemeClock s β) := by
  intro i j hij
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg β)
  apply sub_le_sub_left
  exact s.q_mono' (k + 2 - min i (k + 2)) (by omega)
    (k + 2 - min j (k + 2)) (Nat.sub_le_sub_left (min_le_min_right _ hij) _)

/-- Actual backward cells cover the whole physical clock strip. The only
input is the property propagated on each genuine closed cell. -/
theorem backward_scheme_cell_induction {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (P : ℝ → Prop) (hbase : P 0)
    (hstep : ∀ p ≤ k + 1, P (β ^ 2 * (1 - s.q (p + 1))) →
      ∀ t ∈ Icc (β ^ 2 * (1 - s.q (p + 1))) (β ^ 2 * (1 - s.q p)), P t) :
    ∀ t ∈ Icc (0 : ℝ) (β ^ 2), P t := by
  have hstart : backwardSchemeClock s β 0 = 0 := by simp [backwardSchemeClock, s.q_top]
  have hend : backwardSchemeClock s β (k + 2) = β ^ 2 := by simp [backwardSchemeClock, s.q_zero]
  have he := finite_closed_interval_induction (k + 2) (backwardSchemeClock s β)
    (backwardSchemeClock_monotone s β) P (hstart ▸ hbase) (fun i hi => ?_)
  · simpa only [hstart, hend] using he
  have hc0 : backwardSchemeClock s β i = β ^ 2 * (1 - s.q (k + 1 - i + 1)) := by
    unfold backwardSchemeClock
    rw [min_eq_left (by omega)]
    rw [show k + 2 - i = k + 1 - i + 1 by omega]
  have hc1 : backwardSchemeClock s β (i + 1) = β ^ 2 * (1 - s.q (k + 1 - i)) := by
    unfold backwardSchemeClock
    rw [min_eq_left (by omega)]
    rw [show k + 2 - (i + 1) = k + 1 - i by omega]
  rw [hc0, hc1]
  exact hstep (k + 1 - i) (by omega)

end FRSB
