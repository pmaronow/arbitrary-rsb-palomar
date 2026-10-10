module

public import FRSB.MeasureCellInduction

@[expose] public section


/-! Finite adjacent closed-cell propagation, including a degenerate grid. -/
noncomputable section
open Set
namespace FourPapersCommon

theorem finite_closed_cell_constant {N : ℕ} {T : ℝ} (node : Fin (N+1) → ℝ)
    (hm : Monotone node) (h0 : node 0 = 0) (hT : node ⟨N,by omega⟩ = T)
    (F : ℝ → ℝ)
    (hc : ∀ i : Fin N,∀ t ∈ Icc (node i.castSucc) (node i.succ),F t = F (node i.castSucc)) :
    EqOn F (fun _ => F 0) (Icc (0 : ℝ) T) := by
  let S : ℕ → ℝ := fun k => node ⟨min k N,by omega⟩
  have hS : Monotone S := by
    intro i j hij
    apply hm
    exact min_le_min_right N hij
  have hS0 : S 0 = 0 := by simpa [S] using h0
  have hSN : S N = T := by simpa only [S,min_self] using hT
  have he := FRSB.finite_closed_interval_induction N S hS (fun t => F t=F 0)
    (by rw [hS0]) (by
      intro i hi hFi t ht
      let j : Fin N := ⟨i,hi⟩
      have hSi : S i = node j.castSucc := by simp only [S,min_eq_left hi.le]; rfl
      have hSi1 : S (i+1) = node j.succ := by simp only [S,min_eq_left (by omega : i+1 ≤ N)]; rfl
      rw [hSi,hSi1] at ht
      exact (hc j t ht).trans (by simpa only [hSi] using hFi))
  intro t ht
  exact he t (by simpa only [hS0,hSN] using ht)

theorem finite_closed_cell_constant_of_pair {N : ℕ} {T : ℝ} (node : Fin (N+1) → ℝ)
    (hm : Monotone node) (h0 : node 0 = 0) (hT : node ⟨N,by omega⟩ = T)
    (F : ℝ → ℝ)
    (hc : ∀ i : Fin N,∀ a ∈ Icc (node i.castSucc) (node i.succ),
      ∀ b ∈ Icc (node i.castSucc) (node i.succ),F b = F a) :
    EqOn F (fun _ => F 0) (Icc (0 : ℝ) T) :=
  finite_closed_cell_constant node hm h0 hT F (fun i t ht => hc i (node i.castSucc)
    ⟨le_rfl,hm (by exact_mod_cast Nat.le_succ i.val)⟩ t ht)

end FourPapersCommon
