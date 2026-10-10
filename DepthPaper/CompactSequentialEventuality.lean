module

public import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.Tactic

@[expose] public section


/-! A compactness upgrade for the uniform eventual conclusions in the
physical parameter windows. A failing point is selected at every large
degree and an actual convergent subsequence contradicts the criterion. -/
noncomputable section
open Set Filter
open scoped Topology
namespace DepthPaper
variable {X : Type*} [MetricSpace X]

theorem compact_eventually_of_sequential {K : Set X} (hK : IsCompact K)
    (P : ℕ→X→Prop)
    (hseq : ∀p:ℕ→ℕ,Tendsto p atTop atTop→∀x:ℕ→X,
      (∀n,x n∈K)→∀x0∈K,Tendsto x atTop (𝓝 x0)→∀ᶠn in atTop,P (p n) (x n)) :
    ∀ᶠp:ℕ in atTop,∀x∈K,P p x := by
  by_contra hh
  rw [eventually_atTop] at hh
  push_neg at hh
  choose p hp x hx hbad using hh
  have hpt : Tendsto p atTop atTop:=tendsto_atTop_mono hp tendsto_id
  obtain ⟨x0,hx0,φ,hφ,ht⟩:=hK.tendsto_subseq hx
  have H:=hseq (p∘φ) (hpt.comp hφ.tendsto_atTop) (x∘φ)
    (fun n=>hx (φ n)) x0 hx0 ht
  obtain ⟨n,hn⟩:=H.exists
  exact hbad (φ n) hn

theorem compact_eventually_allowed_of_sequential {K : Set X} (hK : IsCompact K)
    (A : ℕ→Prop) (P : ℕ→X→Prop)
    (hseq : ∀p:ℕ→ℕ,(∀n,A (p n))→Tendsto p atTop atTop→∀x:ℕ→X,
      (∀n,x n∈K)→∀x0∈K,Tendsto x atTop (𝓝 x0)→∀ᶠn in atTop,P (p n) (x n)) :
    ∀ᶠp:ℕ in atTop,A p→∀x∈K,P p x := by
  by_contra hh
  rw [eventually_atTop] at hh
  push_neg at hh
  choose p hp hA x hx hbad using hh
  have hpt : Tendsto p atTop atTop:=tendsto_atTop_mono hp tendsto_id
  obtain ⟨x0,hx0,φ,hφ,ht⟩:=hK.tendsto_subseq hx
  have H:=hseq (p∘φ) (fun n=>hA (φ n)) (hpt.comp hφ.tendsto_atTop) (x∘φ)
    (fun n=>hx (φ n)) x0 hx0 ht
  obtain ⟨n,hn⟩:=H.exists
  exact hbad (φ n) hn

end DepthPaper
