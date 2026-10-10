module

public import Mathlib.Topology.Compactness.Compact

@[expose] public section


/-! The compact-fiber tube lemma gives an actual open parameter domain for
an equation that is smooth on a neighborhood of a whole closed interval. -/
open Set Filter
open scoped Topology
namespace DepthPaper

def compactFiberDomain {E F : Type*} (U : Set (E × F)) (K : Set F) : Set E :=
  {θ | ∀ q ∈ K, (θ,q) ∈ U}

theorem isOpen_compactFiberDomain {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (U : Set (E × F)) (hU : IsOpen U) (K : Set F) (hK : IsCompact K) :
    IsOpen (compactFiberDomain U K) := by
  apply isOpen_iff_mem_nhds.mpr
  intro θ hθ
  have hsubset : ({θ} : Set E) ×ˢ K ⊆ U := by
    rintro ⟨u,q⟩ ⟨hu,hq⟩
    have he : u = θ := hu
    subst u
    exact hθ q hq
  obtain ⟨V,W,hV,hW,hθV,hKW,hVW⟩ :=
    generalized_tube_lemma isCompact_singleton hK hU hsubset
  apply mem_of_superset (hV.mem_nhds (hθV (mem_singleton θ)))
  intro u hu q hq
  exact hVW ⟨hu,hKW hq⟩

end DepthPaper
