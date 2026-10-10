module

public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.ContinuousOn

@[expose] public section

/-! Continuity of the genuine unique zero in a compact fiber. This is a
closed-graph argument and assumes no regularity of the selected root. -/
noncomputable section
open Set
namespace DepthPaper.RevisedClosedIFT
universe u v
variable {E : Type u} [TopologicalSpace E]
  {F : Type v} [TopologicalSpace F] [T2Space F]

theorem continuousOn_unique_zero {D : Set E} {K : Set F} {Φ : E×F→F} {y : E→F}
    [Zero F] (hK : IsCompact K) (hΦ : ContinuousOn Φ (D×ˢK))
    (hyK : ∀θ∈D,y θ∈K) (hzero : ∀θ∈D,Φ (θ,y θ)=0)
    (hunique : ∀θ∈D,∀z∈K,Φ (θ,z)=0 → z=y θ) : ContinuousOn y D := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let ys : D→K := fun θ=>⟨y θ,hyK θ θ.property⟩
  let G : D×K→F := fun p=>Φ ((p.1:E),(p.2:F))
  have hG : Continuous G := hΦ.comp_continuous
    (continuous_subtype_val.prodMap continuous_subtype_val)
    (fun p=>⟨p.1.property,p.2.property⟩)
  have hgraph : ys.graph=G⁻¹'{0} := by
    ext p
    change ys p.1=p.2 ↔ Φ ((p.1:E),(p.2:F))=0
    constructor
    · intro hp
      have he := congrArg Subtype.val hp
      change y (p.1:E)=(p.2:F) at he
      rw [←he]
      exact hzero p.1 p.1.property
    · intro hp
      apply Subtype.ext
      exact (hunique p.1 p.1.property p.2 p.2.property hp).symm
  have hc : Continuous ys := continuous_of_isClosed_graph
    (hgraph.symm ▸ (isClosed_singleton.preimage hG))
  exact continuousOn_iff_continuous_domRestrict.mpr (continuous_subtype_val.comp hc)

end DepthPaper.RevisedClosedIFT
