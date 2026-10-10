module

public import FRSB.CompactLipschitzConvergence
public import Mathlib.Topology.Order.Compact

@[expose] public section


/-! A continuous common derivative envelope suffices for local uniform
 convergence, even when that envelope is unbounded at spatial infinity. -/
open Set Filter
open scoped Topology NNReal
namespace FRSB

theorem tendstoUniformlyOn_of_common_lipschitzOn {A : Type*} {l : Filter A}
    (f : A → ℝ → ℝ) (g : ℝ → ℝ) (S : Set ℝ) (hS : IsCompact S)
    (K : ℝ≥0) (hLip : ∀ i, LipschitzOnWith K (f i) S)
    (hpoint : ∀ x ∈ S, Tendsto (fun i => f i x) l (𝓝 (g x))) :
    TendstoUniformlyOn f g l S := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let F : A → S → ℝ := fun i x => f i x
  let G : S → ℝ := fun x => g x
  have hmod : Tendsto (fun r : ℝ => (K : ℝ) * r) (𝓝 0) (𝓝 0) := by
    simpa only [mul_zero, id_eq] using
      (tendsto_id : Tendsto (fun r : ℝ => r) (𝓝 0) (𝓝 0)).const_mul (K : ℝ)
  have heq : Equicontinuous F :=
    (Metric.uniformEquicontinuous_of_continuity_modulus (fun r => (K : ℝ) * r) hmod F
      (fun x y i => by
        simpa only [F, Subtype.dist_eq] using (hLip i).dist_le_mul x x.2 y y.2)).equicontinuous
  have hp : Tendsto F l (𝓝 G) := tendsto_pi_nhds.mpr fun x => hpoint x x.2
  have hu := (heq.tendsto_uniformFun_iff_pi l G).mpr hp
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
    (UniformFun.tendsto_iff_tendstoUniformly.mp hu)

theorem tendstoUniformlyOn_of_common_continuous_derivative_bound
    {A : Type*} {l : Filter A} (f : A → ℝ → ℝ) (g : ℝ → ℝ)
    (D : ℝ → ℝ) (hD : Continuous D) (S : Set ℝ) (hS : IsCompact S)
    (hd : ∀ i, Differentiable ℝ (f i))
    (hbound : ∀ i x, ‖deriv (f i) x‖ ≤ D x)
    (hpoint : ∀ x ∈ S, Tendsto (fun i => f i x) l (𝓝 (g x))) :
    TendstoUniformlyOn f g l S := by
  obtain ⟨R, _hR, hSR⟩ := hS.isBounded.exists_pos_norm_le
  have hsub : S ⊆ Icc (-R) R := by
    intro x hx
    exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hSR x hx)
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image
    (hD.continuousOn : ContinuousOn D (Icc (-R) R))
  apply tendstoUniformlyOn_of_common_lipschitzOn f g S hS (Real.nnabs M) _ hpoint
  intro i
  have hl : LipschitzOnWith (Real.nnabs M) (f i) (Icc (-R) R) :=
    (convex_Icc (-R) R).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x _ => (hd i x).hasDerivAt.hasDerivWithinAt) (fun x hx => by
        rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_nnabs]
        exact (hbound i x).trans ((hM (mem_image_of_mem D hx)).trans (le_abs_self M)))
  exact hl.mono hsub

end FRSB
