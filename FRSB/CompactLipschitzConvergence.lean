module

public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section


/-! Common derivative bounds turn pointwise convergence into local uniform convergence. -/
open Set Filter
open scoped Topology NNReal
namespace FRSB

theorem tendstoUniformlyOn_of_common_lipschitz {A : Type*} {l : Filter A}
    (f : A → ℝ → ℝ) (g : ℝ → ℝ) (S : Set ℝ) (hS : IsCompact S)
    (K : ℝ≥0) (hLip : ∀ i, LipschitzWith K (f i))
    (hpoint : ∀ x ∈ S, Tendsto (fun i => f i x) l (𝓝 (g x))) :
    TendstoUniformlyOn f g l S := by
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let F : A → S → ℝ := fun i x => f i x
  let G : S → ℝ := fun x => g x
  have hmod : Tendsto (fun r : ℝ => (K : ℝ) * r) (𝓝 0) (𝓝 0) := by
    convert! (tendsto_id : Tendsto (fun r : ℝ => r) (𝓝 0) (𝓝 0)).const_mul (K : ℝ)
      using 1 <;> simp
  have heq : Equicontinuous F :=
    (Metric.uniformEquicontinuous_of_continuity_modulus (fun r => (K : ℝ) * r) hmod F
      (fun x y i => by simpa only [F, Subtype.dist_eq] using (hLip i).dist_le_mul x y)).equicontinuous
  have hp : Tendsto F l (𝓝 G) := tendsto_pi_nhds.mpr fun x => hpoint x x.2
  have hu := (heq.tendsto_uniformFun_iff_pi l G).mpr hp
  have hh : TendstoUniformly F G l := UniformFun.tendsto_iff_tendstoUniformly.mp hu
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr hh

theorem tendstoUniformlyOn_of_common_derivative_bound {A : Type*} {l : Filter A}
    (f : A → ℝ → ℝ) (g : ℝ → ℝ) (S : Set ℝ) (hS : IsCompact S)
    (K : ℝ≥0) (hd : ∀ i, Differentiable ℝ (f i))
    (hbound : ∀ i x, ‖deriv (f i) x‖ ≤ K)
    (hpoint : ∀ x ∈ S, Tendsto (fun i => f i x) l (𝓝 (g x))) :
    TendstoUniformlyOn f g l S :=
  tendstoUniformlyOn_of_common_lipschitz f g S hS K
    (fun i => lipschitzWith_of_nnnorm_deriv_le (hd i) (fun x => by
      exact_mod_cast hbound i x)) hpoint

end FRSB
