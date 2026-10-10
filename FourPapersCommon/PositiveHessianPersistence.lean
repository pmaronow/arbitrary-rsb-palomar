module

public import FourPapersCommon.PositiveHessianEquivalence
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

@[expose] public section


/-! Positive definite real bilinear forms are an open set in operator norm
on every finite-dimensional normed space. Compactness of the actual unit
sphere gives the uniform margin, without imposing a Euclidean norm. -/
noncomputable section
open Set Metric
open scoped Topology
namespace FourPapersCommon
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_positive_hessian_unit_margin (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v : E,v≠0 → 0 < B v v) :
    ∃ c : ℝ,0<c ∧ ∀ v : E,‖v‖=1 → c ≤ B v v := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · refine ⟨1,zero_lt_one,?_⟩
    intro v hv
    have hz : v=0 := Subsingleton.eq_zero v
    simp only [hz,norm_zero] at hv
    norm_num at hv
  · have hQ : Continuous (fun v : E=>B v v) :=
      (continuous_const.clm_apply continuous_id).clm_apply continuous_id
    obtain ⟨u,hu,hm⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
      (NormedSpace.sphere_nonempty.mpr zero_le_one) hQ.continuousOn
    have hun : ‖u‖=1 := by simpa only [mem_sphere_zero_iff_norm] using hu
    have hune : u≠0 := by intro hz;simp only [hz,norm_zero] at hun;norm_num at hun
    refine ⟨B u u,hB u hune,?_⟩
    intro v hv
    exact hm (by simpa only [mem_sphere_zero_iff_norm] using hv)

theorem exists_positive_hessian_norm_radius (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v : E,v≠0 → 0 < B v v) :
    ∃ ε : ℝ,0<ε ∧ ∀ B' : E →L[ℝ] E →L[ℝ] ℝ,
      ‖B'-B‖<ε → ∀ v : E,v≠0 → 0 < B' v v := by
  obtain ⟨c,hc,hmargin⟩ := exists_positive_hessian_unit_margin B hB
  refine ⟨c/2,by positivity,?_⟩
  intro B' hclose v hv
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let u : E := ‖v‖⁻¹ • v
  have hu : ‖u‖=1 := by
    dsimp only [u]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hvn),inv_mul_cancel₀ hvn.ne']
  have he : |B' u u-B u u| ≤ ‖B'-B‖ := by
    have hh : ‖(B'-B) u u‖ ≤ ‖B'-B‖*‖u‖*‖u‖ := by
      calc
        _ ≤ ‖(B'-B) u‖*‖u‖ := ((B'-B) u).le_opNorm u
        _ ≤ (‖B'-B‖*‖u‖)*‖u‖ :=
          mul_le_mul_of_nonneg_right ((B'-B).le_opNorm u) (norm_nonneg _)
    simpa only [ContinuousLinearMap.sub_apply,Real.norm_eq_abs,hu,mul_one] using hh
  have hpos : 0 < B' u u := by
    have hm := hmargin u hu
    have he' := neg_abs_le (B' u u-B u u)
    linarith
  have hscale : ‖v‖ • u=v := by
    dsimp only [u]
    rw [smul_smul,mul_inv_cancel₀ hvn.ne',one_smul]
  have hscalar : B' (‖v‖ • u) (‖v‖ • u)=‖v‖^2*B' u u := by
    simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
    ring
  rw [hscale] at hscalar
  rw [hscalar]
  exact mul_pos (sq_pos_of_pos hvn) hpos

theorem isOpen_positive_hessians :
    IsOpen {B : E →L[ℝ] E →L[ℝ] ℝ | ∀ v : E,v≠0 → 0 < B v v} := by
  change @IsOpen _ (ContinuousLinearMap.toPseudoMetricSpace
    (E := E) (F := E →L[ℝ] ℝ)).toUniformSpace.toTopologicalSpace _
  apply Metric.isOpen_iff.mpr
  intro B hB
  obtain ⟨ε,hε,hball⟩ := exists_positive_hessian_norm_radius B hB
  refine ⟨ε,hε,?_⟩
  intro B' hB'
  exact hball B' (by simpa only [mem_ball,dist_eq_norm] using hB')

end FourPapersCommon
