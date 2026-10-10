module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

@[expose] public section


/-! Strong continuity of translation is equivalent to uniform continuity of a
bounded function. This uses the fixed function's modulus of continuity, without
asserting operator-norm continuity of the translation group. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction
namespace DepthPaper

def bcfSpatialTranslate (a : ℝ) (G : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  G.compContinuous ⟨fun x:ℝ=>x+a,by fun_prop⟩
@[simp] theorem bcfSpatialTranslate_apply (a : ℝ) (G : ℝ →ᵇ ℝ) (x : ℝ) :
    bcfSpatialTranslate a G x=G (x+a) := rfl
@[simp] theorem bcfSpatialTranslate_zero (G : ℝ →ᵇ ℝ) : bcfSpatialTranslate 0 G=G := by ext x; simp

theorem continuous_bcfSpatialTranslate (G : ℝ →ᵇ ℝ) (hG : UniformContinuous G) :
    Continuous (fun a:ℝ=>bcfSpatialTranslate a G) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuous_iff.mp hG (ε/2) (by positivity)
  refine ⟨δ,hδ,fun b hb=>?_⟩
  rw [dist_eq_norm]
  apply lt_of_le_of_lt ?_ (by linarith : ε/2<ε)
  apply (BoundedContinuousFunction.norm_le (by positivity : 0≤ε/2)).mpr
  intro x
  change ‖G (x+b)-G (x+a)‖≤ε/2
  rw [←dist_eq_norm]
  apply (hd ?_).le
  simpa only [Real.dist_eq,add_sub_add_left_eq_sub] using hb

theorem uniformContinuous_of_bcfSpatialTranslate (G : ℝ →ᵇ ℝ)
    (h : ContinuousAt (fun a:ℝ=>bcfSpatialTranslate a G) 0) : UniformContinuous G := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := Metric.continuousAt_iff.mp h ε hε
  refine ⟨δ,hδ,fun x y hxy=>?_⟩
  have hh : dist (y-x) (0:ℝ)<δ := by simpa only [Real.dist_eq,sub_zero,abs_sub_comm] using hxy
  have ht := hd hh
  rw [bcfSpatialTranslate_zero,dist_eq_norm] at ht
  calc
    dist (G x) (G y)=‖(bcfSpatialTranslate (y-x) G-G) x‖ := by
      simp only [bcfSpatialTranslate_apply,BoundedContinuousFunction.sub_apply,add_sub_cancel_left,
        dist_eq_norm,norm_sub_rev,←add_sub_assoc]
    _≤‖bcfSpatialTranslate (y-x) G-G‖ := BoundedContinuousFunction.norm_coe_le_norm _ x
    _<ε := ht

theorem uniformContinuous_bcf_mul (F G : ℝ →ᵇ ℝ) (hF : UniformContinuous F)
    (hG : UniformContinuous G) : UniformContinuous (F*G) := by
  apply uniformContinuous_of_bcfSpatialTranslate
  have he : (fun a:ℝ=>bcfSpatialTranslate a (F*G))=
      fun a=>bcfSpatialTranslate a F*bcfSpatialTranslate a G := by funext a; ext x; rfl
  rw [he]
  exact ((continuous_bcfSpatialTranslate F hF).mul (continuous_bcfSpatialTranslate G hG)).continuousAt

theorem uniformContinuous_bcf_pow (F : ℝ →ᵇ ℝ) (hF : UniformContinuous F) (n : ℕ) :
    UniformContinuous (F^n) := by
  induction n with
  | zero => change UniformContinuous (fun _:ℝ=>(1:ℝ)); exact uniformContinuous_const
  | succ n ih => rw [pow_succ]; exact uniformContinuous_bcf_mul _ _ ih hF

end DepthPaper
