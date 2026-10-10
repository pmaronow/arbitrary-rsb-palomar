module

public import DepthPaper.TerminalSpace
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

@[expose] public section


/-! A genuine parameter derivative in the sup norm. Pointwise derivatives
alone do not suffice: continuity of the derivative family in the sup norm
is used in the uniform mean-value remainder estimate. -/
noncomputable section
open Set Filter Asymptotics
open scoped Topology BoundedContinuousFunction NNReal ContDiff
namespace DepthPaper
set_option maxHeartbeats 500000
set_option maxSynthPendingDepth 64

theorem hasDerivAt_bcf_of_pointwise {A : Type*} [TopologicalSpace A]
    (f df : ℝ→A→ᵇℝ) (U : Set ℝ) (hU : IsOpen U) {p : ℝ} (hp : p∈U)
    (hd : ∀q∈U,∀x,HasDerivAt (fun r=>f r x) (df q x) q)
    (hc : ContinuousAt df p) : HasDerivAt f (df p) p := by
  rw [hasDerivAt_iff_isLittleO,isLittleO_iff]
  intro c hcpos
  have he : ∀ᶠq in 𝓝 p,q∈U ∧ ‖df q-df p‖<c := by
    filter_upwards [hU.mem_nhds hp,
      ((hc.sub (continuousAt_const (y:=df p))).norm.tendsto
        (gt_mem_nhds (by simpa using hcpos)))] with q hq hdq
    exact ⟨hq,hdq⟩
  obtain ⟨δ,hδ,hbound⟩:=Metric.eventually_nhds_iff.mp he
  filter_upwards [Metric.ball_mem_nhds p hδ] with q hq
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hcpos.le (norm_nonneg _))).mpr
  intro x
  let g:ℝ→ℝ:=fun r=>f r x-f p x-(r-p)*df p x
  have hgd : ∀r∈Metric.ball p δ,
      HasDerivWithinAt g (df r x-df p x) (Metric.ball p δ) r := by
    intro r hr
    have hg:=(hd r (hbound hr).1 x).sub_const (f p x)
    have ha:=((hasDerivAt_id r).sub_const p).mul_const (df p x)
    convert (hg.sub ha).hasDerivWithinAt using 1
    · funext a
      simp [g]
    · simp
  have hgn : ∀r∈Metric.ball p δ,‖df r x-df p x‖≤c := by
    intro r hr
    exact ((df r-df p).norm_coe_le_norm x).trans (hbound hr).2.le
  have hh:=Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (x:=p) (y:=q) hgd hgn
    (convex_ball p δ) (by simpa using hδ) hq
  simpa only [g,sub_self,zero_mul,sub_zero,BoundedContinuousFunction.coe_sub,
    BoundedContinuousFunction.coe_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] using hh

theorem lipschitzOnWith_bcf_of_pointwise {A : Type*} [TopologicalSpace A]
    (f df : ℝ→A→ᵇℝ) (s : Set ℝ) (hs : Convex ℝ s) (K : ℝ≥0)
    (hd : ∀q∈s,∀x,HasDerivWithinAt (fun r=>f r x) (df q x) s q)
    (hb : ∀q∈s,∀x,‖df q x‖≤K) : LipschitzOnWith K f s := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro p hp q hq
  rw [dist_eq_norm,dist_eq_norm]
  apply (BoundedContinuousFunction.norm_le (mul_nonneg K.coe_nonneg (norm_nonneg _))).mpr
  intro x
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r hr=>hd r hr x) (fun r hr=>hb r hr x) hs hq hp

theorem hasDerivWithinAt_bcf_of_pointwise {A : Type*} [TopologicalSpace A]
    (f df : ℝ→A→ᵇℝ) (s : Set ℝ) (hs : Convex ℝ s) {p : ℝ} (hp : p∈s)
    (hd : ∀q∈s,∀x,HasDerivWithinAt (fun r=>f r x) (df q x) s q)
    (hc : ContinuousWithinAt df s p) : HasDerivWithinAt f (df p) s p := by
  rw [hasDerivWithinAt_iff_isLittleO,isLittleO_iff]
  intro c hcpos
  have he : ∀ᶠq in 𝓝[s] p,‖df q-df p‖<c :=
    ((hc.sub (continuousWithinAt_const (b:=df p))).norm.tendsto
      (gt_mem_nhds (by simpa using hcpos)))
  obtain ⟨δ,hδ,hbound⟩:=Metric.mem_nhdsWithin_iff.mp he
  filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Metric.ball_mem_nhds p hδ)] with q hqs hq
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hcpos.le (norm_nonneg _))).mpr
  intro x
  let g:ℝ→ℝ:=fun r=>f r x-f p x-(r-p)*df p x
  have hgd : ∀r∈Metric.ball p δ∩s,
      HasDerivWithinAt g (df r x-df p x) (Metric.ball p δ∩s) r := by
    intro r hr
    have hg:=(hd r hr.2 x).sub_const (f p x)
    have ha:=((hasDerivAt_id r).sub_const p).mul_const (df p x)
    convert ((hg.sub ha.hasDerivWithinAt).mono inter_subset_right) using 1
    · funext a
      simp [g]
    · simp
  have hgn : ∀r∈Metric.ball p δ∩s,‖df r x-df p x‖≤c := by
    intro r hr
    exact ((df r-df p).norm_coe_le_norm x).trans (hbound hr).le
  have hh:=Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (x:=p) (y:=q) hgd hgn
    ((convex_ball p δ).inter hs) ⟨by simpa using hδ,hp⟩ ⟨hq,hqs⟩
  simpa only [g,sub_self,zero_mul,sub_zero,BoundedContinuousFunction.coe_sub,
    BoundedContinuousFunction.coe_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] using hh

theorem contDiffOn_of_within_derivative_chain {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s) (G : ℕ→ℝ→F)
    (hG : ∀j,∀x∈s,HasDerivWithinAt (G j) (G (j+1) x) s x) (j : ℕ) :
    ContDiffOn ℝ ∞ (G j) s := by
  have hn:∀n:ℕ,∀j:ℕ,ContDiffOn ℝ n (G j) s := by
    intro n
    induction n with
    | zero =>
      intro j
      change ContDiffOn ℝ 0 (G j) s
      rw [contDiffOn_zero]
      exact fun x hx=>(hG j x hx).continuousWithinAt
    | succ n ih =>
      intro j
      rw [show ((n+1:ℕ):ℕ∞ω)=(n:ℕ∞ω)+1 by simp,
        contDiffOn_succ_iff_derivWithin hs]
      refine ⟨fun x hx=>(hG j x hx).differentiableWithinAt,?_,?_⟩
      · intro hw
        simp at hw
      · exact (ih (j+1)).congr (fun x hx=>(hG j x hx).derivWithin (hs x hx))
  exact contDiffOn_infty.mpr (fun n=>hn n j)

theorem iteratedDerivWithin_of_within_derivative_chain {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s) (G : ℕ→ℝ→F)
    (hG : ∀j,∀x∈s,HasDerivWithinAt (G j) (G (j+1) x) s x)
    (j : ℕ) {x : ℝ} (hx : x∈s) :
    iteratedDerivWithin j (G 0) s x=G j x := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    rw [iteratedDerivWithin_succ,
      derivWithin_congr (fun y hy=>ih hy) (ih hx)]
    exact (hG j x hx).derivWithin (hs x hx)

end DepthPaper
