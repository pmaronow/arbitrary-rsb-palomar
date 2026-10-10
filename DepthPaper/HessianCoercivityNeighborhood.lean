module

public import FourPapersCommon.PositiveHessianPersistence

@[expose] public section


/-! True quantitative coercivity near a positive finite-dimensional
Hessian, in the actual norm and dual operator norm. -/
noncomputable section
open Set Filter
open scoped Topology
namespace DepthPaper
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 64
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem bilinear_coercivity_of_norm_close (B B0:E→L[ℝ] E→L[ℝ] ℝ) {c:ℝ}
    (hc:0 < c) (hB0:∀v:E,‖v‖=1→c ≤ B0 v v) (hclose:‖B-B0‖ ≤ c/2) :
    ∀v:E,c/2*‖v‖^2 ≤ B v v := by
  intro v
  by_cases hv:v=0
  · subst v
    simp
  · have hvn:0 < ‖v‖ := norm_pos_iff.mpr hv
    let u:E := ‖v‖⁻¹ • v
    have hu:‖u‖=1 := by
      dsimp only [u]
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hvn),inv_mul_cancel₀ hvn.ne']
    have hdiff:|B u u-B0 u u| ≤ c/2 := by
      have hh:‖(B-B0) u u‖ ≤ ‖B-B0‖*‖u‖*‖u‖ :=
        ((B-B0) u).le_opNorm u |>.trans
          (mul_le_mul_of_nonneg_right ((B-B0).le_opNorm u) (norm_nonneg u))
      have hh':|B u u-B0 u u| ≤ ‖B-B0‖ := by
        simpa only [ContinuousLinearMap.sub_apply,Real.norm_eq_abs,hu,mul_one] using hh
      exact hh'.trans hclose
    have hunit:c/2 ≤ B u u := by
      have hm := hB0 u hu
      linarith [(abs_le.mp hdiff).1]
    have hscale:‖v‖ • u=v := by
      dsimp only [u]
      rw [smul_smul,mul_inv_cancel₀ hvn.ne',one_smul]
    have he:B v v=‖v‖^2*B u u := by
      conv => lhs;rw [←hscale]
      simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
      ring
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hunit (sq_nonneg ‖v‖)]

theorem exists_bilinear_coercive_neighborhood
    {Θ:Type*} [TopologicalSpace Θ] [FiniteDimensional ℝ E]
    (B:Θ→E→L[ℝ] E→L[ℝ] ℝ) (p:Θ) (hcont:ContinuousAt B p)
    (hpos:∀v:E,v≠0→0 < B p v v) :
    ∃κ:ℝ,0 < κ ∧ ∃U:Set Θ,IsOpen U ∧ p∈U ∧
      ∀q∈U,∀v:E,κ*‖v‖^2 ≤ B q v v := by
  obtain ⟨c,hc,hmargin⟩ := FourPapersCommon.exists_positive_hessian_unit_margin (B p) hpos
  have hnear:∀ᶠq in 𝓝 p,‖B q-B p‖ < c/2 := by
    have hzero:ContinuousAt (fun q=>‖B q-B p‖) p := (hcont.sub continuousAt_const).norm
    have H := hzero (Iio_mem_nhds (show ‖B p-B p‖ < c/2 by simp;positivity))
    exact H
  obtain ⟨U,hUsub,hU,hp⟩ := mem_nhds_iff.mp hnear
  exact ⟨c/2,by positivity,U,hU,hp,fun q hq=>
    bilinear_coercivity_of_norm_close (B q) (B p) hc hmargin (hUsub hq).le⟩

end DepthPaper
