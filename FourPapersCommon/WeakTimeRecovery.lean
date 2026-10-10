module

public import FourPapersCommon.WeakTimeMollification

@[expose] public section


/-! A continuous distributional time derivative is the actual classical
derivative at every point where its source is continuous. Genuine smooth
convolutions converge, together with their derivatives locally uniformly;
no differentiable representative is supplied. -/
noncomputable section
open Set MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff Convolution
namespace FourPapersCommon
set_option maxHeartbeats 500000

theorem hasDerivAt_time_of_weak_continuousAt (u w : ℝ×ℝ→ℝ)
    (hu : Continuous u) (hw : Paper.IsParisiWeakTimeDerivative u w)
    (hwm : Measurable w) (t x : ℝ) (ht : t∈Ioo (0:ℝ) 1)
    (hwc : ContinuousAt w (t,x)) :
    HasDerivAt (fun s=>u (s,x)) (w (t,x)) t := by
  let F : ℕ→ℝ→ℝ:=fun n s=>timeMollification u
    ((Paper.parisiPlaneBump n).normed volume) s x
  let G : ℕ→ℝ→ℝ:=fun n s=>(w ⋆[ContinuousLinearMap.mul ℝ ℝ,volume]
    ((Paper.parisiPlaneBump n).normed volume)) (s,x)
  have hC : Tendsto (fun p : ℕ×ℝ=>w (p.2,x)) (atTop×ˢ𝓝 t) (𝓝 (w (t,x))) :=
    hwc.tendsto.comp (tendsto_snd.prodMk_nhds tendsto_const_nhds)
  have hG : Tendsto (fun p : ℕ×ℝ=>G p.1 p.2) (atTop×ˢ𝓝 t) (𝓝 (w (t,x))) := by
    have hh:=ContDiffBump.convolution_tendsto_right (μ:=volume)
      (φ:=fun p : ℕ×ℝ=>Paper.parisiPlaneBump p.1)
      (g:=fun _ : ℕ×ℝ=>w) (k:=fun p : ℕ×ℝ=>(p.2,x))
      (Paper.parisiPlaneBump_rOut_tendsto.comp tendsto_fst)
      (.of_forall fun _=>hwm.aestronglyMeasurable)
      (hwc.tendsto.comp tendsto_snd)
      (tendsto_snd.prodMk_nhds tendsto_const_nhds)
    apply hh.congr
    intro p
    dsimp only [G]
    rw [convolution_symm (ContinuousLinearMap.mul ℝ ℝ) (by ext; rfl)]
    rfl
  have hGu : TendstoUniformlyOnFilter G (fun s=>w (s,x)) atTop (𝓝 t) := by
    rw [tendstoUniformlyOnFilter_iff_tendsto,Metric.uniformity_eq_comap_nhds_zero,
      tendsto_comap_iff]
    simpa only [Function.comp_def,dist_self] using hC.dist hG
  have hφ : ∀ᶠ n in atTop,(Paper.parisiPlaneBump n).rOut < min t (1-t)/2 :=
    Paper.parisiPlaneBump_rOut_tendsto.eventually
      (eventually_lt_nhds (half_pos (lt_min ht.1 (sub_pos.mpr ht.2))))
  have hs : ∀ᶠ s in 𝓝 t,t/2<s ∧ s<(1+t)/2 :=
    (eventually_gt_nhds (half_lt_self ht.1)).and
      (eventually_lt_nhds (by linarith [ht.2] : t<(1+t)/2))
  have hFG : ∀ᶠ p : ℕ×ℝ in atTop×ˢ𝓝 t,HasDerivAt (F p.1) (G p.1 p.2) p.2 := by
    filter_upwards [hφ.prod_mk hs] with p hp
    apply hasDerivAt_timeMollification_of_weak u w hu hw
    · have hm : min t (1-t)/2≤t/2 := by gcongr; exact min_le_left _ _
      exact hp.1.trans_le hm |>.trans hp.2.1
    · have hm : min t (1-t)/2≤(1-t)/2 := by gcongr; exact min_le_right _ _
      exact hp.1.trans_le hm |>.trans (by linarith [hp.2.2])
  have hF : ∀s : ℝ,Tendsto (fun n=>F n s) atTop (𝓝 (u (s,x))) := by
    intro s
    have hh:=ContDiffBump.convolution_tendsto_right_of_continuous
      (μ:=volume) Paper.parisiPlaneBump_rOut_tendsto hu (s,x)
    apply hh.congr
    intro n
    dsimp only [F,timeMollification]
    rw [convolution_symm (ContinuousLinearMap.mul ℝ ℝ) (by ext; rfl)]
    rfl
  exact hasDerivAt_of_tendstoUniformlyOnFilter hGu hFG (.of_forall hF)

end FourPapersCommon
