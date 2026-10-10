module

public import FourPapersCommon.WeakTimeRecovery
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

@[expose] public section


/-! A continuous weak solution with a bounded measurable time source has
genuine Lipschitz time sections. The proof uses the already constructed
smooth plane mollifications and their actual weak-source derivatives. -/
noncomputable section
open Set MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff Convolution NNReal
namespace FourPapersCommon
set_option maxHeartbeats 600000

theorem norm_normedBump_convolution_le (w : ℝ × ℝ → ℝ)
    (hw : Measurable w) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ p, ‖w p‖ ≤ M)
    (φ : ContDiffBump (0 : ℝ × ℝ)) (p : ℝ × ℝ) :
    ‖(w ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (φ.normed volume)) p‖ ≤ M := by
  have hh := dist_convolution_le (μ := volume) (x₀ := p) (z₀ := (0 : ℝ)) hM
    φ.support_normed_eq.subset φ.nonneg_normed φ.integral_normed
    hw.aestronglyMeasurable (fun y _ => by simpa only [dist_zero_right] using hb y)
  rw [convolution_symm (ContinuousLinearMap.mul ℝ ℝ) (by ext; rfl)]
  change ‖∫ t, φ.normed volume t * w (p-t)‖ ≤ M
  simpa only [dist_zero_right,convolution_def,lsmul_apply,smul_eq_mul] using hh

theorem weakTime_norm_sub_le_interior (u w : ℝ × ℝ → ℝ)
    (hu : Continuous u) (hw : Paper.IsParisiWeakTimeDerivative u w)
    (hwm : Measurable w) (M : ℝ) (hb : ∀ p, ‖w p‖ ≤ M)
    (x : ℝ) {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hb' : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b) :
    ‖u (b,x) - u (a,x)‖ ≤ M * (b-a) := by
  have hM : 0 ≤ M := (norm_nonneg (w (0,0))).trans (hb (0,0))
  let F : ℕ → ℝ → ℝ := fun n t => timeMollification u
    ((Paper.parisiPlaneBump n).normed volume) t x
  have hn : ∀ᶠ n in atTop, (Paper.parisiPlaneBump n).rOut < min a (1-b) :=
    Paper.parisiPlaneBump_rOut_tendsto.eventually
      (eventually_lt_nhds (lt_min ha.1 (sub_pos.mpr hb'.2)))
  have hbound : ∀ᶠ n in atTop, ‖F n b - F n a‖ ≤ M * (b-a) := by
    filter_upwards [hn] with n hn
    have hd (t : ℝ) (ht : t ∈ Icc a b) :=
      hasDerivAt_timeMollification_of_weak u w hu hw (Paper.parisiPlaneBump n) t x
        ((hn.trans_le (min_le_left _ _)).trans_le ht.1)
        ((hn.trans_le (min_le_right _ _)).trans_le (by linarith [ht.2]))
    apply norm_image_sub_le_of_norm_deriv_le_segment'
      (fun t ht => (hd t ht).hasDerivWithinAt)
      (fun t _ => norm_normedBump_convolution_le w hwm M hM hb _ (t,x))
      b ⟨hab,le_rfl⟩
  have hF (t : ℝ) : Tendsto (fun n => F n t) atTop (𝓝 (u (t,x))) := by
    have hh := ContDiffBump.convolution_tendsto_right_of_continuous
      (μ := volume) Paper.parisiPlaneBump_rOut_tendsto hu (t,x)
    apply hh.congr
    intro n
    dsimp only [F,timeMollification]
    rw [convolution_symm (ContinuousLinearMap.mul ℝ ℝ) (by ext; rfl)]
    rfl
  exact le_of_tendsto ((hF b).sub (hF a)).norm hbound

theorem lipschitzOnWith_weakTime_section (u w : ℝ × ℝ → ℝ)
    (hu : Continuous u) (hw : Paper.IsParisiWeakTimeDerivative u w)
    (hwm : Measurable w) (M : ℝ) (hb : ∀ p, ‖w p‖ ≤ M) (x : ℝ) :
    LipschitzOnWith M.toNNReal (fun t => u (t,x)) (Icc (0 : ℝ) 1) := by
  have hM : 0 ≤ M := (norm_nonneg (w (0,0))).trans (hb (0,0))
  have hi (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1) (b : ℝ)
      (hb' : b ∈ Ioo (0 : ℝ) 1) : ‖u (a,x)-u (b,x)‖ ≤ M*‖a-b‖ := by
    rcases le_total a b with hab | hba
    · simpa only [norm_sub_rev,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hab),
        neg_sub] using weakTime_norm_sub_le_interior u w hu hw hwm M hb x ha hb' hab
    · simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hba)] using
        weakTime_norm_sub_le_interior u w hu hw hwm M hb x hb' ha hba
  let S : Set (ℝ × ℝ) := {p | ‖u (p.1,x)-u (p.2,x)‖ ≤ M*‖p.1-p.2‖}
  have hS : IsClosed S := isClosed_le
    ((hu.comp (continuous_fst.prodMk continuous_const)).sub
      (hu.comp (continuous_snd.prodMk continuous_const))).norm
    (continuous_const.mul (continuous_fst.sub continuous_snd).norm)
  have hs : (Ioo (0 : ℝ) 1) ×ˢ (Ioo (0 : ℝ) 1) ⊆ S := fun p hp => hi _ hp.1 _ hp.2
  have hc : (Icc (0 : ℝ) 1) ×ˢ (Icc (0 : ℝ) 1) ⊆ S := by
    have hh := closure_minimal hs hS
    simpa only [closure_prod_eq,closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] using hh
  apply LipschitzOnWith.of_dist_le_mul
  intro a ha b hb'
  simpa only [S,mem_setOf_eq,dist_eq_norm,Real.coe_toNNReal _ hM] using
    (hc (show (a,b) ∈ (Icc (0:ℝ) 1) ×ˢ Icc (0:ℝ) 1 from ⟨ha,hb'⟩))

end FourPapersCommon
