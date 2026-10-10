module

public import Paper.ParisiTimeRegularity
public import Paper.ParisiWeakLipschitz
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv

@[expose] public section


/-! Actual time derivatives of plane mollifications of a distributional
time equation. The weak identity is tested against the explicit reflected
smooth kernel, whose support lies in the physical open strip. -/
noncomputable section
open Set MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff Convolution
namespace FourPapersCommon
set_option maxHeartbeats 400000

def timeMollification (u φ : ℝ×ℝ→ℝ) (t x : ℝ) : ℝ :=
  (u ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] φ) (t,x)

theorem parisiTestT_reflected_time (φ : ℝ×ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ)
    (p y : ℝ×ℝ) :
    Paper.parisiTestT (Paper.reflectedParisiTest φ p) y=
      -fderiv ℝ φ (p-y) (1,0) := by
  have hd:=(hφ.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt y.1
    ((hasDerivAt_const y.1 p).sub
      ((hasDerivAt_id y.1).prodMk (hasDerivAt_const y.1 y.2)))
  simpa only [Paper.reflectedParisiTest,Paper.parisiTestT,Function.comp_def,
    Pi.sub_def,id_eq,Prod.mk.eta,zero_sub,map_neg] using hd.deriv

theorem hasDerivAt_timeMollification (u φ : ℝ×ℝ→ℝ) (hu : Continuous u)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (t x : ℝ) :
    HasDerivAt (fun s=>timeMollification u φ s x)
      (∫y,u y*fderiv ℝ φ ((t,x)-y) (1,0)) t := by
  have hl:=hu.locallyIntegrable (μ:=volume)
  have hd:=(hc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    hl (hφ.of_le (by simp)) (t,x)).comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  rw [convolution_precompR_apply _ hl (hc.fderiv ℝ)
    (hφ.continuous_fderiv (by simp))] at hd
  exact hd

theorem timeMollification_derivative_eq_weakAverage (u w φ : ℝ×ℝ→ℝ)
    (hu : Continuous u) (hw : Paper.IsParisiWeakTimeDerivative u w)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (p : ℝ×ℝ)
    (hs : tsupport (Paper.reflectedParisiTest φ p)⊆
      {y : ℝ×ℝ|0<y.1 ∧ y.1<1}) :
    (∫y,u y*fderiv ℝ φ (p-y) (1,0))=
      ∫y,w y*Paper.reflectedParisiTest φ p y := by
  let ψ:=Paper.reflectedParisiTest φ p
  have hψ:=Paper.contDiff_reflectedParisiTest φ hφ p
  have hψc:=Paper.hasCompactSupport_reflectedParisiTest φ hc p
  have htc:=Paper.hasCompactSupport_parisiTestT ψ hψ hψc
  have hi : Integrable (fun y=>u y*Paper.parisiTestT ψ y) volume :=
    (hu.mul (Paper.continuous_parisiTestT ψ hψ)).integrable_of_hasCompactSupport htc.mul_left
  have his : Integrable (fun y=>u y*Paper.parisiTestT ψ y) Paper.parisiSpaceTime := by
    rw [Paper.parisiSpaceTime_eq_restrict_volume]
    exact hi.restrict
  obtain ⟨hwi,hwe⟩:=hw ψ hψ hψc hs
  have hws : Integrable (fun y=>w y*ψ y) Paper.parisiSpaceTime :=
    (hwi.sub his).congr (.of_forall fun y=>by simp only [Pi.sub_apply];ring)
  rw [integral_add his hws] at hwe
  have hut : (∫y,u y*Paper.parisiTestT ψ y∂Paper.parisiSpaceTime)=
      -(∫y,u y*fderiv ℝ φ (p-y) (1,0)) := by
    rw [Paper.integral_parisiSpaceTime_eq_volume_of_support]
    · simp_rw [ψ,parisiTestT_reflected_time φ hφ p,mul_neg]
      exact integral_neg _
    · intro y hy
      have hy':=hs ((Paper.tsupport_parisiTestT_subset ψ hψ)
        (subset_closure (Function.support_mul_subset_right _ _ hy)))
      exact ⟨⟨hy'.1.le,hy'.2.le⟩,mem_univ _⟩
  have hwt : (∫y,w y*ψ y∂Paper.parisiSpaceTime)=∫y,w y*ψ y := by
    apply Paper.integral_parisiSpaceTime_eq_volume_of_support
    intro y hy
    have hy':=hs (subset_closure (Function.support_mul_subset_right _ _ hy))
    exact ⟨⟨hy'.1.le,hy'.2.le⟩,mem_univ _⟩
  rw [hut,hwt] at hwe
  linarith

theorem hasDerivAt_timeMollification_of_weak (u w : ℝ×ℝ→ℝ)
    (hu : Continuous u) (hw : Paper.IsParisiWeakTimeDerivative u w)
    (φ : ContDiffBump (0:ℝ×ℝ)) (t x : ℝ)
    (hl : φ.rOut<t) (hr : φ.rOut<1-t) :
    HasDerivAt (fun s=>timeMollification u (φ.normed volume) s x)
      ((w ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] (φ.normed volume)) (t,x)) t := by
  have hd:=hasDerivAt_timeMollification u (φ.normed volume) hu
    (φ.contDiff_normed (μ:=volume)) (φ.hasCompactSupport_normed (μ:=volume)) t x
  rw [timeMollification_derivative_eq_weakAverage u w (φ.normed volume) hu hw
    (φ.contDiff_normed (μ:=volume)) (φ.hasCompactSupport_normed (μ:=volume)) (t,x)
    (Paper.tsupport_reflected_planeBump_subset φ t x hl hr)] at hd
  exact hd

end FourPapersCommon
