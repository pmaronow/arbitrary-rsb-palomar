module

public import GeneralDepthPaper.CompactTiltKernel
public import GeneralDepthPaper.TerminalReconstruction
public import GeneralDepthPaper.GaussianNormalizerUnits
public import Mathlib.Analysis.Calculus.ContDiff.Comp

@[expose] public section


/-! Normalized compact-tilt responses are actual Gaussian increment averages,
with joint smoothness in all Banach parameters. The proof differentiates the
analytic bounded kernel and uses its genuinely positive uniform normalizer. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000

theorem compactTiltNormalizer_apply (w : ℝ≥0) (p : CompactTiltParameter) (hp : 0<p.1)
    (s : CompactTiltLocation) :
    compactTiltNormalizer w p s=∫d,Real.exp (compactTiltLaplaceLinear (d,s) p) ∂gaussianReal 0 w := by
  change (∫d,compactTiltKernel p (d,s) ∂gaussianReal 0 w)=_
  apply integral_congr_ae
  exact .of_forall fun d=>compactTiltKernel_apply p hp (d,s)

def compactTiltLower (w : ℝ≥0) (p : CompactTiltParameter) : ℝ :=
  ∫d,Real.exp (-(‖p.2.1‖+‖p.2.2‖)*‖d‖-p.1*d^2) ∂gaussianReal 0 w

theorem integrable_compactTiltLower (w : ℝ≥0) (p : CompactTiltParameter) (hp : 0<p.1) :
    Integrable (fun d=>Real.exp (-(‖p.2.1‖+‖p.2.2‖)*‖d‖-p.1*d^2)) (gaussianReal 0 w) := by
  apply (integrable_const (μ:=gaussianReal 0 w) (1:ℝ)).mono'
  · exact (Real.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  · exact .of_forall fun d=>by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      apply Real.exp_le_one_iff.mpr
      have h1 := mul_nonneg (add_nonneg (norm_nonneg p.2.1) (norm_nonneg p.2.2)) (norm_nonneg d)
      have h2 := mul_nonneg hp.le (sq_nonneg d)
      nlinarith

theorem compactTiltLower_pos (w : ℝ≥0) (p : CompactTiltParameter) (hp : 0<p.1) :
    0<compactTiltLower w p := integral_exp_pos (integrable_compactTiltLower w p hp)

theorem compactTiltLower_le (w : ℝ≥0) (p : CompactTiltParameter) (hp : 0<p.1)
    (s : CompactTiltLocation) : compactTiltLower w p≤compactTiltNormalizer w p s := by
  change (∫d,Real.exp (-(‖p.2.1‖+‖p.2.2‖)*‖d‖-p.1*d^2) ∂gaussianReal 0 w)≤
    ∫d,compactTiltKernel p (d,s) ∂gaussianReal 0 w
  apply integral_mono (integrable_compactTiltLower w p hp)
    (integrable_parametricGaussianKernel_section w (compactTiltKernel p) s)
  intro d
  dsimp only
  rw [compactTiltKernel_apply p hp (d,s)]
  apply Real.exp_le_exp.mpr
  rw [compactTiltLaplaceLinear_apply]
  have hi (g : TerminalSpace) :
      ‖terminalValue g (s.2+d)-terminalValue g s.2‖≤‖g‖*‖d‖ := by
    have h := norm_terminalValue_sub_le g s.2 (s.2+d)
    simp only [add_sub_cancel_left] at h
    exact h.trans (mul_le_mul_of_nonneg_right (norm_terminalJet_le g 0) (norm_nonneg _))
  have h1 : -‖p.2.1‖*‖d‖≤(s.1:ℝ)*(terminalValue p.2.1 (s.2+d)-terminalValue p.2.1 s.2) := by
    have hlow := neg_abs_le (terminalValue p.2.1 (s.2+d)-terminalValue p.2.1 s.2)
    have hb := hi p.2.1
    rw [Real.norm_eq_abs] at hb
    have hprod := mul_le_mul_of_nonneg_left (show -‖p.2.1‖*‖d‖≤
      terminalValue p.2.1 (s.2+d)-terminalValue p.2.1 s.2 by linarith) s.1.2.1
    have ht := mul_le_mul_of_nonneg_right s.1.2.2 (mul_nonneg (norm_nonneg p.2.1) (norm_nonneg d))
    nlinarith
  have h2 := neg_abs_le (terminalValue p.2.2 (s.2+d)-terminalValue p.2.2 s.2)
  have hb2 := hi p.2.2
  rw [Real.norm_eq_abs] at hb2
  nlinarith

theorem isUnit_compactTiltNormalizer (w : ℝ≥0) (p : CompactTiltParameter) (hp : 0<p.1) :
    IsUnit (compactTiltNormalizer w p) := by
  let f := compactTiltNormalizer w p
  let δ := compactTiltLower w p
  have hd : 0<δ := compactTiltLower_pos w p hp
  have hb : ∀s,δ≤f s := compactTiltLower_le w p hp
  refine ⟨⟨f,inversePositiveBCF f δ hd hb,?_,?_⟩,rfl⟩
  · ext s
    exact mul_inv_cancel₀ (hd.trans_le (hb s)).ne'
  · ext s
    exact inv_mul_cancel₀ (hd.trans_le (hb s)).ne'

theorem fderiv_compactTiltKernel_apply (p : CompactTiltParameter) (hp : 0<p.1)
    (v : CompactTiltParameter) (s : ℝ×CompactTiltLocation) :
    (fderiv ℝ compactTiltKernel p v) s=
      Real.exp (compactTiltLaplaceLinear s p)*compactTiltLaplaceLinear s v := by
  have hk := (analyticAt_compactTiltKernel p hp).differentiableAt.hasFDerivAt
  have heval := ((BoundedContinuousFunction.evalCLM ℝ s).hasFDerivAt).comp p hk
  have he : (fun q=>Real.exp (compactTiltLaplaceLinear s q))=ᶠ[𝓝 p]
      (fun q=>compactTiltKernel q s) := by
    have hloc : ∀ᶠq:CompactTiltParameter in 𝓝 p,0<q.1 :=
      continuous_fst.continuousAt (Ioi_mem_nhds hp)
    exact hloc.mono fun q hq=>(compactTiltKernel_apply q hq s).symm
  have hexp := ((Real.hasDerivAt_exp (compactTiltLaplaceLinear s p)).comp_hasFDerivAt p
    (compactTiltLaplaceLinear s).hasFDerivAt).congr_of_eventuallyEq he.symm
  have hl := heval.unique hexp
  exact congrArg (fun D:CompactTiltParameter→L[ℝ]ℝ=>D v) hl

theorem fderiv_compactTiltNormalizer_apply (w : ℝ≥0) (p : CompactTiltParameter) (hp : 0<p.1)
    (v : CompactTiltParameter) (s : CompactTiltLocation) :
    (fderiv ℝ (compactTiltNormalizer w) p v) s=
      ∫d,Real.exp (compactTiltLaplaceLinear (d,s) p)*compactTiltLaplaceLinear (d,s) v
        ∂gaussianReal 0 w := by
  have hk := (analyticAt_compactTiltKernel p hp).differentiableAt.hasFDerivAt
  have hd := ((parametricGaussianKernelAverageCLM w).hasFDerivAt.comp p hk).fderiv
  change fderiv ℝ (compactTiltNormalizer w) p=
    (parametricGaussianKernelAverageCLM w).comp (fderiv ℝ compactTiltKernel p) at hd
  rw [hd]
  change (∫d,(fderiv ℝ compactTiltKernel p v) (d,s) ∂gaussianReal 0 w)=_
  apply integral_congr_ae
  exact .of_forall fun d=>fderiv_compactTiltKernel_apply p hp v (d,s)

theorem inverse_compactTiltNormalizer_apply (w : ℝ≥0) (p : CompactTiltParameter)
    (hp : 0<p.1) (s : CompactTiltLocation) :
    Ring.inverse (compactTiltNormalizer w p) s=(compactTiltNormalizer w p s)⁻¹ := by
  have hm := Ring.mul_inverse_cancel (compactTiltNormalizer w p) (isUnit_compactTiltNormalizer w p hp)
  have hx := congrArg (fun f:CompactTiltLocation →ᵇ ℝ=>f s) hm
  change compactTiltNormalizer w p s*Ring.inverse (compactTiltNormalizer w p) s=1 at hx
  have hn : compactTiltNormalizer w p s≠0 :=
    (compactTiltLower_pos w p hp |>.trans_le (compactTiltLower_le w p hp s)).ne'
  apply mul_left_cancel₀ hn
  rw [mul_inv_cancel₀ hn]
  exact hx

def compactTiltResponse (w : ℝ≥0) (q : CompactTiltParameter×TerminalSpace) : CompactTiltLocation →ᵇ ℝ :=
  Ring.inverse (compactTiltNormalizer w q.1)*
    (fderiv ℝ (compactTiltNormalizer w) q.1 (0,(0,q.2)))

theorem compactTiltResponse_apply (w : ℝ≥0) (q : CompactTiltParameter×TerminalSpace)
    (hp : 0<q.1.1) (s : CompactTiltLocation) :
    compactTiltResponse w q s=
      (∫d,Real.exp (compactTiltLaplaceLinear (d,s) q.1)*
        (terminalValue q.2 (s.2+d)-terminalValue q.2 s.2) ∂gaussianReal 0 w)/
      (∫d,Real.exp (compactTiltLaplaceLinear (d,s) q.1) ∂gaussianReal 0 w) := by
  change Ring.inverse (compactTiltNormalizer w q.1) s*
    (fderiv ℝ (compactTiltNormalizer w) q.1 (0,(0,q.2))) s=_
  rw [inverse_compactTiltNormalizer_apply w q.1 hp s,
    fderiv_compactTiltNormalizer_apply w q.1 hp,compactTiltNormalizer_apply w q.1 hp]
  simp only [compactTiltLaplaceLinear_apply,terminalValue_zeroDatum,sub_self,mul_zero,
    zero_add,zero_mul,sub_zero]
  ring

theorem contDiffAt_compactTiltResponse (w : ℝ≥0) (q : CompactTiltParameter×TerminalSpace)
    (hp : 0<q.1.1) : ContDiffAt ℝ ⊤ (compactTiltResponse w) q := by
  have hN : AnalyticAt ℝ (compactTiltNormalizer w) q.1 := analyticAt_compactTiltNormalizer w q.1 hp
  have hinv : AnalyticAt ℝ Ring.inverse (compactTiltNormalizer w q.1) := by
    simpa using analyticAt_inverse (𝕜:=ℝ) (IsUnit.unit (isUnit_compactTiltNormalizer w q.1 hp))
  have hNfst : AnalyticAt ℝ (fun r:CompactTiltParameter×TerminalSpace=>
      compactTiltNormalizer w r.1) q :=
    hN.comp (f:=fun r:CompactTiltParameter×TerminalSpace=>r.1) analyticAt_fst
  have hInv : ContDiffAt ℝ ⊤ (fun r:CompactTiltParameter×TerminalSpace=>
      Ring.inverse (compactTiltNormalizer w r.1)) q :=
    (hinv.comp (f:=fun r:CompactTiltParameter×TerminalSpace=>compactTiltNormalizer w r.1) hNfst).contDiffAt
  have hD : ContDiffAt ℝ ⊤ (fderiv ℝ (compactTiltNormalizer w)) q.1 :=
    (hN.contDiffAt (n:=⊤)).fderiv_right (m:=⊤) (by simp)
  have hDR : ContDiffAt ℝ ⊤ (fun r:CompactTiltParameter×TerminalSpace=>
      fderiv ℝ (compactTiltNormalizer w) r.1 (0,(0,r.2))) q :=
    (hD.comp q (show ContDiffAt ℝ ⊤ (fun r:CompactTiltParameter×TerminalSpace=>r.1) q from contDiffAt_fst)).clm_apply
      (show ContDiffAt ℝ ⊤ (fun r:CompactTiltParameter×TerminalSpace=>(0,(0,r.2))) q by fun_prop)
  exact hInv.mul hDR

end GeneralDepthPaper
