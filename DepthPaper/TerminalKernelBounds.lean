module

public import DepthPaper.AnalyticKernelBounds
public import DepthPaper.CompactTiltKernel
public import DepthPaper.GaussianKernelOperator
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public section


/-! Uniform, explicit all-order bounds for the actual centered Gaussian
exponential kernels. The terminal ball is not assumed compact. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff
namespace DepthPaper
set_option maxSynthPendingDepth 64

theorem norm_iteratedFDeriv_weightedTerminalKernel_le
    (ρ B : ℝ) (hρ : 0<ρ) (p : TerminalParameter)
    (hp : ρ≤p.1) (hg : ‖p.2‖≤B) (n : ℕ) :
    ‖iteratedFDeriv ℝ n weightedTerminalKernel p‖ ≤
      (n.factorial:ℝ)*Real.exp ((B+ρ/2)^2/(2*ρ))/(ρ/2)^n := by
  let r : ℝ≥0 := ⟨ρ/2,by positivity⟩
  have hr : 0<r := by change 0<ρ/2; positivity
  apply norm_iteratedFDeriv_boundedExpKernel_le terminalLaplaceLinear (fun _=>1)
    continuous_terminalLaplaceLinear continuous_const p r hr _ (Real.exp_pos _).le
  intro s
  rw [one_mul,Real.norm_of_nonneg (Real.exp_pos _).le,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hi := norm_terminalValue_sub_le p.2 s.2 (s.2+s.1)
  simp only [add_sub_cancel_left] at hi
  have hinc : terminalValue p.2 (s.2+s.1)-terminalValue p.2 s.2≤B*‖s.1‖ :=
    (le_abs_self _).trans (hi.trans ((mul_le_mul_of_nonneg_right
      ((norm_terminalJet_le p.2 0).trans hg) (norm_nonneg _))))
  rw [terminalLaplaceLinear_apply]
  calc
    terminalValue p.2 (s.2+s.1)-terminalValue p.2 s.2-p.1*s.1^2+
        (r:ℝ)*‖terminalLaplaceLinear s‖
      ≤B*‖s.1‖-ρ*s.1^2+(r:ℝ)*(‖s.1‖+s.1^2) := by
        have hL := norm_terminalLaplaceLinear_le s.1 s.2
        gcongr
    _=(B+ρ/2)*‖s.1‖-(ρ/2)*s.1^2 := by
      have hrval : (r:ℝ)=ρ/2 := rfl
      rw [hrval]
      ring
    _≤(B+ρ/2)^2/(2*ρ) := by
      convert quadratic_exponential_bound (ρ/2) (B+ρ/2) s.1 (by positivity) using 1 <;> ring

theorem norm_iteratedFDeriv_compactTiltKernel_le
    (ρ B : ℝ) (hρ : 0<ρ) (p : CompactTiltParameter)
    (hp : ρ≤p.1) (hg : ‖p.2.1‖+‖p.2.2‖≤B) (n : ℕ) :
    ‖iteratedFDeriv ℝ n compactTiltKernel p‖ ≤
      (n.factorial:ℝ)*Real.exp ((B+ρ)^2/(2*ρ))/(ρ/2)^n := by
  let r : ℝ≥0 := ⟨ρ/2,by positivity⟩
  have hr : 0<r := by change 0<ρ/2; positivity
  apply norm_iteratedFDeriv_boundedExpKernel_le compactTiltLaplaceLinear (fun _=>1)
    continuous_compactTiltLaplaceLinear continuous_const p r hr _ (Real.exp_pos _).le
  intro s
  rw [one_mul,Real.norm_of_nonneg (Real.exp_pos _).le,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  calc
    compactTiltLaplaceLinear s p+(r:ℝ)*‖compactTiltLaplaceLinear s‖
      ≤B*‖s.1‖-ρ*s.1^2+(r:ℝ)*(2*‖s.1‖+s.1^2) := by
        have he := compactTilt_exponent_le s p
        have hL := norm_compactTiltLaplaceLinear_le s
        exact add_le_add (he.trans (by gcongr)) (by gcongr)
    _=(B+ρ)*‖s.1‖-(ρ/2)*s.1^2 := by
      have hrval : (r:ℝ)=ρ/2 := rfl
      rw [hrval]
      ring
    _≤(B+ρ)^2/(2*ρ) := by
      convert quadratic_exponential_bound (ρ/2) (B+ρ) s.1 (by positivity) using 1 <;> ring

theorem norm_iteratedFDeriv_centeredKernelNormalizer_le
    (v : ℝ≥0) (ρ B : ℝ) (hρ : 0<ρ) (p : TerminalParameter)
    (hp : ρ≤p.1) (hg : ‖p.2‖≤B) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (centeredKernelNormalizer v) p‖ ≤
      (n.factorial:ℝ)*Real.exp ((B+ρ/2)^2/(2*ρ))/(ρ/2)^n := by
  have h := (gaussianKernelAverageCLM v).norm_iteratedFDeriv_comp_left
    ((analyticAt_weightedTerminalKernel p (hρ.trans_le hp)).contDiffAt (n:=⊤))
    (show (n:ℕ∞ω)≤⊤ from le_top)
  change ‖iteratedFDeriv ℝ n (centeredKernelNormalizer v) p‖≤_ at h
  exact h.trans ((mul_le_mul_of_nonneg_right (norm_gaussianKernelAverageCLM_le v)
    (norm_nonneg _)).trans (by simpa only [one_mul] using
      norm_iteratedFDeriv_weightedTerminalKernel_le ρ B hρ p hp hg n))

theorem norm_iteratedFDeriv_compactTiltNormalizer_le
    (v : ℝ≥0) (ρ B : ℝ) (hρ : 0<ρ) (p : CompactTiltParameter)
    (hp : ρ≤p.1) (hg : ‖p.2.1‖+‖p.2.2‖≤B) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (compactTiltNormalizer v) p‖ ≤
      (n.factorial:ℝ)*Real.exp ((B+ρ)^2/(2*ρ))/(ρ/2)^n := by
  have h := (parametricGaussianKernelAverageCLM v).norm_iteratedFDeriv_comp_left
    ((analyticAt_compactTiltKernel p (hρ.trans_le hp)).contDiffAt (n:=⊤))
    (show (n:ℕ∞ω)≤⊤ from le_top)
  change ‖iteratedFDeriv ℝ n (compactTiltNormalizer v) p‖≤_ at h
  exact h.trans ((mul_le_mul_of_nonneg_right (norm_parametricGaussianKernelAverageCLM_le v)
    (norm_nonneg _)).trans (by simpa only [one_mul] using
      norm_iteratedFDeriv_compactTiltKernel_le ρ B hρ p hp hg n))

end DepthPaper
