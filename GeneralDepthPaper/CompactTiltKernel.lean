module

public import GeneralDepthPaper.TerminalKernel
public import GeneralDepthPaper.ParametricGaussianAverage

@[expose] public section


/-! An analytic kernel uniform in a compact auxiliary tilt. An independent
second terminal direction allows differentiation of its normalizer without
introducing a division by the auxiliary tilt at zero. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 32
abbrev UnitTilt := Icc (0:ℝ) 1
abbrev CompactTiltParameter := ℝ×(TerminalSpace×TerminalSpace)
abbrev CompactTiltLocation := UnitTilt×ℝ

def compactTiltLaplaceLinear (s : ℝ×CompactTiltLocation) : CompactTiltParameter→L[ℝ]ℝ :=
  let inc := terminalEvalCLM (s.2.2+s.1)-terminalEvalCLM s.2.2
  (s.2.1:ℝ) • (inc.comp ((ContinuousLinearMap.fst ℝ TerminalSpace TerminalSpace).comp
    (ContinuousLinearMap.snd ℝ ℝ (TerminalSpace×TerminalSpace))))+
  inc.comp ((ContinuousLinearMap.snd ℝ TerminalSpace TerminalSpace).comp
    (ContinuousLinearMap.snd ℝ ℝ (TerminalSpace×TerminalSpace)))-
  s.1^2 • (ContinuousLinearMap.fst ℝ ℝ (TerminalSpace×TerminalSpace))

@[simp] theorem compactTiltLaplaceLinear_apply (s : ℝ×CompactTiltLocation) (p : CompactTiltParameter) :
    compactTiltLaplaceLinear s p=
      (s.2.1:ℝ)*(terminalValue p.2.1 (s.2.2+s.1)-terminalValue p.2.1 s.2.2)+
      (terminalValue p.2.2 (s.2.2+s.1)-terminalValue p.2.2 s.2.2)-p.1*s.1^2 := by
  change (s.2.1:ℝ)*(terminalValue p.2.1 (s.2.2+s.1)-terminalValue p.2.1 s.2.2)+
    (terminalValue p.2.2 (s.2.2+s.1)-terminalValue p.2.2 s.2.2)-s.1^2*p.1=_
  ring

theorem continuous_compactTiltLaplaceLinear : Continuous compactTiltLaplaceLinear := by
  have hc := lipschitzWith_terminalEvalCLM.continuous
  unfold compactTiltLaplaceLinear
  fun_prop

theorem compactTilt_exponent_le (s : ℝ×CompactTiltLocation) (p : CompactTiltParameter) :
    compactTiltLaplaceLinear s p≤(‖p.2.1‖+‖p.2.2‖)*‖s.1‖-p.1*s.1^2 := by
  rw [compactTiltLaplaceLinear_apply]
  have ht0 : 0≤(s.2.1:ℝ) := s.2.1.2.1
  have ht1 : (s.2.1:ℝ)≤1 := s.2.1.2.2
  have hi (g : TerminalSpace) : terminalValue g (s.2.2+s.1)-terminalValue g s.2.2≤‖g‖*‖s.1‖ := by
    have h := norm_terminalValue_sub_le g s.2.2 (s.2.2+s.1)
    simp only [add_sub_cancel_left] at h
    exact (le_abs_self _).trans (h.trans
      (mul_le_mul_of_nonneg_right (norm_terminalJet_le g 0) (norm_nonneg _)))
  have h1 := mul_le_mul_of_nonneg_left (hi p.2.1) ht0
  have h2 := mul_le_mul_of_nonneg_right ht1 (mul_nonneg (norm_nonneg p.2.1) (norm_nonneg s.1))
  nlinarith [hi p.2.2]

theorem norm_compactTiltLaplaceLinear_le (s : ℝ×CompactTiltLocation) :
    ‖compactTiltLaplaceLinear s‖≤2*‖s.1‖+s.1^2 := by
  apply (compactTiltLaplaceLinear s).opNorm_le_bound (by positivity)
  intro p
  have hp1 : ‖p.2.1‖≤‖p‖ := (norm_fst_le p.2).trans (norm_snd_le p)
  have hp2 : ‖p.2.2‖≤‖p‖ := (norm_snd_le p.2).trans (norm_snd_le p)
  have hpb : ‖p.1‖≤‖p‖ := norm_fst_le p
  have ht : ‖(s.2.1:ℝ)‖≤1 := by rw [Real.norm_of_nonneg s.2.1.2.1]; exact s.2.1.2.2
  have hi (g : TerminalSpace) :
      ‖terminalValue g (s.2.2+s.1)-terminalValue g s.2.2‖≤‖g‖*‖s.1‖ := by
    have h := norm_terminalValue_sub_le g s.2.2 (s.2.2+s.1)
    simp only [add_sub_cancel_left] at h
    exact h.trans (mul_le_mul_of_nonneg_right (norm_terminalJet_le g 0) (norm_nonneg _))
  rw [compactTiltLaplaceLinear_apply]
  calc
    ‖_+_-_‖≤‖(s.2.1:ℝ)*(terminalValue p.2.1 (s.2.2+s.1)-terminalValue p.2.1 s.2.2)‖+
      ‖terminalValue p.2.2 (s.2.2+s.1)-terminalValue p.2.2 s.2.2‖+‖p.1*s.1^2‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _≤1*(‖p‖*‖s.1‖)+(‖p‖*‖s.1‖)+‖p‖*s.1^2 := by
      rw [norm_mul,norm_mul,Real.norm_of_nonneg (sq_nonneg _)]
      exact add_le_add (add_le_add
        (mul_le_mul ht ((hi p.2.1).trans (mul_le_mul_of_nonneg_right hp1 (norm_nonneg _)))
          (norm_nonneg _) zero_le_one)
        ((hi p.2.2).trans (mul_le_mul_of_nonneg_right hp2 (norm_nonneg _))))
        (mul_le_mul_of_nonneg_right hpb (sq_nonneg _))
    _=(2*‖s.1‖+s.1^2)*‖p‖ := by ring

def compactTiltKernel (p : CompactTiltParameter) : (ℝ×CompactTiltLocation) →ᵇ ℝ :=
  boundedExpKernel compactTiltLaplaceLinear (fun _=>1) continuous_compactTiltLaplaceLinear continuous_const p

theorem compactTiltKernel_apply (p : CompactTiltParameter) (hp : 0<p.1) (s : ℝ×CompactTiltLocation) :
    compactTiltKernel p s=Real.exp (compactTiltLaplaceLinear s p) := by
  apply (boundedExpKernel_apply _ _ _ _ p ?_ s).trans (one_mul _)
  refine ⟨Real.exp ((‖p.2.1‖+‖p.2.2‖)^2/(4*p.1)),fun s=>?_⟩
  rw [one_mul,Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr ((compactTilt_exponent_le s p).trans
    (quadratic_exponential_bound p.1 (‖p.2.1‖+‖p.2.2‖) s.1 hp))

theorem analyticAt_compactTiltKernel (p : CompactTiltParameter) (hp : 0<p.1) :
    AnalyticAt ℝ compactTiltKernel p := by
  let r : ℝ≥0 := ⟨p.1/2,by positivity⟩
  have hr : 0<r := by change 0<p.1/2; positivity
  let c : ℝ := ‖p.2.1‖+‖p.2.2‖+2*(r:ℝ)
  let a : ℝ := p.1-(r:ℝ)
  have ha : 0<a := by change 0<p.1-p.1/2; linarith
  apply analyticAt_boundedExpKernel compactTiltLaplaceLinear (fun _=>1)
    continuous_compactTiltLaplaceLinear continuous_const p r hr
    (Real.exp (c^2/(4*a))) (Real.exp_pos _).le
  intro s
  rw [one_mul,Real.norm_of_nonneg (Real.exp_pos _).le,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  calc
    compactTiltLaplaceLinear s p+(r:ℝ)*‖compactTiltLaplaceLinear s‖
      ≤(‖p.2.1‖+‖p.2.2‖)*‖s.1‖-p.1*s.1^2+(r:ℝ)*(2*‖s.1‖+s.1^2) :=
        add_le_add (compactTilt_exponent_le s p)
          (mul_le_mul_of_nonneg_left (norm_compactTiltLaplaceLinear_le s) r.2)
    _=c*‖s.1‖-a*s.1^2 := by dsimp [c,a]; ring
    _≤c^2/(4*a) := quadratic_exponential_bound a c s.1 ha

def compactTiltNormalizer (w : ℝ≥0) (p : CompactTiltParameter) : CompactTiltLocation →ᵇ ℝ :=
  parametricGaussianKernelAverage w (compactTiltKernel p)

theorem analyticAt_compactTiltNormalizer (w : ℝ≥0) (p : CompactTiltParameter) (hp : 0<p.1) :
    AnalyticAt ℝ (compactTiltNormalizer w) p :=
  ((parametricGaussianKernelAverageCLM w).analyticAt _).comp (analyticAt_compactTiltKernel p hp)

end GeneralDepthPaper
