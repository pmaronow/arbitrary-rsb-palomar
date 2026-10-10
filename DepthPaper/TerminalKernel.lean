module

public import DepthPaper.TerminalOperators
public import DepthPaper.AnalyticKernel

@[expose] public section


/-! The genuine centered exponential kernel is analytic in the mass-scaled
terminal datum and positive Gaussian precision, as a bounded function of both
spatial position and Gaussian displacement. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace DepthPaper
set_option maxSynthPendingDepth 32

abbrev TerminalParameter := ℝ×TerminalSpace

def terminalEvalCLM (x : ℝ) : TerminalSpace→L[ℝ]ℝ :=
  LinearMap.mkContinuous
    {toFun:=fun g=>terminalValue g x
     map_add':=fun g h=>terminalValue_add g h x
     map_smul':=fun c g=>by simpa only [RingHom.id_apply,smul_eq_mul] using terminalValue_smul c g x}
    (1+‖x‖) (fun g=>norm_terminalValue_le g x)

@[simp] theorem terminalEvalCLM_apply (x : ℝ) (g : TerminalSpace) :
    terminalEvalCLM x g=terminalValue g x := rfl

theorem lipschitzWith_terminalEvalCLM : LipschitzWith 1 terminalEvalCLM := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm,NNReal.coe_one,one_mul]
  apply (terminalEvalCLM x-terminalEvalCLM y).opNorm_le_bound (norm_nonneg _)
  intro g
  change ‖terminalValue g x-terminalValue g y‖≤‖x-y‖*‖g‖
  exact (norm_terminalValue_sub_le g y x).trans
    ((mul_le_mul_of_nonneg_right (norm_terminalJet_le g 0) (norm_nonneg _)).trans_eq (mul_comm _ _))

def terminalLaplaceLinear (p : ℝ×ℝ) : TerminalParameter→L[ℝ]ℝ :=
  ((terminalEvalCLM (p.2+p.1)-terminalEvalCLM p.2).comp
      (ContinuousLinearMap.snd ℝ ℝ TerminalSpace))-
    (p.1^2) • (ContinuousLinearMap.fst ℝ ℝ TerminalSpace)

@[simp] theorem terminalLaplaceLinear_apply (d x : ℝ) (p : TerminalParameter) :
    terminalLaplaceLinear (d,x) p=terminalValue p.2 (x+d)-terminalValue p.2 x-p.1*d^2 := by
  change (terminalValue p.2 (x+d)-terminalValue p.2 x)-d^2*p.1=_
  ring

theorem continuous_terminalLaplaceLinear : Continuous terminalLaplaceLinear := by
  have hc := lipschitzWith_terminalEvalCLM.continuous
  unfold terminalLaplaceLinear
  fun_prop

theorem norm_terminalLaplaceLinear_le (d x : ℝ) :
    ‖terminalLaplaceLinear (d,x)‖≤‖d‖+d^2 := by
  apply (terminalLaplaceLinear (d,x)).opNorm_le_bound (by positivity)
  intro p
  rw [terminalLaplaceLinear_apply]
  have hg : ‖p.2‖≤‖p‖ := norm_snd_le p
  have hb : ‖p.1‖≤‖p‖ := norm_fst_le p
  have hi := norm_terminalValue_sub_le p.2 x (x+d)
  simp only [add_sub_cancel_left] at hi
  calc
    ‖terminalValue p.2 (x+d)-terminalValue p.2 x-p.1*d^2‖
      ≤‖terminalValue p.2 (x+d)-terminalValue p.2 x‖+‖p.1*d^2‖ := norm_sub_le _ _
    _≤‖d‖*‖p.2‖+‖p.1‖*d^2 := by
      rw [norm_mul,Real.norm_of_nonneg (sq_nonneg _)]
      exact add_le_add (hi.trans ((mul_le_mul_of_nonneg_right (norm_terminalJet_le p.2 0)
        (norm_nonneg _)).trans_eq (mul_comm _ _))) le_rfl
    _≤‖d‖*‖p‖+‖p‖*d^2 := by gcongr
    _=(‖d‖+d^2)*‖p‖ := by ring

def weightedTerminalKernel (p : TerminalParameter) : (ℝ×ℝ) →ᵇ ℝ :=
  boundedExpKernel terminalLaplaceLinear (fun _=>1) continuous_terminalLaplaceLinear continuous_const p

theorem quadratic_exponential_bound (a c d : ℝ) (ha : 0<a) :
    c*‖d‖-a*d^2≤c^2/(4*a) := by
  apply (le_div_iff₀ (by positivity)).mpr
  have hd : ‖d‖^2=d^2 := by simp only [Real.norm_eq_abs,sq_abs]
  have hs := sq_nonneg (2*a*‖d‖-c)
  have he : (2*a*‖d‖-c)^2=4*a^2*d^2-4*a*c*‖d‖+c^2 := by
    rw [←hd]
    ring
  rw [he] at hs
  nlinarith

theorem weightedTerminalKernel_apply (p : TerminalParameter) (hp : 0<p.1) (d x : ℝ) :
    weightedTerminalKernel p (d,x)=
      Real.exp (terminalValue p.2 (x+d)-terminalValue p.2 x-p.1*d^2) := by
  apply (boundedExpKernel_apply terminalLaplaceLinear (fun _=>1)
    continuous_terminalLaplaceLinear continuous_const p ?_ (d,x)).trans
  · simp only [one_mul,terminalLaplaceLinear_apply]
  · refine ⟨Real.exp (‖p.2‖^2/(4*p.1)),fun s=>?_⟩
    rw [one_mul,Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    rw [terminalLaplaceLinear_apply]
    have hd := norm_terminalValue_sub_le p.2 s.2 (s.2+s.1)
    simp only [add_sub_cancel_left] at hd
    have hi : terminalValue p.2 (s.2+s.1)-terminalValue p.2 s.2≤‖p.2‖*‖s.1‖ :=
      (le_abs_self _).trans (hd.trans (mul_le_mul_of_nonneg_right (norm_terminalJet_le p.2 0)
        (norm_nonneg _)))
    exact (sub_le_sub_right hi _).trans (quadratic_exponential_bound p.1 ‖p.2‖ s.1 hp)

theorem analyticAt_weightedTerminalKernel (p : TerminalParameter) (hp : 0<p.1) :
    AnalyticAt ℝ weightedTerminalKernel p := by
  let r : ℝ≥0 := ⟨p.1/2,by positivity⟩
  have hr : 0<r := by change 0<p.1/2; positivity
  let c : ℝ := ‖p.2‖+(r:ℝ)
  let a : ℝ := p.1-(r:ℝ)
  have ha : 0<a := by change 0<p.1-p.1/2; linarith
  apply analyticAt_boundedExpKernel terminalLaplaceLinear (fun _=>1)
    continuous_terminalLaplaceLinear continuous_const p r hr (Real.exp (c^2/(4*a))) (Real.exp_pos _).le
  intro s
  rw [one_mul,Real.norm_of_nonneg (Real.exp_pos _).le,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hL := norm_terminalLaplaceLinear_le s.1 s.2
  have hg := norm_terminalValue_sub_le p.2 s.2 (s.2+s.1)
  simp only [add_sub_cancel_left] at hg
  rw [terminalLaplaceLinear_apply]
  have hi : terminalValue p.2 (s.2+s.1)-terminalValue p.2 s.2≤‖p.2‖*‖s.1‖ :=
    (le_abs_self _).trans (hg.trans (mul_le_mul_of_nonneg_right (norm_terminalJet_le p.2 0)
      (norm_nonneg _)))
  calc
    terminalValue p.2 (s.2+s.1)-terminalValue p.2 s.2-p.1*s.1^2+
        (r:ℝ)*‖terminalLaplaceLinear s‖
      ≤‖p.2‖*‖s.1‖-p.1*s.1^2+(r:ℝ)*(‖s.1‖+s.1^2) := by gcongr
    _=c*‖s.1‖-a*s.1^2 := by dsimp [c,a]; ring
    _≤c^2/(4*a) := quadratic_exponential_bound a c s.1 ha

end DepthPaper
