module

public import GeneralDepthPaper.TerminalSpace
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Common.Mathlib.Probability.Distributions.Gaussian.ExpGrowth

@[expose] public section


/-! Actual reconstructed terminal functions and their bounded centered
increment operators. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 32
open ColeHopfFoundation.ProbabilityTheory

theorem contDiff_terminalValue (g : TerminalSpace) : ContDiff ℝ 3 (terminalValue g) := by
  have h2 : ContDiff ℝ 1 (terminalJet g 1) := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun x=>(hasDerivAt_terminalJet_one g x).differentiableAt,?_⟩
    have he : deriv (terminalJet g 1)=terminalJet g 2 :=
      funext (fun x=>(hasDerivAt_terminalJet_one g x).deriv)
    rw [he]
    exact (terminalJet g 2).continuous
  have h1 : ContDiff ℝ 2 (terminalJet g 0) := by
    change ContDiff ℝ ((1:ℕ∞ω)+1) _
    rw [contDiff_succ_iff_deriv]
    refine ⟨fun x=>(hasDerivAt_terminalJet_zero g x).differentiableAt,by simp,?_⟩
    have he : deriv (terminalJet g 0)=terminalJet g 1 :=
      funext (fun x=>(hasDerivAt_terminalJet_zero g x).deriv)
    simpa only [he] using h2
  change ContDiff ℝ ((2:ℕ∞ω)+1) _
  rw [contDiff_succ_iff_deriv]
  refine ⟨fun x=>(hasDerivAt_terminalValue g x).differentiableAt,by simp,?_⟩
  have he : deriv (terminalValue g)=terminalJet g 0 :=
    funext (fun x=>(hasDerivAt_terminalValue g x).deriv)
  simpa only [he] using h1

theorem lipschitzWith_terminalValue (g : TerminalSpace) :
    LipschitzWith ‖terminalJet g 0‖₊ (terminalValue g) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun x=>(hasDerivAt_terminalValue g x).differentiableAt)
  intro x
  rw [(hasDerivAt_terminalValue g x).deriv]
  exact BoundedContinuousFunction.nnnorm_coe_le_nnnorm _ _

theorem norm_terminalValue_sub_le (g : TerminalSpace) (x y : ℝ) :
    ‖terminalValue g y-terminalValue g x‖≤‖terminalJet g 0‖*‖y-x‖ := by
  simpa only [dist_eq_norm,coe_nnnorm] using (lipschitzWith_terminalValue g).dist_le_mul y x

theorem hasLinearGrowth_terminalValue (g : TerminalSpace) : HasLinearGrowth (terminalValue g) := by
  apply HasLinearGrowth.of_lipschitz (L:=‖terminalJet g 0‖)
  intro x y
  exact norm_terminalValue_sub_le g x y

theorem norm_terminalJet_le (g : TerminalSpace) (i : Fin 3) : ‖terminalJet g i‖≤‖g‖ :=
  (norm_le_pi_norm g.1.2 i).trans (norm_snd_le g.1)

def terminalSumNorm (g : TerminalSpace) : ℝ := ‖g.1.1‖+∑i : Fin 3,‖terminalJet g i‖

theorem terminalSumNorm_le_four_norm (g : TerminalSpace) : terminalSumNorm g≤4*‖g‖ := by
  have h0 : ‖g.1.1‖≤‖g‖ := norm_fst_le g.1
  have hi (i : Fin 3) : ‖terminalJet g i‖≤‖g‖ := norm_terminalJet_le g i
  have hs := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ:Finset (Fin 3)))=>hi i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  norm_num at hs
  change (∑i:Fin 3,‖terminalJet g i‖)≤3*‖g‖ at hs
  unfold terminalSumNorm
  linarith

theorem norm_terminalValue_le (g : TerminalSpace) (x : ℝ) :
    ‖terminalValue g x‖≤(1+‖x‖)*‖g‖ := by
  have h0 : ‖terminalValue g 0‖≤‖g‖ := by
    rw [terminalValue_zero]; exact norm_fst_le g.1
  have hd := norm_terminalValue_sub_le g 0 x
  rw [sub_zero] at hd
  calc
    ‖terminalValue g x‖≤‖terminalValue g x-terminalValue g 0‖+‖terminalValue g 0‖ :=
      by simpa only [sub_add_cancel] using
        norm_add_le (terminalValue g x-terminalValue g 0) (terminalValue g 0)
    _≤‖terminalJet g 0‖*‖x‖+‖g‖ := add_le_add hd h0
    _≤‖g‖*‖x‖+‖g‖ := by gcongr; exact norm_terminalJet_le g 0
    _=(1+‖x‖)*‖g‖ := by ring

def terminalIncrement (d : ℝ) (g : TerminalSpace) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x=>terminalValue g (x+d)-terminalValue g x)
    (((contDiff_terminalValue g).continuous.comp (continuous_id.add continuous_const)).sub
      (contDiff_terminalValue g).continuous) (‖d‖*‖g‖) (fun x=>by
        have h := norm_terminalValue_sub_le g x (x+d)
        simp only [add_sub_cancel_left] at h
        exact h.trans ((mul_le_mul_of_nonneg_right (norm_terminalJet_le g 0)
          (norm_nonneg d)).trans_eq (mul_comm _ _)))

@[simp] theorem terminalIncrement_apply (d : ℝ) (g : TerminalSpace) (x : ℝ) :
    terminalIncrement d g x=terminalValue g (x+d)-terminalValue g x := rfl

theorem norm_terminalIncrement_le (d : ℝ) (g : TerminalSpace) :
    ‖terminalIncrement d g‖≤‖d‖*‖g‖ := by
  apply (BoundedContinuousFunction.norm_le (f:=terminalIncrement d g)
    (C:=‖d‖*‖g‖) (mul_nonneg (norm_nonneg d) (norm_nonneg g))).mpr
  intro x
  rw [terminalIncrement_apply]
  have h := norm_terminalValue_sub_le g x (x+d)
  simp only [add_sub_cancel_left] at h
  exact h.trans ((mul_le_mul_of_nonneg_right (norm_terminalJet_le g 0)
    (norm_nonneg d)).trans_eq (mul_comm _ _))

@[simp] theorem terminalValue_add (g h : TerminalSpace) (x : ℝ) :
    terminalValue (g+h) x=terminalValue g x+terminalValue h x := by
  change (g.1.1+h.1.1)+(∫y in (0:ℝ)..x,terminalJet g 0 y+terminalJet h 0 y)=_
  rw [intervalIntegral.integral_add ((terminalJet g 0).continuous.intervalIntegrable _ _)
    ((terminalJet h 0).continuous.intervalIntegrable _ _)]
  unfold terminalValue terminalJet
  ring

@[simp] theorem terminalValue_smul (c : ℝ) (g : TerminalSpace) (x : ℝ) :
    terminalValue (c•g) x=c*terminalValue g x := by
  change c*g.1.1+(∫y in (0:ℝ)..x,c*terminalJet g 0 y)=_
  rw [intervalIntegral.integral_const_mul]
  unfold terminalValue terminalJet
  ring

def terminalIncrementCLM (d : ℝ) : TerminalSpace→L[ℝ](ℝ →ᵇ ℝ) :=
  LinearMap.mkContinuous
    {toFun:=terminalIncrement d
     map_add':=fun g h=>by ext x; simp only [terminalIncrement_apply,terminalValue_add,
       BoundedContinuousFunction.add_apply]; ring
     map_smul':=fun c g=>by ext x; simp only [terminalIncrement_apply,terminalValue_smul,
       BoundedContinuousFunction.smul_apply,RingHom.id_apply,smul_eq_mul]; ring}
    ‖d‖ (norm_terminalIncrement_le d)

@[simp] theorem terminalIncrementCLM_apply (d : ℝ) (g : TerminalSpace) :
    terminalIncrementCLM d g=terminalIncrement d g := rfl

theorem norm_terminalIncrementCLM_le (d : ℝ) : ‖terminalIncrementCLM d‖≤‖d‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

theorem lipschitzWith_terminalIncrementCLM : LipschitzWith 1 terminalIncrementCLM := by
  apply LipschitzWith.of_dist_le_mul
  intro d e
  simp only [dist_eq_norm,NNReal.coe_one,one_mul]
  apply (terminalIncrementCLM d-terminalIncrementCLM e).opNorm_le_bound (norm_nonneg _)
  intro g
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro x
  change ‖(terminalValue g (x+d)-terminalValue g x)-
    (terminalValue g (x+e)-terminalValue g x)‖≤_
  rw [sub_sub_sub_cancel_right]
  have h := norm_terminalValue_sub_le g (x+e) (x+d)
  simp only [add_sub_add_left_eq_sub] at h
  exact h.trans ((mul_le_mul_of_nonneg_right (norm_terminalJet_le g 0)
    (norm_nonneg (d-e))).trans_eq (mul_comm _ _))

end GeneralDepthPaper
