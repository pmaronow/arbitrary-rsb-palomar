module

public import DepthPaper.RevisedEntropyTerminal
public import DepthPaper.GaussianTiltedSpatial

@[expose] public section

/-! Exact terminal-direction derivatives of actual Gaussian Cole–Hopf
integrals. All masses and nonnegative variances are included. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ContDiff

namespace DepthPaper
open ColeHopfFoundation.ProbabilityTheory
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

theorem hasDerivAt_revisedTerminalExponentialIntegral
    (a : ℝ) (v : ℝ≥0) (g k : TerminalSpace) (x : ℝ) :
    HasDerivAt (fun t => ∫ z,
      Real.exp (a * (terminalValue g (x + z) + t * terminalValue k (x + z)))
      ∂gaussianReal 0 v)
      (∫ z, a * terminalValue k (x + z) *
        Real.exp (a * terminalValue g (x + z)) ∂gaussianReal 0 v) 0 := by
  let G := terminalValue g
  let K := terminalValue k
  let W : ℝ → ℝ := fun y => |G y| + |K y|
  have hGm : Measurable G := (contDiff_terminalValue g).continuous.measurable
  have hKm : Measurable K := (contDiff_terminalValue k).continuous.measurable
  have hWm : Measurable W := hGm.norm.add hKm.norm
  have hWg : HasLinearGrowth W := by
    refine ⟨‖g‖ + ‖k‖, ‖g‖ + ‖k‖, by positivity, fun y => ?_⟩
    rw [abs_of_nonneg (by dsimp only [W]; positivity)]
    have hg := norm_terminalValue_le g y
    have hk := norm_terminalValue_le k y
    simp only [Real.norm_eq_abs] at hg hk
    dsimp only [W, G, K]
    nlinarith
  have hboundg : HasExpGrowth (fun y => |a| * |K y| * Real.exp (|a| * W y)) :=
    (((hasLinearGrowth_terminalValue k).toHasExpGrowth.abs.const_mul |a|).mul
      (hWg.exp_mul |a|))
  have hboundm : Measurable (fun z =>
      |a| * |K (x + z)| * Real.exp (|a| * W (x + z))) := by
    fun_prop
  have hboundi : Integrable (fun z =>
      |a| * |K (x + z)| * Real.exp (|a| * W (x + z))) (gaussianReal 0 v) :=
    (hboundg.comp_add_const x).integrable_gaussianReal hboundm.aestronglyMeasurable
  have hGi := integrable_exp_mul_comp_add (hasLinearGrowth_terminalValue g) hGm a v x
  have hDm : AEStronglyMeasurable (fun z =>
      a * K (x + z) * Real.exp (a * G (x + z))) (gaussianReal 0 v) := by
    fun_prop
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 v)
    (F := fun t z => Real.exp (a * (G (x + z) + t * K (x + z))))
    (F' := fun t z => a * K (x + z) *
      Real.exp (a * (G (x + z) + t * K (x + z))))
    (bound := fun z => |a| * |K (x + z)| * Real.exp (|a| * W (x + z)))
    (s := Metric.ball (0 : ℝ) 1) (Metric.ball_mem_nhds _ one_pos)
    (Eventually.of_forall fun t => by fun_prop)
    (by simpa only [zero_mul, add_zero] using hGi)
    (by simpa only [zero_mul, add_zero] using hDm) ?_ hboundi ?_).2
  · simpa only [zero_mul, add_zero] using hd
  · exact Eventually.of_forall fun z t ht => by
      have ht1 : |t| ≤ 1 := by
        have hh := Metric.mem_ball.1 ht
        simpa only [Real.dist_eq, sub_zero] using hh.le
      rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_pos (Real.exp_pos _)]
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      calc
        a * (G (x + z) + t * K (x + z))
            ≤ |a| * |G (x + z) + t * K (x + z)| := by
              rw [← abs_mul]; exact le_abs_self _
        _ ≤ |a| * (|G (x + z)| + |t * K (x + z)|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
        _ ≤ |a| * W (x + z) := by
          dsimp only [W]
          rw [abs_mul]
          gcongr
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right ht1 (abs_nonneg (K (x + z)))
  · exact Eventually.of_forall fun z t _ => by
      convert! ((((hasDerivAt_const t (G (x + z))).add
        ((hasDerivAt_id t).mul_const (K (x + z)))).const_mul a).exp) using 1 <;>
        dsimp only [Pi.add_apply, id_eq]
      ring

theorem hasDerivAt_revisedColeHopf_terminal_affine_nonzero
    (a : ℝ) (ha : a ≠ 0) (v : ℝ≥0) (g k : TerminalSpace) (x : ℝ) :
    HasDerivAt (fun t : ℝ => coleHopf a v (terminalValue (g + t • k)) x)
      ((∫ z, terminalValue k (x + z) *
        Real.exp (a * terminalValue g (x + z)) ∂gaussianReal 0 v) /
        (∫ z, Real.exp (a * terminalValue g (x + z)) ∂gaussianReal 0 v)) 0 := by
  have hp := integral_exp_mul_comp_add_pos (hasLinearGrowth_terminalValue g)
    (contDiff_terminalValue g).continuous.measurable a v x
  have hd := ((hasDerivAt_revisedTerminalExponentialIntegral a v g k x).log
    (by simpa only [zero_mul, add_zero] using hp.ne')).const_mul (1 / a)
  simp only [zero_mul, add_zero] at hd
  rw [show (∫ z, a * terminalValue k (x + z) *
      Real.exp (a * terminalValue g (x + z)) ∂gaussianReal 0 v) =
      a * ∫ z, terminalValue k (x + z) *
        Real.exp (a * terminalValue g (x + z)) ∂gaussianReal 0 v by
      simpa only [mul_assoc] using integral_const_mul a
        (fun z => terminalValue k (x + z) * Real.exp (a * terminalValue g (x + z)))] at hd
  have hd' := hd.congr_deriv (show (1 / a) *
      ((a * ∫ z, terminalValue k (x + z) *
        Real.exp (a * terminalValue g (x + z)) ∂gaussianReal 0 v) /
        (∫ z, Real.exp (a * terminalValue g (x + z)) ∂gaussianReal 0 v)) =
      (∫ z, terminalValue k (x + z) *
        Real.exp (a * terminalValue g (x + z)) ∂gaussianReal 0 v) /
        (∫ z, Real.exp (a * terminalValue g (x + z)) ∂gaussianReal 0 v) by
      field_simp)
  apply hd'.congr_of_eventuallyEq
  exact Eventually.of_forall fun t => by
    change coleHopf a v (terminalValue (g + t • k)) x = _
    rw [coleHopf_of_ne ha]
    congr 2
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      change Real.exp (a * terminalValue (g + t • k) (x + z)) = _
      rw [terminalValue_add, terminalValue_smul]

theorem hasDerivAt_revisedColeHopf_terminal_affine_zero
    (v : ℝ≥0) (g k : TerminalSpace) (x : ℝ) :
    HasDerivAt (fun t : ℝ => coleHopf 0 v (terminalValue (g + t • k)) x)
      (∫ z, terminalValue k (x + z) ∂gaussianReal 0 v) 0 := by
  have hi (f : TerminalSpace) : Integrable
      (fun z => terminalValue f (x + z)) (gaussianReal 0 v) :=
    ((hasLinearGrowth_terminalValue f).toHasExpGrowth.comp_add_const x).integrable_gaussianReal
      (((contDiff_terminalValue f).continuous.comp
        (continuous_const.add continuous_id)).aestronglyMeasurable)
  have he (t : ℝ) : coleHopf 0 v (terminalValue (g + t • k)) x =
      (∫ z, terminalValue g (x + z) ∂gaussianReal 0 v) +
        t * (∫ z, terminalValue k (x + z) ∂gaussianReal 0 v) := by
    rw [coleHopf_zero]
    simp_rw [terminalValue_add, terminalValue_smul]
    rw [integral_add (hi g) ((hi k).const_mul t), integral_const_mul]
  have hd := (hasDerivAt_const (0 : ℝ)
      (∫ z, terminalValue g (x + z) ∂gaussianReal 0 v)).add
    ((hasDerivAt_id (0 : ℝ)).mul_const
      (∫ z, terminalValue k (x + z) ∂gaussianReal 0 v))
  simp only [zero_add, one_mul] at hd
  apply hd.congr_of_eventuallyEq
  exact Eventually.of_forall he

theorem hasDerivAt_revisedColeHopf_terminal_affine
    (a : ℝ) (v : ℝ≥0) (g k : TerminalSpace) (x : ℝ) :
    HasDerivAt (fun t : ℝ => coleHopf a v (terminalValue (g + t • k)) x)
      ((∫ z, terminalValue k (x + z) *
        Real.exp (a * terminalValue g (x + z)) ∂gaussianReal 0 v) /
        (∫ z, Real.exp (a * terminalValue g (x + z)) ∂gaussianReal 0 v)) 0 := by
  by_cases ha : a = 0
  · subst a
    simpa only [zero_mul, Real.exp_zero, mul_one, integral_const,
      probReal_univ, one_smul, div_one] using
      hasDerivAt_revisedColeHopf_terminal_affine_zero v g k x
  · exact hasDerivAt_revisedColeHopf_terminal_affine_nonzero a ha v g k x

def revisedColeHopfTerminalDerivative (a V : ℝ) (g k : TerminalSpace) : TerminalSpace :=
  fderiv ℝ (fun h : TerminalSpace => coleHopfTerminal ((a, V), h)) g k

theorem terminalValue_revisedColeHopfTerminalDerivative
    (a V : ℝ) (hV : 0 < V) (g k : TerminalSpace) (x : ℝ) :
    terminalValue (revisedColeHopfTerminalDerivative a V g k) x =
      (∫ z, terminalValue k (x + z) *
        Real.exp (a * terminalValue g (x + z)) ∂gaussianReal 0 V.toNNReal) /
        (∫ z, Real.exp (a * terminalValue g (x + z)) ∂gaussianReal 0 V.toNNReal) := by
  have harg : ContDiffAt ℝ ∞ (fun h : TerminalSpace => ((a, V), h)) g := by fun_prop
  have hf := ((contDiffAt_coleHopfTerminal ((a, V), g) hV).comp g harg).differentiableAt
    (by simp) |>.hasFDerivAt
  have hk : HasDerivAt (fun t : ℝ => g + t • k) k 0 := by
    convert! (hasDerivAt_const (0 : ℝ) g).add ((hasDerivAt_id (0 : ℝ)).smul_const k)
      using 1 <;> simp
  have hf0 : HasFDerivAt (fun h : TerminalSpace => coleHopfTerminal ((a, V), h))
      (fderiv ℝ (fun h : TerminalSpace => coleHopfTerminal ((a, V), h)) g)
      (g + (0 : ℝ) • k) := by
    simpa only [zero_smul, add_zero, Function.comp_def] using hf
  have hd := (terminalEvalCLM x).hasFDerivAt.comp_hasDerivAt 0
    (hf0.comp_hasDerivAt 0 hk)
  have hscalar := hasDerivAt_revisedColeHopf_terminal_affine a V.toNNReal g k x
  have hsame : HasDerivAt
      (fun t : ℝ => terminalValue (coleHopfTerminal ((a, V), g + t • k)) x)
      ((∫ z, terminalValue k (x + z) * Real.exp (a * terminalValue g (x + z))
        ∂gaussianReal 0 V.toNNReal) /
        (∫ z, Real.exp (a * terminalValue g (x + z)) ∂gaussianReal 0 V.toNNReal)) 0 := by
    apply hscalar.congr_of_eventuallyEq
    exact Eventually.of_forall fun t => terminalValue_coleHopfTerminal ((a, V), g + t • k) hV x
  exact hd.unique hsame

end DepthPaper
