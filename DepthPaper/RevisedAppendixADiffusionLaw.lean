module

public import DepthPaper.ColeHopfClosedVariance
public import FourPapersCommon.ClockedAdditiveState
public import FRSB.BackwardHeatTest
public import FRSB.ConstantMassBackwardKernel
public import FRSB.ConditionalKernelLaw

@[expose] public section

/-! Appendix A.1(iii): the endpoint law of the actual pathwise additive
Brownian diffusion for an arbitrary terminal datum.  The transition law is
derived by bounded backward Fourier tests, rather than supplied as a premise.
Zero mass and zero variance are included. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper StochasticCalculus
open scoped Topology NNReal BoundedContinuousFunction
namespace DepthPaper
open ColeHopfFoundation ColeHopfFoundation.ProbabilityTheory FourPapersCommon FRSB

theorem revised_terminal_oneLipschitz_iff (g : TerminalSpace) :
    LipschitzWith 1 (terminalValue g) ↔ ‖terminalJet g 0‖ ≤ 1 := by
  constructor
  · intro hg
    apply (BoundedContinuousFunction.norm_le (by norm_num)).mpr
    intro x
    rw [←(hasDerivAt_terminalValue g x).deriv]
    exact norm_deriv_le_of_lipschitz hg
  · intro hg
    exact (lipschitzWith_terminalValue g).weaken (by exact_mod_cast hg)

def revisedTerminalHeatWeight (a : ℝ) (g : TerminalSpace) (x : ℝ) : ℝ :=
  Real.exp (a * terminalValue g x)

theorem hasDerivAt_revisedTerminalHeatWeight (a : ℝ) (g : TerminalSpace) (x : ℝ) :
    HasDerivAt (revisedTerminalHeatWeight a g)
      (revisedTerminalHeatWeight a g x * (a * terminalJet g 0 x)) x :=
  ((hasDerivAt_terminalValue g x).const_mul a).exp

theorem heatC2Datum_revisedTerminalHeatWeight (a : ℝ) (g : TerminalSpace) :
    HeatC2Datum (revisedTerminalHeatWeight a g) := by
  have hD := (hasLinearGrowth_terminalValue g).exp_mul a
  change HasExpGrowth (revisedTerminalHeatWeight a g) at hD
  have h0 : HasExpGrowth (fun x => terminalJet g 0 x) :=
    HasExpGrowth.of_bounded (fun x => by
      simpa only [Real.norm_eq_abs] using BoundedContinuousFunction.norm_coe_le_norm (terminalJet g 0) x)
  have h1 : HasExpGrowth (fun x => terminalJet g 1 x) :=
    HasExpGrowth.of_bounded (fun x => by
      simpa only [Real.norm_eq_abs] using BoundedContinuousFunction.norm_coe_le_norm (terminalJet g 1) x)
  have hd : deriv (revisedTerminalHeatWeight a g) =
      fun x => revisedTerminalHeatWeight a g x * (a * terminalJet g 0 x) :=
    funext (fun x => (hasDerivAt_revisedTerminalHeatWeight a g x).deriv)
  have hd2 : iteratedDeriv 2 (revisedTerminalHeatWeight a g) =
      fun x => revisedTerminalHeatWeight a g x *
        ((a * terminalJet g 0 x)^2 + a * terminalJet g 1 x) := by
    rw [iteratedDeriv_succ,iteratedDeriv_one,hd]
    funext x
    change deriv (revisedTerminalHeatWeight a g * (fun y => a * terminalJet g 0 y)) x = _
    rw [((hasDerivAt_revisedTerminalHeatWeight a g x).mul
      ((hasDerivAt_terminalJet_zero g x).const_mul a)).deriv]
    ring
  refine ⟨((contDiff_const.mul (contDiff_terminalValue g)).exp).of_le (by norm_num),?_⟩
  intro j hj
  interval_cases j
  · simpa only [iteratedDeriv_zero] using hD
  · simpa only [iteratedDeriv_one,hd] using hD.mul (h0.const_mul a)
  · rw [hd2]
    simpa only [pow_two] using hD.mul (((h0.const_mul a).mul (h0.const_mul a)).add (h1.const_mul a))

theorem gaussianHeatFlow_revisedTerminalHeatWeight_pos (a : ℝ) (g : TerminalSpace) (v x : ℝ) :
    0 < gaussianHeatFlow (revisedTerminalHeatWeight a g) v x :=
  integral_exp_mul_comp_add_pos (hasLinearGrowth_terminalValue g)
    (contDiff_terminalValue g).continuous.measurable a v.toNNReal x

theorem gaussianHeatFlow_revisedTerminalHeatWeight_log_gradient
    (a : ℝ) (g : TerminalSpace) {v : ℝ} (hv : 0 ≤ v) (x : ℝ) :
    gaussianHeatFlow (deriv (revisedTerminalHeatWeight a g)) v x /
      gaussianHeatFlow (revisedTerminalHeatWeight a g) v x =
        a * terminalJet (coleHopfTerminal ((a,v),g)) 0 x := by
  have hd := hasDerivAt_gaussianHeatFlow_spatial (heatC2Datum_revisedTerminalHeatWeight a g) v x
  have he : gaussianHeatFlow (revisedTerminalHeatWeight a g) v =
      fun y => Real.exp (a * terminalValue (coleHopfTerminal ((a,v),g)) y) := by
    funext y
    rw [terminalValue_coleHopfTerminal_nonneg _ hv]
    change gaussianHeatFlow (fun y => Real.exp (a * terminalValue g y)) v y = _
    exact (by simpa only [Real.coe_toNNReal v hv] using
      (gaussianHeatFlow_exp_eq_exp_coleHopf a v.toNNReal (terminalValue g)
        (hasLinearGrowth_terminalValue g) (contDiff_terminalValue g).continuous.measurable y))
  rw [he] at hd
  have hd' := ((hasDerivAt_terminalValue (coleHopfTerminal ((a,v),g)) x).const_mul a).exp
  rw [hd.unique hd',he]
  exact mul_div_cancel_left₀ _ (Real.exp_pos _).ne'

def revisedDiffusionVariance (T : ℝ≥0) (s : ℝ) : ℝ := max 0 ((T : ℝ) - max 0 s)

theorem revisedDiffusionVariance_mem (T : ℝ≥0) (s : ℝ) :
    revisedDiffusionVariance T s ∈ Icc (0 : ℝ) T := by
  exact ⟨le_max_left _ _,max_le T.coe_nonneg (by linarith [le_max_left (0 : ℝ) s])⟩

theorem revisedDiffusionVariance_of_mem (T : ℝ≥0) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    revisedDiffusionVariance T s = T-s := by
  simp only [revisedDiffusionVariance,max_eq_right hs.1,max_eq_right (sub_nonneg.mpr hs.2)]

theorem revisedDiffusionGradientLip_exists (a : ℝ) (T : ℝ≥0) (g : TerminalSpace) :
    ∃ C : ℝ≥0, ∀ v ∈ Icc (0 : ℝ) T,
      ‖terminalJet (coleHopfTerminal ((a,v),g)) 1‖ ≤ C := by
  have hc : Continuous (fun v : ℝ => terminalJet (coleHopfTerminal ((a,v),g)) 1) :=
    (terminalJetCLM 1).continuous.comp (continuous_coleHopfTerminal.comp (by fun_prop))
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  exact ⟨(max B 0).toNNReal,fun v hv => by
    rw [Real.coe_toNNReal _ (le_max_right _ _)]
    exact (hB v hv).trans (le_max_left _ _)⟩

def revisedDiffusionDriftData (a : ℝ) (T : ℝ≥0) (g : TerminalSpace)
    (hg : ‖terminalJet g 0‖ ≤ 1) : AdditiveDriftData where
  coefficient := fun _ => a
  gradient := fun s x => terminalJet (coleHopfTerminal ((a,revisedDiffusionVariance T s),g)) 0 x
  radius := ‖a‖₊
  gradientLip := (revisedDiffusionGradientLip_exists a T g).choose
  coefficient_measurable := measurable_const
  coefficient_bound := fun _ => le_rfl
  gradient_continuous := by
    have hc : Continuous (fun p : ℝ × ℝ =>
        terminalJet (coleHopfTerminal ((a,revisedDiffusionVariance T p.1),g)) 0) :=
      (terminalJetCLM 0).continuous.comp
        (continuous_coleHopfTerminal.comp (by unfold revisedDiffusionVariance; fun_prop))
    exact continuous_eval.comp (hc.prodMk continuous_snd)
  gradient_bound := fun s x =>
    (BoundedContinuousFunction.norm_coe_le_norm _ x).trans
      ((norm_terminalJet_coleHopfTerminal_nonneg _ (revisedDiffusionVariance_mem T s).1).trans hg)
  gradient_lipschitz := by
    intro s
    apply lipschitzWith_of_nnnorm_deriv_le
      (fun x => (hasDerivAt_terminalJet_zero _ x).differentiableAt)
    intro x
    apply NNReal.coe_le_coe.mp
    rw [coe_nnnorm,(hasDerivAt_terminalJet_zero _ x).deriv]
    exact (BoundedContinuousFunction.norm_coe_le_norm _ x).trans
      ((revisedDiffusionGradientLip_exists a T g).choose_spec _ (revisedDiffusionVariance_mem T s))

def revisedUnitRate : NonnegativeRate := ⟨fun _ => 1,continuous_const,fun _ => zero_le_one⟩

@[simp] theorem rateClock_revisedUnitRate (t : ℝ≥0) : rateClock revisedUnitRate t = t := by
  apply Subtype.ext
  simp [rateClock,rateClockReal,revisedUnitRate]

theorem filtration_revisedUnitRate :
    timeChangedBrownianFiltration (rateClock revisedUnitRate) (monotone_rateClock revisedUnitRate) =
      canonicalBrownianFiltration := by
  have hclock : rateClock revisedUnitRate = id := funext rateClock_revisedUnitRate
  simp only [hclock]
  rfl

def revisedColeHopfDiffusion (a : ℝ) (T : ℝ≥0) (g : TerminalSpace)
    (hg : ‖terminalJet g 0‖ ≤ 1) (x : ℝ) : ℝ≥0 → BrownianSample → ℝ :=
  clockedItoState (revisedDiffusionDriftData a T g hg) revisedUnitRate x T T.coe_nonneg

theorem stronglyAdapted_revisedColeHopfDiffusion (a : ℝ) (T : ℝ≥0) (g : TerminalSpace)
    (hg : ‖terminalJet g 0‖ ≤ 1) (x : ℝ) :
    StronglyAdapted canonicalBrownianFiltration (revisedColeHopfDiffusion a T g hg x) := by
  have he := stronglyAdapted_clockedItoState (revisedDiffusionDriftData a T g hg)
    revisedUnitRate x T T.coe_nonneg
  rw [filtration_revisedUnitRate] at he
  exact he

@[simp] theorem revisedColeHopfDiffusion_zero (a : ℝ) (T : ℝ≥0) (g : TerminalSpace)
    (hg : ‖terminalJet g 0‖ ≤ 1) (x : ℝ) (ω : BrownianSample) :
    revisedColeHopfDiffusion a T g hg x 0 ω = x :=
  clockedItoState_zero _ _ _ _ _ _

theorem revisedColeHopfDiffusion_integral_equation (a : ℝ) (T : ℝ≥0) (g : TerminalSpace)
    (hg : ‖terminalJet g 0‖ ≤ 1) (x : ℝ) (ω : BrownianSample) (t : ℝ≥0) (ht : t ≤ T) :
    revisedColeHopfDiffusion a T g hg x t ω = x+canonicalBrownian t ω+
      ∫ s in 0..(t : ℝ), a * terminalJet (coleHopfTerminal ((a,(T:ℝ)-s),g)) 0
        (revisedColeHopfDiffusion a T g hg x s.toNNReal ω) := by
  unfold revisedColeHopfDiffusion
  rw [clockedItoState_eq _ _ _ _ _ (t := t) (NNReal.coe_le_coe.mpr ht),
    clockedStateReal_integral_equation _ _ _ _ _ _ ⟨t.coe_nonneg,NNReal.coe_le_coe.mpr ht⟩]
  simp only [rateNoiseReal,timeChangedBrownian,rateClock_revisedUnitRate,Real.toNNReal_coe]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le t.coe_nonneg] at hs
  have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1,hs.2.trans (NNReal.coe_le_coe.mpr ht)⟩
  simp only [revisedDiffusionDriftData,revisedDiffusionVariance_of_mem T hsT]
  rw [clockedItoState_eq _ _ _ _ _
    (by simpa only [Real.coe_toNNReal s hs.1] using hsT.2)]
  simp only [Real.coe_toNNReal s hs.1]

theorem abs_deriv_revisedTerminalHeatWeight_le (a : ℝ) (g : TerminalSpace)
    (hg : ‖terminalJet g 0‖ ≤ 1) (x : ℝ) :
    |deriv (revisedTerminalHeatWeight a g) x| ≤ |a| * revisedTerminalHeatWeight a g x := by
  rw [(hasDerivAt_revisedTerminalHeatWeight a g x).deriv,abs_mul,abs_mul,
    abs_of_pos (show 0 < revisedTerminalHeatWeight a g x from Real.exp_pos _) ]
  have hj : |terminalJet g 0 x| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using (BoundedContinuousFunction.norm_coe_le_norm _ x).trans hg
  calc
    _ ≤ revisedTerminalHeatWeight a g x * (|a| * 1) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hj (abs_nonneg a)) (Real.exp_pos _).le
    _ = _ := by ring

theorem revisedTerminalBackward_bounds (a : ℝ) (g : TerminalSpace)
    (hg : ‖terminalJet g 0‖ ≤ 1) (ψ : ℝ → ℝ) (hψ : HeatC2Datum ψ)
    (L L1 : ℝ) (hL : 0 ≤ L) (hψb : ∀ y, |ψ y| ≤ L)
    (hψd : ∀ y, |deriv ψ y| ≤ L1) (v x : ℝ) :
    |backwardHeatQuotient (fun y => revisedTerminalHeatWeight a g y * ψ y)
      (revisedTerminalHeatWeight a g) v x| ≤ L ∧
    |backwardHeatQuotientDx (fun y => revisedTerminalHeatWeight a g y * ψ y)
      (revisedTerminalHeatWeight a g) v x| ≤ L1 + 2*|a| *L := by
  have hD := heatC2Datum_revisedTerminalHeatWeight a g
  have hN := hD.mul hψ
  have hp := gaussianHeatFlow_revisedTerminalHeatWeight_pos a g v x
  have hrel : ∀ y, |revisedTerminalHeatWeight a g y * ψ y| ≤ L * revisedTerminalHeatWeight a g y := by
    intro y
    rw [abs_mul,abs_of_pos (show 0 < revisedTerminalHeatWeight a g y from Real.exp_pos _),mul_comm]
    exact mul_le_mul_of_nonneg_right (hψb y) (Real.exp_pos _).le
  have hn : ∀ y, |deriv (fun z => revisedTerminalHeatWeight a g z * ψ z) y| ≤
      (|a| *L+L1)*revisedTerminalHeatWeight a g y := by
    intro y
    have hd := (hasDerivAt_revisedTerminalHeatWeight a g y).mul
      ((hψ.smooth.differentiable (by norm_num) y).hasDerivAt)
    change |deriv (revisedTerminalHeatWeight a g * ψ) y| ≤ _
    rw [hd.deriv]
    calc
      _ ≤ |revisedTerminalHeatWeight a g y * (a*terminalJet g 0 y)*ψ y| +
        |revisedTerminalHeatWeight a g y*deriv ψ y| := abs_add_le _ _
      _ ≤ (|a| *revisedTerminalHeatWeight a g y)*L+revisedTerminalHeatWeight a g y*L1 := by
        apply add_le_add
        · rw [abs_mul]
          have hh := abs_deriv_revisedTerminalHeatWeight_le a g hg y
          rw [(hasDerivAt_revisedTerminalHeatWeight a g y).deriv] at hh
          exact mul_le_mul hh (hψb y) (abs_nonneg _)
            (mul_nonneg (abs_nonneg a) (Real.exp_pos _).le)
        · rw [abs_mul,abs_of_pos (show 0 < revisedTerminalHeatWeight a g y from Real.exp_pos _)]
          exact mul_le_mul_of_nonneg_left (hψd y) (Real.exp_pos _).le
      _ = _ := by ring
  refine ⟨abs_backwardHeatQuotient_le hN hD L v x hp hrel,?_⟩
  have hb := abs_backwardHeatQuotientDx_le hN hD L (|a| *L+L1) |a| v x hp hL
    (abs_nonneg a) hrel hn (abs_deriv_revisedTerminalHeatWeight_le a g hg)
  convert hb using 1
  ring

theorem revisedColeHopfDiffusion_backward_interior (a : ℝ) (T : ℝ≥0) (g : TerminalSpace)
    (hg : ‖terminalJet g 0‖ ≤ 1) (x : ℝ) (c : ℝ≥0) (hc : c < T)
    (ψ : ℝ → ℝ) (hψ : HeatC2Datum ψ) (L L1 : ℝ) (hL : 0 ≤ L) (hL1 : 0 ≤ L1)
    (hψb : ∀ y, |ψ y| ≤ L) (hψd : ∀ y, |deriv ψ y| ≤ L1) :
    (∫ ω, backwardHeatQuotient (fun y => revisedTerminalHeatWeight a g y*ψ y)
      (revisedTerminalHeatWeight a g) ((T:ℝ)-c)
        (revisedColeHopfDiffusion a T g hg x c ω) ∂canonicalBrownianMeasure) =
      backwardHeatQuotient (fun y => revisedTerminalHeatWeight a g y*ψ y)
        (revisedTerminalHeatWeight a g) T x := by
  let d := revisedDiffusionDriftData a T g hg
  let X := revisedColeHopfDiffusion a T g hg x
  let μ := clockedItoDrift d revisedUnitRate x T T.coe_nonneg
  let δ : ℝ := ((T:ℝ)-c)/2
  have hδ : 0 < δ := by dsimp [δ]; exact div_pos (sub_pos.mpr (NNReal.coe_lt_coe.mpr hc)) (by norm_num)
  have hcap : (c:ℝ)+δ ≤ T := by dsimp [δ]; linarith [NNReal.coe_lt_coe.mpr hc]
  have hD := heatC2Datum_revisedTerminalHeatWeight a g
  have hN := hD.mul hψ
  have hp := fun v y => (gaussianHeatFlow_revisedTerminalHeatWeight_pos a g v y).ne'
  let f := cappedBackwardHeatQuotient
    (fun y => revisedTerminalHeatWeight a g y*ψ y) (revisedTerminalHeatWeight a g) 1 T c δ
  obtain ⟨hf,hdt,hdx,hxx⟩ := cappedBackwardHeatQuotient_ito_continuous hN hD hp
    1 T c δ one_ne_zero hδ hcap
  have hchar := boundedDriftVariableItoCharacteristics_clockedItoState d revisedUnitRate x T T.coe_nonneg
  have hvalue (r : ℝ≥0) : Integrable (fun ω => (1:ℝ)*f r (X r ω)) canonicalBrownianMeasure := by
    apply (integrable_const L).mono'
    · exact (stronglyMeasurable_const.mul (hf.comp_stronglyMeasurable
        (stronglyMeasurable_const.prodMk
          ((hchar.adapted_state r).mono (Filtration.le _ r))))).aestronglyMeasurable
    · filter_upwards [] with ω
      simpa only [one_mul,Real.norm_eq_abs,f,cappedBackwardHeatQuotient] using
        (revisedTerminalBackward_bounds a g hg ψ hψ L L1 hL hψb hψd _ (X r ω)).1
  have hK : ∀ s ∈ Icc (0:ℝ) (c:ℝ), ∀ y, ‖itoSpaceDerivative f s y‖ ≤
      (L1+2*|a| *L).toNNReal := by
    intro s hs y
    rw [(cappedBackwardHeatQuotient_ito_derivatives hN hD hp
      1 T c δ s y one_ne_zero hδ hcap).2.1,Real.norm_eq_abs,
        Real.coe_toNNReal _ (by positivity)]
    exact (revisedTerminalBackward_bounds a g hg ψ hψ L L1 hL hψb hψd _ y).2
  have hPDE : ∀ ω, ∀ s ∈ Icc (0:ℝ) (c:ℝ),
      itoTimeDerivative f s (X s.toNNReal ω)+itoSpaceDerivative f s (X s.toNNReal ω)*μ s.toNNReal ω+
        (1/2:ℝ)*itoSpaceSecondDerivative f s (X s.toNNReal ω)*(rateVolatility revisedUnitRate s.toNNReal)^2 = 0 := by
    intro ω s hs
    have hsT : s ∈ Icc (0:ℝ) T := ⟨hs.1,hs.2.trans (NNReal.coe_lt_coe.mpr hc).le⟩
    have hμ : μ s.toNNReal ω = a*terminalJet (coleHopfTerminal ((a,(T:ℝ)-s),g)) 0 (X s.toNNReal ω) := by
      simp only [μ,clockedItoDrift,Real.coe_toNNReal s hs.1,ite_eq_left hsT.2,d,
        revisedDiffusionDriftData,revisedDiffusionVariance_of_mem T hsT]
      rfl
    obtain ⟨hd,hd',hd''⟩ := cappedBackwardHeatQuotient_ito_derivatives hN hD hp
      1 T c δ s (X s.toNNReal ω) one_ne_zero hδ hcap
    rw [hd,hd',hd'',hμ,rateVolatility_sq,hjbTimeCap_of_le c δ s hs.2]
    have hcapD : hjbTimeCapD c δ s = 1 := by simp [hjbTimeCapD,hs.2]
    rw [hcapD]
    have hh := backwardHeatQuotient_heat_generator
      (fun y => revisedTerminalHeatWeight a g y*ψ y) (revisedTerminalHeatWeight a g)
      ((T:ℝ)-s) (X s.toNNReal ω) (hp _ _)
    rw [gaussianHeatFlow_revisedTerminalHeatWeight_log_gradient a g (sub_nonneg.mpr hsT.2)] at hh
    simp only [one_pow,one_mul,mul_one,revisedUnitRate]
    convert hh using 1
    ring
  have he := backward_weighted_expectation_of_variableDrift hchar f hf
    (fun y s => (hasDerivAt_cappedBackwardHeatQuotient_time hN hD hp
      1 T c δ s y one_ne_zero hδ hcap).differentiableAt)
    (fun s => contDiff_cappedBackwardHeatQuotient_spatial hN hD hp 1 T c δ s)
    hdt hdx hxx c _ hK (fun _ => 1) stronglyMeasurable_const 1 (fun _ => by norm_num)
    hPDE (hvalue 0) (hvalue c)
  simpa only [one_mul,f,cappedBackwardHeatQuotient,one_pow,one_mul,
    hjbTimeCap_of_le c δ (c:ℝ) le_rfl,hjbTimeCap_of_le c δ 0 c.coe_nonneg,sub_zero,
    X,clockedItoState_zero,integral_const,probReal_univ,one_smul,revisedColeHopfDiffusion,d] using he

theorem revisedColeHopfDiffusion_backward (a : ℝ) (T : ℝ≥0) (g : TerminalSpace)
    (hg : ‖terminalJet g 0‖ ≤ 1) (x : ℝ)
    (ψ : ℝ → ℝ) (hψ : HeatC2Datum ψ) (L L1 : ℝ) (hL : 0 ≤ L) (hL1 : 0 ≤ L1)
    (hψb : ∀ y, |ψ y| ≤ L) (hψd : ∀ y, |deriv ψ y| ≤ L1) :
    (∫ ω, ψ (revisedColeHopfDiffusion a T g hg x T ω) ∂canonicalBrownianMeasure) =
      backwardHeatQuotient (fun y => revisedTerminalHeatWeight a g y*ψ y)
        (revisedTerminalHeatWeight a g) T x := by
  have hterminal (y : ℝ) : backwardHeatQuotient
      (fun z => revisedTerminalHeatWeight a g z*ψ z) (revisedTerminalHeatWeight a g) 0 y = ψ y := by
    simp [backwardHeatQuotient,gaussianHeatFlow,revisedTerminalHeatWeight,(Real.exp_pos _).ne']
  by_cases hT : T=0
  · subst T
    simp only [revisedColeHopfDiffusion_zero,NNReal.coe_zero,hterminal,integral_const,
      probReal_univ,one_smul]
  have hTpos : 0 < T := lt_of_le_of_ne (bot_le : 0 ≤ T) (Ne.symm hT)
  have hD := heatC2Datum_revisedTerminalHeatWeight a g
  have hN := hD.mul hψ
  have hp := fun v y => (gaussianHeatFlow_revisedTerminalHeatWeight_pos a g v y).ne'
  have hQ := (continuous_backwardHeatQuotient_jets hN hD hp).1
  let X := revisedColeHopfDiffusion a T g hg x
  have hchar := boundedDriftVariableItoCharacteristics_clockedItoState
    (revisedDiffusionDriftData a T g hg) revisedUnitRate x T T.coe_nonneg
  have hXm (t : ℝ≥0) : StronglyMeasurable (X t) :=
    (hchar.adapted_state t).mono (Filtration.le _ t)
  let E : ℝ≥0 → ℝ := fun c => ∫ ω, backwardHeatQuotient
    (fun y => revisedTerminalHeatWeight a g y*ψ y) (revisedTerminalHeatWeight a g)
    ((T:ℝ)-c) (X c ω) ∂canonicalBrownianMeasure
  let R := backwardHeatQuotient (fun y => revisedTerminalHeatWeight a g y*ψ y)
    (revisedTerminalHeatWeight a g) T x
  have hE : Continuous E := by
    apply continuous_of_dominated (bound := fun _ => L)
    · intro c
      exact (hQ.comp_stronglyMeasurable (stronglyMeasurable_const.prodMk (hXm c))).aestronglyMeasurable
    · intro c
      filter_upwards [] with ω
      simpa only [Real.norm_eq_abs] using
        (revisedTerminalBackward_bounds a g hg ψ hψ L L1 hL hψb hψd _ (X c ω)).1
    · exact integrable_const L
    · filter_upwards [] with ω
      exact hQ.comp ((continuous_const.sub NNReal.continuous_coe).prodMk
        (hchar.continuous_state ω))
  have hclosed : IsClosed {c : ℝ≥0 | E c = R} := isClosed_eq hE continuous_const
  have hsub : Iio T ⊆ {c : ℝ≥0 | E c = R} := fun c hc =>
    revisedColeHopfDiffusion_backward_interior a T g hg x c hc ψ hψ L L1 hL hL1 hψb hψd
  have hmem : T ∈ closure (Iio T) := by
    rw [closure_Iio' (show (Iio T).Nonempty from ⟨0,hTpos⟩)]
    exact le_rfl
  have he : E T=R := (closure_minimal hsub hclosed) hmem
  simpa only [E,R,sub_self,hterminal,X] using he

/-- The distribution is proved for the actual Brownian-driven solution for
every terminal datum in the paper's Banach space, including mass zero and
variance zero.  No transition-law hypothesis is assumed. -/
theorem revisedColeHopfDiffusion_endpoint_law (a : ℝ) (T : ℝ≥0) (g : TerminalSpace)
    (hg : ‖terminalJet g 0‖ ≤ 1) (x : ℝ) :
    canonicalBrownianMeasure.map (revisedColeHopfDiffusion a T g hg x T) =
      constantMassKernel a T (terminalValue g) x := by
  have := isMarkovKernel_constantMassKernel a T (terminalValue g)
    (contDiff_terminalValue g).continuous (hasLinearGrowth_terminalValue g)
  have hX : Measurable (revisedColeHopfDiffusion a T g hg x T) :=
    ((stronglyAdapted_clockedItoState (revisedDiffusionDriftData a T g hg)
      revisedUnitRate x T T.coe_nonneg T).mono (Filtration.le _ T)).measurable
  apply measure_eq_of_cos_sin_integrals
  · intro ξ
    rw [integral_map hX.aemeasurable (by fun_prop)]
    have he := revisedColeHopfDiffusion_backward a T g hg x
      (fun y => Real.cos (ξ*y)) (heatC2Datum_cos ξ) 1 |ξ| zero_le_one (abs_nonneg ξ)
      (fun y => Real.abs_cos_le_one _) (fun y => by
        have hd := (((hasDerivAt_id y).const_mul ξ).cos).deriv
        simp only [id_eq,mul_one] at hd
        rw [hd,abs_mul,abs_neg]
        exact mul_le_of_le_one_left (abs_nonneg ξ) (Real.abs_sin_le_one _))
    exact he.trans (backwardHeatQuotient_exp_eq_kernel_integral a T (terminalValue g)
      (contDiff_terminalValue g).continuous (hasLinearGrowth_terminalValue g)
      (fun y => Real.cos (ξ*y)) (by fun_prop) x)
  · intro ξ
    rw [integral_map hX.aemeasurable (by fun_prop)]
    have he := revisedColeHopfDiffusion_backward a T g hg x
      (fun y => Real.sin (ξ*y)) (heatC2Datum_sin ξ) 1 |ξ| zero_le_one (abs_nonneg ξ)
      (fun y => Real.abs_sin_le_one _) (fun y => by
        have hd := (((hasDerivAt_id y).const_mul ξ).sin).deriv
        simp only [id_eq,mul_one] at hd
        rw [hd,abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg ξ) (Real.abs_cos_le_one _))
    exact he.trans (backwardHeatQuotient_exp_eq_kernel_integral a T (terminalValue g)
      (contDiff_terminalValue g).continuous (hasLinearGrowth_terminalValue g)
      (fun y => Real.sin (ξ*y)) (by fun_prop) x)

theorem revisedColeHopfDiffusion_unique (a : ℝ) (T : ℝ≥0) (g : TerminalSpace)
    (hg : ‖terminalJet g 0‖ ≤ 1) (x : ℝ) (ω : BrownianSample)
    (X : ℝ → ℝ) (hX : Continuous X)
    (hXe : ∀ t ∈ Icc (0:ℝ) T, X t=x+canonicalBrownian t.toNNReal ω+
      ∫ s in 0..t, a*terminalJet (coleHopfTerminal ((a,(T:ℝ)-s),g)) 0 (X s)) :
    ∀ t ∈ Icc (0:ℝ) T, X t=revisedColeHopfDiffusion a T g hg x t.toNNReal ω := by
  let d := revisedDiffusionDriftData a T g hg
  have he := additiveStateReal_unique d x T T.coe_nonneg
    (rateNoiseReal revisedUnitRate ω) (continuous_rateNoiseReal revisedUnitRate ω) X hX (by
      intro t ht
      rw [hXe t ht]
      simp only [rateNoiseReal,timeChangedBrownian,rateClock_revisedUnitRate]
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht.1] at hs
      have hsT : s ∈ Icc (0:ℝ) T := ⟨hs.1,hs.2.trans ht.2⟩
      simp only [d,revisedDiffusionDriftData,revisedDiffusionVariance_of_mem T hsT])
  intro t ht
  rw [he ht]
  unfold revisedColeHopfDiffusion
  rw [clockedItoState_eq _ _ _ _ _ (by simpa only [Real.coe_toNNReal t ht.1] using ht.2)]
  simp only [Real.coe_toNNReal t ht.1,clockedStateReal,d]

theorem revisedColeHopfDiffusion_unique_on (a : ℝ) (T : ℝ≥0) (g : TerminalSpace)
    (hg : ‖terminalJet g 0‖ ≤ 1) (x : ℝ) (ω : BrownianSample)
    (X : ℝ → ℝ) (hX : ContinuousOn X (Icc (0:ℝ) T))
    (hXe : ∀ t ∈ Icc (0:ℝ) T, X t=x+canonicalBrownian t.toNNReal ω+
      ∫ s in 0..t, a*terminalJet (coleHopfTerminal ((a,(T:ℝ)-s),g)) 0 (X s)) :
    ∀ t ∈ Icc (0:ℝ) T, X t=revisedColeHopfDiffusion a T g hg x t.toNNReal ω := by
  let Y : ℝ → ℝ := fun s => X (projIcc (0:ℝ) T T.coe_nonneg s)
  have hY : Continuous Y := (hX.comp_continuous continuous_subtype_val
    (fun s : Icc (0:ℝ) T => s.property)).comp continuous_projIcc
  have heq {s : ℝ} (hs : s ∈ Icc (0:ℝ) T) : Y s=X s := by
    simp only [Y,projIcc_of_mem T.coe_nonneg hs]
  have hYe : ∀ t ∈ Icc (0:ℝ) T, Y t=x+canonicalBrownian t.toNNReal ω+
      ∫ s in 0..t, a*terminalJet (coleHopfTerminal ((a,(T:ℝ)-s),g)) 0 (Y s) := by
    intro t ht
    rw [heq ht,hXe t ht]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    dsimp only
    rw [heq ⟨hs.1,hs.2.trans ht.2⟩]
  intro t ht
  rw [←heq ht]
  exact revisedColeHopfDiffusion_unique a T g hg x ω Y hY hYe t ht

/-- Literal A.1(iii) with `w` the raw Cole--Hopf transform and the drift its
actual spatial derivative.  Existence, pathwise uniqueness on the time
interval, and the endpoint probability law are supplied together. -/
theorem revised_appendix_a_1_iii (a V : ℝ) (_ha : 0 ≤ a) (hV : 0 ≤ V)
    (g : TerminalSpace) (hg : ‖terminalJet g 0‖ ≤ 1) (x : ℝ) :
    ∃ ξ : ℝ≥0 → BrownianSample → ℝ,
      StronglyAdapted canonicalBrownianFiltration ξ ∧
      (∀ ω, Continuous (fun t => ξ t ω)) ∧
      (∀ ω, ξ 0 ω=x) ∧
      (∀ ω, ∀ t : ℝ≥0, (t:ℝ) ≤ V → ξ t ω=x+canonicalBrownian t ω+
        ∫ s in 0..(t:ℝ), a*deriv (coleHopf a (V-s).toNNReal (terminalValue g)) (ξ s.toNNReal ω)) ∧
      canonicalBrownianMeasure.map (ξ V.toNNReal)=constantMassKernel a V.toNNReal (terminalValue g) x ∧
      (∀ ω, ∀ X : ℝ → ℝ, ContinuousOn X (Icc (0:ℝ) V) →
        (∀ t ∈ Icc (0:ℝ) V, X t=x+canonicalBrownian t.toNNReal ω+
          ∫ s in 0..t, a*deriv (coleHopf a (V-s).toNNReal (terminalValue g)) (X s)) →
        ∀ t ∈ Icc (0:ℝ) V, X t=ξ t.toNNReal ω) := by
  let T := V.toNNReal
  have hTV : (T:ℝ)=V := Real.coe_toNNReal V hV
  have hderiv (s : ℝ) (hs : s ≤ V) (y : ℝ) :
      deriv (coleHopf a (V-s).toNNReal (terminalValue g)) y =
        terminalJet (coleHopfTerminal ((a,V-s),g)) 0 y := by
    have he : coleHopf a (V-s).toNNReal (terminalValue g) =
        terminalValue (coleHopfTerminal ((a,V-s),g)) :=
      funext (fun z => (terminalValue_coleHopfTerminal_nonneg ((a,V-s),g) (sub_nonneg.mpr hs) z).symm)
    rw [he,(hasDerivAt_terminalValue _ y).deriv]
  refine ⟨revisedColeHopfDiffusion a T g hg x,
    stronglyAdapted_revisedColeHopfDiffusion a T g hg x,
    continuous_clockedItoState _ _ _ _ _,revisedColeHopfDiffusion_zero a T g hg x,?_,
    revisedColeHopfDiffusion_endpoint_law a T g hg x,?_⟩
  · intro ω t ht
    rw [revisedColeHopfDiffusion_integral_equation a T g hg x ω t
      (NNReal.coe_le_coe.mp (by rw [hTV]; exact ht)),hTV]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le t.coe_nonneg] at hs
    dsimp only
    rw [hderiv s (hs.2.trans ht)]
  · intro ω X hX hXe t ht
    apply revisedColeHopfDiffusion_unique_on a T g hg x ω X (by simpa only [hTV] using hX)
      ?_ t (by simpa only [hTV] using ht)
    intro r hr
    rw [hTV] at hr ⊢
    rw [hXe r hr]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hr.1] at hs
    dsimp only
    rw [hderiv s (hs.2.trans hr.2)]

end DepthPaper
