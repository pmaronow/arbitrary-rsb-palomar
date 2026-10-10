module

public import GeneralDepthPaper.WeightedTiltUniformBounds
public import GeneralDepthPaper.ColeHopfParameterBounds
public import GeneralDepthPaper.TerminalGaussianJets

@[expose] public section


/-! All-order uniform parameter bounds for actual Gaussian tilted spatial
moments, obtained from a fixed reference Gaussian and positive kernel inverse. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64

def referenceTerminalGaussianMoment (w : ℝ) (H : ColeHopfParameter→GaussianObservable)
    (p : ColeHopfParameter) : ℝ→ᵇℝ :=
  weightedNormalizedAverage w.toNNReal
    ((gaussianPrecisionDifference p.1.2 w,p.1.1•p.2),H p)

theorem referenceTerminalGaussianMoment_eq (w : ℝ) (H : ColeHopfParameter→GaussianObservable)
    (p : ColeHopfParameter) (hv : 0<p.1.2) (hvw : p.1.2<w) :
    referenceTerminalGaussianMoment w H p=terminalGaussianMoment H p := by
  have hw : 0<w := hv.trans hvw
  have hvN : (0:ℝ≥0)<p.1.2.toNNReal := by
    simpa only [←NNReal.coe_lt_coe,Real.coe_toNNReal _ hv.le,NNReal.coe_zero] using hv
  have hwN : (0:ℝ≥0)<w.toNNReal := by
    simpa only [←NNReal.coe_lt_coe,Real.coe_toNNReal _ hw.le,NNReal.coe_zero] using hw
  let c := Real.sqrt (2*Real.pi*w)/Real.sqrt (2*Real.pi*p.1.2)
  have hc : c≠0 := by dsimp [c]; positivity
  ext x
  rw [referenceTerminalGaussianMoment,weightedNormalizedAverage_apply _ _
    (gaussianPrecisionDifference_pos hv hvw),terminalGaussianMoment,tiltedGaussianOperator_apply _ hv]
  let E : ℝ→ℝ := fun d=>Real.exp (p.1.1*(terminalValue p.2 (x+d)-terminalValue p.2 x))
  have hexp (d:ℝ) : Real.exp (-gaussianPrecisionDifference p.1.2 w*d^2)*E d=
      Real.exp (terminalLaplaceLinear (d,x) (gaussianPrecisionDifference p.1.2 w,p.1.1•p.2)) := by
    rw [←Real.exp_add,terminalLaplaceLinear_apply]
    dsimp [E]
    simp only [terminalValue_smul]
    congr 1
    ring
  have hden : (∫d,E d ∂gaussianReal 0 p.1.2.toNNReal)=
      c*(∫d,Real.exp (terminalLaplaceLinear (d,x)
        (gaussianPrecisionDifference p.1.2 w,p.1.1•p.2)) ∂gaussianReal 0 w.toNNReal) := by
    have hd := gaussianPrecision_integral p.1.2.toNNReal w.toNNReal hvN hwN E
    simpa only [Real.coe_toNNReal _ hv.le,Real.coe_toNNReal _ hw.le,hexp,c] using hd
  have hnum : (∫d,E d*H p (d,x) ∂gaussianReal 0 p.1.2.toNNReal)=
      c*(∫d,Real.exp (terminalLaplaceLinear (d,x)
        (gaussianPrecisionDifference p.1.2 w,p.1.1•p.2))*H p (d,x) ∂gaussianReal 0 w.toNNReal) := by
    have hd := gaussianPrecision_integral p.1.2.toNNReal w.toNNReal hvN hwN (fun d=>E d*H p (d,x))
    simpa only [Real.coe_toNNReal _ hv.le,Real.coe_toNNReal _ hw.le,←mul_assoc,hexp,c] using hd
  change _=(∫d,E d*H p (d,x) ∂gaussianReal 0 p.1.2.toNNReal)/
    (∫d,E d ∂gaussianReal 0 p.1.2.toNNReal)
  rw [hnum,hden]
  exact (mul_div_mul_left _ _ hc).symm

theorem boundedSmoothOn_terminalGaussianMoment (A Vlo Vhi B : ℝ)
    (hA : 0≤A) (hVlo : 0<Vlo) (hV : Vlo≤Vhi) (hB : 0≤B)
    (H : ColeHopfParameter→GaussianObservable)
    (hH : BoundedSmoothOn H (coleHopfBall A Vlo Vhi B)) :
    BoundedSmoothOn (terminalGaussianMoment H) (coleHopfBall A Vlo Vhi B) := by
  let w := 2*Vhi
  let ρ := gaussianPrecisionDifference Vhi w
  let R := gaussianPrecisionDifference Vlo w
  have hVhi := hVlo.trans_le hV
  have hρ : 0<ρ := gaussianPrecisionDifference_pos hVhi (by dsimp [w]; linarith)
  have hR : 0≤R := (gaussianPrecisionDifference_pos hVlo (by dsimp [w]; linarith)).le
  obtain ⟨J,hJ,hHJ⟩:=hH.bound 0
  have hJb : ∀p∈coleHopfBall A Vlo Vhi B,‖H p‖≤J := by
    simpa only [norm_iteratedFDeriv_zero] using hHJ
  have hg := boundedSmoothOn_coleHopf_terminal A Vlo Vhi B hA hVlo
  have ha := boundedSmoothOn_coleHopf_first A Vlo Vhi B hA hVlo
  have hb := boundedSmoothOn_coleHopf_precision A Vlo Vhi B hA hVlo
  have hag := ha.bilinear hg (ContinuousLinearMap.lsmul ℝ ℝ : ℝ→L[ℝ] TerminalSpace→L[ℝ] TerminalSpace)
  have hparam := (hb.prodMk hag).prodMk hH
  have href := (boundedSmoothOn_weightedNormalizedAverage w.toNNReal ρ R (A*B) J hρ hR
    (mul_nonneg hA hB)).comp hparam (fun p hp=>by
      refine ⟨?_,?_,?_,hJb p hp⟩
      · exact (gaussianPrecisionDifference_bounds Vlo Vhi p.1.2 hVlo hV ⟨hp.2.1,hp.2.2.1⟩).1
      · exact (gaussianPrecisionDifference_bounds Vlo Vhi p.1.2 hVlo hV ⟨hp.2.1,hp.2.2.1⟩).2
      · change ‖p.1.1 • p.2‖≤A*B
        rw [norm_smul]
        exact mul_le_mul hp.1 hp.2.2.2 (norm_nonneg _) hA)
  apply href.congr_of_eventuallyEq
  intro p hp
  have hv := hVlo.trans_le hp.2.1
  have hvw : p.1.2<w := hp.2.2.1.trans_lt (by dsimp [w]; linarith)
  have hlocal : ∀ᶠq:ColeHopfParameter in 𝓝 p,0<q.1.2 ∧ q.1.2<w :=
    ((continuous_snd.comp continuous_fst).tendsto p) (Ioo_mem_nhds hv hvw)
  filter_upwards [hlocal] with q hq
  exact referenceTerminalGaussianMoment_eq w H q hq.1 hq.2

end GeneralDepthPaper
