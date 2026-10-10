module

public import GeneralDepthPaper.CompactTiltResponse
public import GeneralDepthPaper.UnitTiltAverage
public import GeneralDepthPaper.GaussianVarianceRatio
public import GeneralDepthPaper.ColeHopfCentered

@[expose] public section


/-! The actual centered Cole–Hopf value is jointly C∞ as a bounded spatial
function, including at mass zero. The auxiliary-tilt response supplies its
removable extension and the exact Gaussian precision identity handles variance. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000
open ColeHopfFoundation.ProbabilityTheory

theorem compactTiltResponse_precision_apply (v w : ℝ≥0) (hv : 0<v) (hvw : v<w)
    (a : ℝ) (g : TerminalSpace) (s : CompactTiltLocation) :
    compactTiltResponse w ((gaussianPrecisionDifference v w,(a•g,0)),g) s=
      (∫d,(terminalValue g (s.2+d)-terminalValue g s.2)*
        Real.exp (((s.1:ℝ)*a)*(terminalValue g (s.2+d)-terminalValue g s.2)) ∂gaussianReal 0 v)/
      (∫d,Real.exp (((s.1:ℝ)*a)*(terminalValue g (s.2+d)-terminalValue g s.2)) ∂gaussianReal 0 v) := by
  have hw : 0<w := hv.trans hvw
  have hb := gaussianPrecisionDifference_pos (show 0<(v:ℝ) from hv) (show (v:ℝ)<w from hvw)
  rw [compactTiltResponse_apply w _ hb]
  simp only [compactTiltLaplaceLinear_apply,terminalValue_smul,terminalValue_zeroDatum,
    sub_self,add_zero]
  let D : ℝ→ℝ := fun d=>terminalValue g (s.2+d)-terminalValue g s.2
  let E : ℝ→ℝ := fun d=>Real.exp (((s.1:ℝ)*a)*D d)
  let c : ℝ := Real.sqrt (2*Real.pi*(w:ℝ))/Real.sqrt (2*Real.pi*(v:ℝ))
  have hc : c≠0 := by dsimp [c]; apply ne_of_gt; positivity
  have hden := gaussianPrecision_integral v w hv hw E
  have hnum := gaussianPrecision_integral v w hv hw (fun d=>D d*E d)
  have hn : (∫d,D d*E d ∂gaussianReal 0 v)=c*(∫d,
      Real.exp ((s.1:ℝ)*(a*terminalValue g (s.2+d)-a*terminalValue g s.2)-
        gaussianPrecisionDifference v w*d^2)*D d ∂gaussianReal 0 w) := by
    rw [hnum]
    congr 1
    apply integral_congr_ae
    exact .of_forall fun d=>by
      dsimp [D,E]
      rw [Real.exp_sub,div_eq_mul_inv,←Real.exp_neg]
      have he : (s.1:ℝ)*(a*terminalValue g (s.2+d)-a*terminalValue g s.2)=
        ((s.1:ℝ)*a)*(terminalValue g (s.2+d)-terminalValue g s.2) := by ring
      rw [he]
      simp only [neg_mul]
      ring
  have hd : (∫d,E d ∂gaussianReal 0 v)=c*(∫d,
      Real.exp ((s.1:ℝ)*(a*terminalValue g (s.2+d)-a*terminalValue g s.2)-
        gaussianPrecisionDifference v w*d^2) ∂gaussianReal 0 w) := by
    rw [hden]
    congr 1
    apply integral_congr_ae
    exact .of_forall fun d=>by
      dsimp [E,D]
      rw [Real.exp_sub,div_eq_mul_inv,←Real.exp_neg]
      have he : (s.1:ℝ)*(a*terminalValue g (s.2+d)-a*terminalValue g s.2)=
        ((s.1:ℝ)*a)*(terminalValue g (s.2+d)-terminalValue g s.2) := by ring
      rw [he]
      simp only [neg_mul]
      ring
  change _=(∫d,D d*E d ∂gaussianReal 0 v)/(∫d,E d ∂gaussianReal 0 v)
  rw [hn,hd]
  exact (mul_div_mul_left _ _ hc).symm

def referenceCenteredColeHopfValue (w : ℝ) (p : ColeHopfParameter) : ℝ →ᵇ ℝ :=
  unitTiltAverageCLM (compactTiltResponse w.toNNReal
    ((gaussianPrecisionDifference p.1.2 w,(p.1.1•p.2,0)),p.2))

def centeredColeHopfValue (p : ColeHopfParameter) : ℝ →ᵇ ℝ :=
  referenceCenteredColeHopfValue (2*p.1.2) p

theorem referenceCenteredColeHopfValue_apply (w : ℝ) (p : ColeHopfParameter)
    (hv : 0<p.1.2) (hvw : p.1.2<w) (x : ℝ) :
    referenceCenteredColeHopfValue w p x=
      coleHopf p.1.1 p.1.2.toNNReal (terminalValue p.2) x-terminalValue p.2 x := by
  have hw : 0<w := hv.trans hvw
  have hvN : (0:ℝ≥0)<p.1.2.toNNReal := by
    rw [←NNReal.coe_lt_coe,NNReal.coe_zero,Real.coe_toNNReal _ hv.le]
    exact hv
  have hvwN : p.1.2.toNNReal<w.toNNReal := by
    rw [←NNReal.coe_lt_coe,Real.coe_toNNReal _ hv.le,Real.coe_toNNReal _ hw.le]
    exact hvw
  rw [coleHopf_centered_integral _ (hasLinearGrowth_terminalValue p.2)
    (contDiff_terminalValue p.2).continuous.measurable]
  change unitTiltAverageCLM _ x=_
  rw [unitTiltAverageCLM_apply]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t∈Icc (0:ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
  have hh := compactTiltResponse_precision_apply p.1.2.toNNReal w.toNNReal hvN hvwN p.1.1 p.2
    (projIcc 0 1 zero_le_one t,x)
  simpa only [Real.coe_toNNReal _ hv.le,Real.coe_toNNReal _ hw.le,
    projIcc_of_mem zero_le_one ht',Subtype.coe_mk] using hh

theorem centeredColeHopfValue_apply (p : ColeHopfParameter) (hv : 0<p.1.2) (x : ℝ) :
    centeredColeHopfValue p x=
      coleHopf p.1.1 p.1.2.toNNReal (terminalValue p.2) x-terminalValue p.2 x :=
  referenceCenteredColeHopfValue_apply (2*p.1.2) p hv (by linarith) x

theorem contDiffAt_referenceCenteredColeHopfValue (w : ℝ) (p : ColeHopfParameter)
    (hv : 0<p.1.2) (hvw : p.1.2<w) :
    ContDiffAt ℝ ⊤ (referenceCenteredColeHopfValue w) p := by
  have hvD : ContDiffAt ℝ ⊤ (fun q:ColeHopfParameter=>q.1.2) p := by fun_prop
  have hpD : ContDiffAt ℝ ⊤ (fun q:ColeHopfParameter=>gaussianPrecisionDifference q.1.2 w) p := by
    unfold gaussianPrecisionDifference
    fun_prop (disch:=positivity)
  have hmap : ContDiffAt ℝ ⊤ (fun q:ColeHopfParameter=>
      ((gaussianPrecisionDifference q.1.2 w,(q.1.1•q.2,(0:TerminalSpace))),q.2)) p := by
    exact (hpD.prodMk ((contDiffAt_fst.fst.smul contDiffAt_snd).prodMk contDiffAt_const)).prodMk contDiffAt_snd
  have hresponse := (contDiffAt_compactTiltResponse w.toNNReal
    ((gaussianPrecisionDifference p.1.2 w,(p.1.1•p.2,(0:TerminalSpace))),p.2)
    (gaussianPrecisionDifference_pos hv hvw)).comp p hmap
  exact unitTiltAverageCLM.contDiff.contDiffAt.comp p hresponse

theorem contDiffAt_centeredColeHopfValue (p : ColeHopfParameter) (hv : 0<p.1.2) :
    ContDiffAt ℝ ⊤ centeredColeHopfValue p := by
  have hlocal : ∀ᶠq:ColeHopfParameter in 𝓝 p,0<q.1.2 ∧ q.1.2<2*p.1.2 :=
    (show Tendsto (fun q:ColeHopfParameter=>q.1.2) (𝓝 p) (𝓝 p.1.2) from
      (continuous_snd.comp continuous_fst).tendsto p) (Ioo_mem_nhds hv (by linarith))
  apply (contDiffAt_referenceCenteredColeHopfValue (2*p.1.2) p hv (by linarith)).congr_of_eventuallyEq
  filter_upwards [hlocal] with q hq
  ext x
  rw [centeredColeHopfValue_apply q hq.1,referenceCenteredColeHopfValue_apply _ q hq.1 hq.2]

end GeneralDepthPaper
