module

public import DepthPaper.GaussianVarianceRatio
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section


/-! The actual centered Gaussian normalizer is jointly analytic in the mass,
positive variance, and Banach terminal datum, including mass zero. The proof
uses an exact precision change to one fixed Gaussian measure. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff
namespace DepthPaper
set_option maxSynthPendingDepth 32
abbrev ColeHopfParameter := (ℝ×ℝ)×TerminalSpace

def gaussianPrecisionPrefactor (w v : ℝ) : ℝ :=
  Real.sqrt (2*Real.pi*w)/Real.sqrt (2*Real.pi*v)

def referenceGaussianNormalizer (w : ℝ) (p : ColeHopfParameter) : ℝ →ᵇ ℝ :=
  gaussianPrecisionPrefactor w p.1.2 • centeredKernelNormalizer w.toNNReal
    (gaussianPrecisionDifference p.1.2 w,p.1.1•p.2)

def centeredGaussianNormalizer (p : ColeHopfParameter) : ℝ →ᵇ ℝ :=
  referenceGaussianNormalizer (2*p.1.2) p

theorem referenceGaussianNormalizer_apply (w : ℝ) (p : ColeHopfParameter)
    (hv : 0<p.1.2) (hvw : p.1.2<w) (x : ℝ) :
    referenceGaussianNormalizer w p x=
      ∫d,Real.exp (p.1.1*(terminalValue p.2 (x+d)-terminalValue p.2 x))
        ∂gaussianReal 0 p.1.2.toNNReal := by
  have hw : 0<w := hv.trans hvw
  have hvN : (0:ℝ≥0)<p.1.2.toNNReal := by
    rw [←NNReal.coe_lt_coe,NNReal.coe_zero,Real.coe_toNNReal _ hv.le]
    exact hv
  have hvwN : p.1.2.toNNReal<w.toNNReal := by
    simpa only [←NNReal.coe_lt_coe,Real.coe_toNNReal _ hv.le,
      Real.coe_toNNReal _ hw.le] using hvw
  simpa only [referenceGaussianNormalizer,gaussianPrecisionPrefactor,
    BoundedContinuousFunction.coe_smul,Pi.smul_apply,smul_eq_mul,
    Real.coe_toNNReal _ hv.le,Real.coe_toNNReal _ hw.le] using
    (centeredGaussianNormalizer_eq_kernel p.1.1 p.2 p.1.2.toNNReal w.toNNReal hvN hvwN x).symm

theorem centeredGaussianNormalizer_apply (p : ColeHopfParameter)
    (hv : 0<p.1.2) (x : ℝ) :
    centeredGaussianNormalizer p x=
      ∫d,Real.exp (p.1.1*(terminalValue p.2 (x+d)-terminalValue p.2 x))
        ∂gaussianReal 0 p.1.2.toNNReal :=
  referenceGaussianNormalizer_apply (2*p.1.2) p hv (by linarith) x

theorem referenceGaussianNormalizer_eq (w : ℝ) (p : ColeHopfParameter)
    (hv : 0<p.1.2) (hvw : p.1.2<w) :
    referenceGaussianNormalizer w p=centeredGaussianNormalizer p := by
  ext x
  rw [referenceGaussianNormalizer_apply w p hv hvw,centeredGaussianNormalizer_apply p hv]

theorem analyticAt_referenceGaussianNormalizer (w : ℝ) (p : ColeHopfParameter)
    (hv : 0<p.1.2) (hvw : p.1.2<w) :
    AnalyticAt ℝ (referenceGaussianNormalizer w) p := by
  have hvA : AnalyticAt ℝ (fun q:ColeHopfParameter=>q.1.2) p :=
    analyticAt_snd.comp analyticAt_fst
  have hmA : AnalyticAt ℝ (fun q:ColeHopfParameter=>q.1.1) p :=
    analyticAt_fst.comp analyticAt_fst
  have hden : 2*Real.pi*p.1.2≠0 := by positivity
  have hs : AnalyticAt ℝ (fun q : ColeHopfParameter=>Real.sqrt (2*Real.pi*q.1.2)) p :=
    (Real.contDiffAt_sqrt (n:=ω) hden).analyticAt.comp (f:=fun q:ColeHopfParameter=>2*Real.pi*q.1.2)
      (analyticAt_const.mul hvA)
  have hpref : AnalyticAt ℝ (fun q:ColeHopfParameter=>gaussianPrecisionPrefactor w q.1.2) p := by
    exact analyticAt_const.div hs (by apply ne_of_gt; positivity)
  have hprecision : AnalyticAt ℝ (fun q:ColeHopfParameter=>gaussianPrecisionDifference q.1.2 w) p := by
    unfold gaussianPrecisionDifference
    exact (analyticAt_const.div (analyticAt_const.mul hvA) (show 2*p.1.2≠0 by positivity)).sub analyticAt_const
  have hdata : AnalyticAt ℝ (fun q:ColeHopfParameter=>q.1.1•q.2) p := hmA.smul analyticAt_snd
  have hkernel : AnalyticAt ℝ (fun q:ColeHopfParameter=>centeredKernelNormalizer w.toNNReal
      (gaussianPrecisionDifference q.1.2 w,q.1.1•q.2)) p :=
    (analyticAt_centeredKernelNormalizer w.toNNReal _
      (gaussianPrecisionDifference_pos hv hvw)).comp (hprecision.prod hdata)
  exact hpref.smul hkernel

theorem analyticAt_centeredGaussianNormalizer (p : ColeHopfParameter) (hv : 0<p.1.2) :
    AnalyticAt ℝ centeredGaussianNormalizer p := by
  have hlocal : ∀ᶠq:ColeHopfParameter in 𝓝 p,0<q.1.2 ∧ q.1.2<2*p.1.2 :=
    (show Tendsto (fun q:ColeHopfParameter=>q.1.2) (𝓝 p) (𝓝 p.1.2) from
      (continuous_snd.comp continuous_fst).tendsto p)
      (Ioo_mem_nhds hv (by linarith))
  apply (analyticAt_referenceGaussianNormalizer (2*p.1.2) p hv (by linarith)).congr
  exact hlocal.mono fun q hq=>referenceGaussianNormalizer_eq _ q hq.1 hq.2

theorem contDiffAt_centeredGaussianNormalizer (p : ColeHopfParameter) (hv : 0<p.1.2) :
    ContDiffAt ℝ ⊤ centeredGaussianNormalizer p :=
  (analyticAt_centeredGaussianNormalizer p hv).contDiffAt.of_le le_top

end DepthPaper
