module

public import DepthPaper.CompactTiltUniformBounds
public import DepthPaper.GaussianTiltedOperator

@[expose] public section


/-! Uniform all-order bounds for genuine fixed-reference normalized averages
of bounded observables. The auxiliary tilt inverse cancels the Gaussian
precision prefactor before any differentiation. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff
namespace DepthPaper
set_option maxSynthPendingDepth 64

abbrev WeightedTiltParameter := TerminalParameter×GaussianObservable

def weightedTiltBall (ρ R B J : ℝ) : Set WeightedTiltParameter :=
  {q|ρ≤q.1.1 ∧ q.1.1≤R ∧ ‖q.1.2‖≤B ∧ ‖q.2‖≤J}

def compactTopRestrictionCLM : (CompactTiltLocation→ᵇℝ)→L[ℝ](ℝ→ᵇℝ) :=
  BoundedContinuousFunction.compContinuousCLM ℝ ℝ
    ⟨fun x:ℝ=>(⟨1,⟨zero_le_one,le_rfl⟩⟩,x),by fun_prop⟩

def weightedKernelInverse (w : ℝ≥0) (p : TerminalParameter) : ℝ→ᵇℝ :=
  compactTopRestrictionCLM (Ring.inverse (compactTiltNormalizer w (p.1,(p.2,0))))

theorem compactTiltNormalizer_top (w : ℝ≥0) (p : TerminalParameter) (hp : 0<p.1) (x : ℝ) :
    compactTiltNormalizer w (p.1,(p.2,0)) (⟨1,⟨zero_le_one,le_rfl⟩⟩,x)=
      centeredKernelNormalizer w p x := by
  change (∫d,compactTiltKernel (p.1,(p.2,0)) (d,(⟨1,⟨zero_le_one,le_rfl⟩⟩,x))
    ∂gaussianReal 0 w)=(∫d,weightedTerminalKernel p (d,x) ∂gaussianReal 0 w)
  apply integral_congr_ae
  exact .of_forall fun d=>by
    dsimp only
    rw [compactTiltKernel_apply _ hp,weightedTerminalKernel_apply p hp]
    simp only [compactTiltLaplaceLinear_apply,terminalValue_zeroDatum,sub_self,add_zero,one_mul]

theorem weightedKernelInverse_apply (w : ℝ≥0) (p : TerminalParameter) (hp : 0<p.1) (x : ℝ) :
    weightedKernelInverse w p x=(centeredKernelNormalizer w p x)⁻¹ := by
  change Ring.inverse (compactTiltNormalizer w (p.1,(p.2,0)))
    (⟨1,⟨zero_le_one,le_rfl⟩⟩,x)=_
  rw [inverse_compactTiltNormalizer_apply w _ hp,compactTiltNormalizer_top w p hp x]

def weightedNormalizedAverage (w : ℝ≥0) (q : WeightedTiltParameter) : ℝ→ᵇℝ :=
  weightedKernelInverse w q.1*gaussianKernelAverage w (weightedTerminalKernel q.1*q.2)

theorem weightedNormalizedAverage_apply (w : ℝ≥0) (q : WeightedTiltParameter)
    (hq : 0<q.1.1) (x : ℝ) :
    weightedNormalizedAverage w q x=
      (∫d,Real.exp (terminalLaplaceLinear (d,x) q.1)*q.2 (d,x) ∂gaussianReal 0 w)/
      (∫d,Real.exp (terminalLaplaceLinear (d,x) q.1) ∂gaussianReal 0 w) := by
  change weightedKernelInverse w q.1 x*(∫d,(weightedTerminalKernel q.1*q.2) (d,x)
    ∂gaussianReal 0 w)=_
  rw [weightedKernelInverse_apply w q.1 hq]
  have hden : centeredKernelNormalizer w q.1 x=
      ∫d,Real.exp (terminalLaplaceLinear (d,x) q.1) ∂gaussianReal 0 w := by
    change (∫d,weightedTerminalKernel q.1 (d,x) ∂gaussianReal 0 w)=_
    apply integral_congr_ae
    exact .of_forall fun d=>by
      dsimp only
      rw [weightedTerminalKernel_apply q.1 hq,terminalLaplaceLinear_apply]
  have hnum : (∫d,(weightedTerminalKernel q.1*q.2) (d,x) ∂gaussianReal 0 w)=
      ∫d,Real.exp (terminalLaplaceLinear (d,x) q.1)*q.2 (d,x) ∂gaussianReal 0 w := by
    apply integral_congr_ae
    exact .of_forall fun d=>by
      dsimp only
      change weightedTerminalKernel q.1 (d,x)*q.2 (d,x)=_
      rw [weightedTerminalKernel_apply q.1 hq,terminalLaplaceLinear_apply]
  rw [hden,hnum]
  ring

theorem norm_weightedTiltBall_le (ρ R B J : ℝ) (hρ : 0<ρ)
    (q : WeightedTiltParameter) (hq : q∈weightedTiltBall ρ R B J) :
    ‖q‖≤max R (max B J) := by
  rw [Prod.norm_def,Prod.norm_def,Real.norm_of_nonneg (hρ.trans_le hq.1).le]
  exact max_le (max_le (hq.2.1.trans (le_max_left _ _))
    (hq.2.2.1.trans ((le_max_left B J).trans (le_max_right _ _))))
    (hq.2.2.2.trans ((le_max_right B J).trans (le_max_right _ _)))

theorem boundedSmoothOn_weightedNormalizedAverage (w : ℝ≥0)
    (ρ R B J : ℝ) (hρ : 0<ρ) (hR : 0≤R) (hB : 0≤B) :
    BoundedSmoothOn (weightedNormalizedAverage w) (weightedTiltBall ρ R B J) := by
  let s := weightedTiltBall ρ R B J
  let C := max R (max B J)
  have hC : 0≤C := hR.trans (le_max_left _ _)
  have hball : ∀q∈s,‖q‖≤C := fun q hq=>norm_weightedTiltBall_le ρ R B J hρ q hq
  have hp := BoundedSmoothOn.linear (ContinuousLinearMap.fst ℝ TerminalParameter GaussianObservable)
    s C hC hball
  have hH := BoundedSmoothOn.linear (ContinuousLinearMap.snd ℝ TerminalParameter GaussianObservable)
    s C hC hball
  have hb := hp.compCLM (ContinuousLinearMap.fst ℝ ℝ TerminalSpace)
  have hg := hp.compCLM (ContinuousLinearMap.snd ℝ ℝ TerminalSpace)
  have hcompact := hb.prodMk (hg.prodMk (BoundedSmoothOn.const (0:TerminalSpace) s))
  have hinv := ((boundedSmoothOn_inverse_compactTiltNormalizer w ρ R B hρ hR hB).comp
    hcompact (fun q hq=>by
      change ρ≤q.1.1 ∧ q.1.1≤R ∧ ‖q.1.2‖+‖(0:TerminalSpace)‖≤B
      simpa only [norm_zero,add_zero] using ⟨hq.1,hq.2.1,hq.2.2.1⟩)).compCLM compactTopRestrictionCLM
  have hk : BoundedSmoothOn (fun q:WeightedTiltParameter=>weightedTerminalKernel q.1) s := by
    refine ⟨fun q hq=>(analyticAt_weightedTerminalKernel q.1 (hρ.trans_le hq.1)).contDiffAt.comp q
      contDiffAt_fst,fun n=>?_⟩
    have hkb : BoundedSmoothOn weightedTerminalKernel {p:TerminalParameter|ρ≤p.1 ∧ ‖p.2‖≤B} := by
      refine ⟨fun p hp=>(analyticAt_weightedTerminalKernel p (hρ.trans_le hp.1)).contDiffAt,
        fun n=>⟨(n.factorial:ℝ)*Real.exp ((B+ρ/2)^2/(2*ρ))/(ρ/2)^n,by positivity,?_⟩⟩
      intro p hp
      exact norm_iteratedFDeriv_weightedTerminalKernel_le ρ B hρ p hp.1 hp.2 n
    exact (hkb.comp hp (fun q hq=>⟨hq.1,hq.2.2.1⟩)).bound n
  have hnum := (hk.bilinear hH (ContinuousLinearMap.mul ℝ GaussianObservable)).compCLM
    (gaussianKernelAverageCLM w)
  exact hinv.bilinear hnum (ContinuousLinearMap.mul ℝ (ℝ→ᵇℝ))

end DepthPaper
