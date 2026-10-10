module

public import GeneralDepthPaper.TerminalKernelBounds
public import GeneralDepthPaper.CompactNormalizerBounds
public import GeneralDepthPaper.UniformDerivativeCalculus

@[expose] public section


/-! All derivatives of the actual compact auxiliary-tilt response are uniformly
bounded on precision rectangles and terminal balls, including zero tilt. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64

def compactTiltBall (ρ R B : ℝ) : Set CompactTiltParameter :=
  {p|ρ≤p.1 ∧ p.1≤R ∧ ‖p.2.1‖+‖p.2.2‖≤B}

def compactResponseBall (ρ R B J : ℝ) : Set (CompactTiltParameter×TerminalSpace) :=
  {q|q.1∈compactTiltBall ρ R B ∧ ‖q.2‖≤J}

theorem boundedSmoothOn_compactTiltKernel (ρ R B : ℝ) (hρ : 0<ρ) :
    BoundedSmoothOn compactTiltKernel (compactTiltBall ρ R B) := by
  refine ⟨fun p hp=>(analyticAt_compactTiltKernel p (hρ.trans_le hp.1)).contDiffAt,
    fun n=>⟨(n.factorial:ℝ)*Real.exp ((B+ρ)^2/(2*ρ))/(ρ/2)^n,by positivity,?_⟩⟩
  intro p hp
  exact norm_iteratedFDeriv_compactTiltKernel_le ρ B hρ p hp.1 hp.2.2 n

theorem boundedSmoothOn_compactTiltNormalizer (w : ℝ≥0) (ρ R B : ℝ) (hρ : 0<ρ) :
    BoundedSmoothOn (compactTiltNormalizer w) (compactTiltBall ρ R B) :=
  (boundedSmoothOn_compactTiltKernel ρ R B hρ).compCLM (parametricGaussianKernelAverageCLM w)

theorem boundedSmoothOn_inverse_compactTiltNormalizer (w : ℝ≥0)
    (ρ R B : ℝ) (hρ : 0<ρ) (hR : 0≤R) (hB : 0≤B) :
    BoundedSmoothOn (fun p=>Ring.inverse (compactTiltNormalizer w p))
      (compactTiltBall ρ R B) := by
  letI : Nontrivial (CompactTiltLocation→ᵇℝ) := ⟨⟨0,1,by
    intro he
    have hh := congrArg (fun f:CompactTiltLocation→ᵇℝ=>f (⟨0,⟨le_rfl,zero_le_one⟩⟩,0)) he
    norm_num at hh⟩⟩
  exact (boundedSmoothOn_compactTiltNormalizer w ρ R B hρ).inverse
    (fun p hp=>isUnit_compactTiltNormalizer w p (hρ.trans_le hp.1))
    ((compactNormalizerBallLower w B R)⁻¹)
    (inv_nonneg.mpr (compactNormalizerBallLower_pos w B R hB hR).le)
    (fun p hp=>norm_inverse_compactTiltNormalizer_le w B R hB hR p
      (hρ.trans_le hp.1) hp.2.1 hp.2.2)

theorem norm_compactResponseBall_le (ρ R B J : ℝ) (hρ : 0<ρ)
    (q : CompactTiltParameter×TerminalSpace) (hq : q∈compactResponseBall ρ R B J) :
    ‖q‖≤max R (max B J) := by
  have hp0 : 0≤q.1.1 := (hρ.trans_le hq.1.1).le
  have hpB : ‖q.1.2‖≤B := by
    rw [Prod.norm_def]
    exact max_le ((le_add_of_nonneg_right (norm_nonneg _)).trans hq.1.2.2)
      ((le_add_of_nonneg_left (norm_nonneg _)).trans hq.1.2.2)
  rw [Prod.norm_def,Prod.norm_def,Real.norm_of_nonneg hp0]
  exact max_le (max_le (hq.1.2.1.trans (le_max_left _ _))
    (hpB.trans ((le_max_left B J).trans (le_max_right _ _))))
    (hq.2.trans ((le_max_right B J).trans (le_max_right _ _)))

theorem boundedSmoothOn_compactTiltResponse (w : ℝ≥0)
    (ρ R B J : ℝ) (hρ : 0<ρ) (hR : 0≤R) (hB : 0≤B) (hJ : 0≤J) :
    BoundedSmoothOn (compactTiltResponse w) (compactResponseBall ρ R B J) := by
  let s := compactResponseBall ρ R B J
  let C := max R (max B J)
  have hC : 0≤C := hR.trans (le_max_left _ _)
  have hball : ∀q∈s,‖q‖≤C := fun q hq=>norm_compactResponseBall_le ρ R B J hρ q hq
  have hfst := BoundedSmoothOn.linear (ContinuousLinearMap.fst ℝ CompactTiltParameter TerminalSpace)
    s C hC hball
  have hNinv := (boundedSmoothOn_inverse_compactTiltNormalizer w ρ R B hρ hR hB).comp
    hfst (fun q hq=>hq.1)
  have hD := (boundedSmoothOn_compactTiltNormalizer w ρ R B hρ).fderiv.comp
    hfst (fun q hq=>hq.1)
  let dir : (CompactTiltParameter×TerminalSpace)→L[ℝ] CompactTiltParameter :=
    (ContinuousLinearMap.inr ℝ ℝ (TerminalSpace×TerminalSpace)).comp
      ((ContinuousLinearMap.inr ℝ TerminalSpace TerminalSpace).comp
        (ContinuousLinearMap.snd ℝ CompactTiltParameter TerminalSpace))
  have hdir := BoundedSmoothOn.linear dir s C hC hball
  have hnum := hD.bilinear hdir (ContinuousLinearMap.apply ℝ (CompactTiltLocation→ᵇℝ)).flip
  exact hNinv.bilinear hnum (ContinuousLinearMap.mul ℝ (CompactTiltLocation→ᵇℝ))

end GeneralDepthPaper
