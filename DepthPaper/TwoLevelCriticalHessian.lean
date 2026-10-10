module

public import DepthPaper.TwoLevelAtomicDerivative
public import DepthPaper.CriticalHessianChart

@[expose] public section


/-! The actual full atomic coordinate chart preserves critical Hessian
positivity. The chart inverse and derivative bijectivity are proved in the
imported concrete chart modules. -/
noncomputable section
open scoped ContDiff
namespace DepthPaper

theorem twoLevelAtomic_hessian_positive_iff {r:ℕ}
    (f:AtomicPoint (r+1)→ℝ) (v:TwoLevelAtomicPoint r) (hm:v.2.1≠0)
    (hf:ContDiffAt ℝ 2 f (twoLevelAtomicCoordinates v))
    (hc:fderiv ℝ (f ∘ twoLevelAtomicCoordinates) v=0) :
    (∀w:TwoLevelAtomicPoint r,w≠0→
      0<fderiv ℝ (fderiv ℝ (f ∘ twoLevelAtomicCoordinates)) v w w) ↔
    (∀w:AtomicPoint (r+1),w≠0→
      0<fderiv ℝ (fderiv ℝ f) (twoLevelAtomicCoordinates v) w w) :=
  critical_hessian_positive_iff hf
    ((contDiff_twoLevelAtomicCoordinates r).contDiffAt.of_le (by simp))
    (twoLevelAtomicCoordinates_fderiv_bijective v hm) hc

theorem twoLevelAtomic_critical_of_composite_critical {r:ℕ}
    (f:AtomicPoint (r+1)→ℝ) (v:TwoLevelAtomicPoint r) (hm:v.2.1≠0)
    (hf:DifferentiableAt ℝ f (twoLevelAtomicCoordinates v))
    (hc:fderiv ℝ (f ∘ twoLevelAtomicCoordinates) v=0) :
    fderiv ℝ f (twoLevelAtomicCoordinates v)=0 :=
  critical_of_critical_comp hf
    ((contDiff_twoLevelAtomicCoordinates r).differentiable (by simp) v)
    (twoLevelAtomicCoordinates_fderiv_bijective v hm).2 hc

end DepthPaper
