module

public import GeneralDepthPaper.UniformDerivativeCalculus

@[expose] public section


/-! Banach-algebra polynomial closure of actual all-order derivative bounds. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GeneralDepthPaper
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem BoundedSmoothOn.smul {f : E→ℝ} {g : E→F} {s : Set E}
    (hf : BoundedSmoothOn f s) (hg : BoundedSmoothOn g s) :
    BoundedSmoothOn (fun x=>f x • g x) s :=
  hf.bilinear hg (ContinuousLinearMap.lsmul ℝ ℝ)

theorem BoundedSmoothOn.const_smul {g : E→F} {s : Set E}
    (hg : BoundedSmoothOn g s) (c : ℝ) : BoundedSmoothOn (fun x=>c • g x) s :=
  (BoundedSmoothOn.const c s).smul hg

theorem BoundedSmoothOn.mul {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    {f g : E→A} {s : Set E} (hf : BoundedSmoothOn f s) (hg : BoundedSmoothOn g s) :
    BoundedSmoothOn (fun x=>f x*g x) s :=
  hf.bilinear hg (ContinuousLinearMap.mul ℝ A)

theorem BoundedSmoothOn.pow {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    {f : E→A} {s : Set E} (hf : BoundedSmoothOn f s) (n : ℕ) :
    BoundedSmoothOn (fun x=>f x^n) s := by
  induction n with
  | zero => simpa only [pow_zero] using BoundedSmoothOn.const (1:A) s
  | succ n ih => simpa only [pow_succ] using ih.mul hf

end GeneralDepthPaper
