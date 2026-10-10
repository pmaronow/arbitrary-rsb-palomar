module

public import FourPapersCommon.PositiveHessianEquivalence
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

@[expose] public section


/-! Schur positivity for continuous bilinear Hessians in product norms.
The eliminated block equation is an actual linear equation, not a supplied
positivity conclusion. No matrix or Euclidean-norm identification is used. -/
noncomputable section
namespace DepthPaper
variable {E F:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
set_option maxHeartbeats 600000

/-- The true graph of the eliminated coordinate. -/
def schurElimination (L:F→L[ℝ]E) : F→L[ℝ] E×F :=
  (-L).prod (ContinuousLinearMap.id ℝ F)

/-- The Schur complement is the original form restricted to that graph. -/
def schurComplement (B:(E×F)→L[ℝ](E×F)→L[ℝ]ℝ) (L:F→L[ℝ]E) :
    F→L[ℝ]F→L[ℝ]ℝ := B.bilinearComp (schurElimination L) (schurElimination L)

@[simp] theorem schurComplement_apply
    (B:(E×F)→L[ℝ](E×F)→L[ℝ]ℝ) (L:F→L[ℝ]E) (u v:F) :
    schurComplement B L u v=B (-L u,u) (-L v,v) := rfl

theorem schur_elimination_orthogonal
    (B:(E×F)→L[ℝ](E×F)→L[ℝ]ℝ) (L:F→L[ℝ]E)
    (hL:∀(x:E)(y:F),B (L y,0) (x,0)=B (0,y) (x,0)) (x:E) (y:F) :
    B (-L y,y) (x,0)=0 := by
  have he : (-L y,y)=-(L y,0)+(0,y) := by ext <;> simp
  rw [he,map_add,map_neg]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.neg_apply]
  rw [hL]
  ring

/-- The exact completing-square identity for the genuine full Hessian. -/
theorem schur_square_identity
    (B:(E×F)→L[ℝ](E×F)→L[ℝ]ℝ) (L:F→L[ℝ]E)
    (hB:∀u v,B u v=B v u)
    (hL:∀(x:E)(y:F),B (L y,0) (x,0)=B (0,y) (x,0)) (x:E) (y:F) :
    B (x,y) (x,y)=B (x+L y,0) (x+L y,0)+schurComplement B L y y := by
  have hv : (x,y)=(x+L y,0)+(-L y,y) := by ext <;> simp
  have hcross := schur_elimination_orthogonal B L hL (x+L y) y
  have hcross' := (hB (x+L y,0) (-L y,y)).trans hcross
  conv_lhs => rw [hv]
  simp only [map_add,ContinuousLinearMap.add_apply,hcross,hcross',zero_add,add_zero]
  rfl

/-- Strict positivity of the full form is equivalent to that of its two
actual Schur blocks. -/
theorem schur_positive_iff
    (B:(E×F)→L[ℝ](E×F)→L[ℝ]ℝ) (L:F→L[ℝ]E)
    (hB:∀u v,B u v=B v u)
    (hL:∀(x:E)(y:F),B (L y,0) (x,0)=B (0,y) (x,0)) :
    (∀v:E×F,v≠0→0<B v v) ↔
      (∀x:E,x≠0→0<B (x,0) (x,0)) ∧
      (∀y:F,y≠0→0<schurComplement B L y y) := by
  constructor
  · intro h
    refine ⟨fun x hx=>h (x,0) (by simpa using hx),fun y hy=>?_⟩
    exact h (-L y,y) (by intro he;exact hy (congrArg Prod.snd he))
  · rintro ⟨hA,hS⟩ ⟨x,y⟩ hv
    rw [schur_square_identity B L hB hL]
    by_cases hy:y=0
    · have hx:x≠0 := by simpa [hy] using hv
      simpa [hy] using hA x hx
    · have hAn : 0≤B (x+L y,0) (x+L y,0) := by
        by_cases hx:x+L y=0
        · rw [hx]
          change 0≤B 0 0
          simp
        · exact (hA _ hx).le
      exact add_pos_of_nonneg_of_pos hAn (hS y hy)

/-- The eliminated block from an actual invertible first Hessian block. -/
def schurBlockSolver (B:(E×F)→L[ℝ](E×F)→L[ℝ]ℝ)
    (A:E≃L[ℝ](E→L[ℝ]ℝ)) : F→L[ℝ]E :=
  A.symm.toContinuousLinearMap.comp
    (B.bilinearComp (ContinuousLinearMap.inr ℝ E F) (ContinuousLinearMap.inl ℝ E F))

/-- The solver genuinely solves the off-diagonal block equation. -/
theorem schurBlockSolver_equation
    (B:(E×F)→L[ℝ](E×F)→L[ℝ]ℝ) (A:E≃L[ℝ](E→L[ℝ]ℝ))
    (hA:∀x w:E,A x w=B (x,0) (w,0)) (x:E) (y:F) :
    B (schurBlockSolver B A y,0) (x,0)=B (0,y) (x,0) := by
  rw [←hA]
  simp [schurBlockSolver,ContinuousLinearMap.bilinearComp_apply]

/-- Literal diagonal-minus-inverse-block form of the actual complement. -/
theorem schurComplement_diagonal_formula
    (B:(E×F)→L[ℝ](E×F)→L[ℝ]ℝ) (L:F→L[ℝ]E)
    (hB:∀u v,B u v=B v u)
    (hL:∀(x:E)(y:F),B (L y,0) (x,0)=B (0,y) (x,0)) (y:F) :
    schurComplement B L y y=B (0,y) (0,y)-B (L y,0) (L y,0) := by
  have h := schur_square_identity B L hB hL (0:E) y
  simp only [zero_add] at h
  linarith

/-- Every actual C² scalar Hessian has the symmetry required by the
Schur-square calculation. -/
theorem scalar_hessian_symmetric {f:E→ℝ} {x:E} (hf:ContDiffAt ℝ 2 f x)
    (v w:E) : fderiv ℝ (fderiv ℝ f) x v w=fderiv ℝ (fderiv ℝ f) x w v :=
  (hf.isSymmSndFDerivAt (by simp)).eq v w

end DepthPaper
