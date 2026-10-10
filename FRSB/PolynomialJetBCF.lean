module

public import FRSB.PolynomialJetFields

@[expose] public section


/-! Exact bounded-continuous-function representations of the actual polynomial
jet fields, and their continuity in the weak overlap-law topology. -/
noncomputable section
open Set MvPolynomial Paper
open scoped Topology BoundedContinuousFunction
namespace FRSB
set_option maxHeartbeats 1000000

 def polynomialJetBCF (β:ℝ) (μ:ParisiMeasure) (f:MomentPolynomial) :
    (Icc (0:ℝ) 1×ℝ)→ᵇℝ :=
  aeval (fun j=>bcfSpatialDerivative (parisiGradientBCF β μ) j) f

 theorem polynomialJetBCF_apply (β:ℝ) (μ:ParisiMeasure) (f:MomentPolynomial)
    (p:Icc (0:ℝ) 1×ℝ) :
    polynomialJetBCF β μ f p=polynomialJetField β μ f p.1 p.2 := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [polynomialJetBCF,polynomialJetField]
  | add f g hf hg =>
    change (aeval (fun j=>bcfSpatialDerivative (parisiGradientBCF β μ) j) (f+g)) p=
      eval (fun j=>parisiSpatialJet β μ (j+1) p.1 p.2) (f+g)
    simp only [map_add,BoundedContinuousFunction.add_apply]
    exact congrArg₂ (·+·) hf hg
  | mul_X f j hf =>
    change (aeval (fun j=>bcfSpatialDerivative (parisiGradientBCF β μ) j) (f*X j)) p=
      eval (fun j=>parisiSpatialJet β μ (j+1) p.1 p.2) (f*X j)
    simp only [map_mul,aeval_X,eval_X,BoundedContinuousFunction.mul_apply]
    have hj : bcfSpatialDerivative (parisiGradientBCF β μ) j p =
        parisiSpatialJet β μ (j+1) p.1 p.2 := by
      change _=parisiSlabExtend (by norm_num : (0:ℝ)≤1)
        (bcfSpatialDerivative (parisiGradientBCF β μ) j) (p.1,p.2)
      simp only [parisiSlabExtend,projIcc_of_mem _ p.1.property]
    exact congrArg₂ (·*·) hf hj

 theorem polynomialJetField_eq_extension (β:ℝ) (μ:ParisiMeasure) (f:MomentPolynomial)
    (s x:ℝ) : polynomialJetField β μ f s x=
      parisiSlabExtend (by norm_num : (0:ℝ)≤1) (polynomialJetBCF β μ f) (s,x) := by
  unfold parisiSlabExtend
  rw [polynomialJetBCF_apply]
  unfold polynomialJetField
  apply congrArg (fun y : ℕ→ℝ => eval y f)
  funext j
  change parisiSlabExtend (by norm_num : (0:ℝ)≤1)
    (bcfSpatialDerivative (parisiGradientBCF β μ) j) (s,x)=
      parisiSlabExtend (by norm_num : (0:ℝ)≤1)
        (bcfSpatialDerivative (parisiGradientBCF β μ) j) ((projIcc (0:ℝ) 1 (by norm_num) s:ℝ),x)
  simp only [parisiSlabExtend,projIcc_of_mem _ (projIcc (0:ℝ) 1 (by norm_num) s).property]

 theorem continuous_polynomialJetBCF (β:ℝ) (f:MomentPolynomial) :
    Continuous (fun μ:ParisiMeasure=>polynomialJetBCF β μ f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simpa only [polynomialJetBCF,aeval_C] using
      (continuous_const : Continuous (fun _:ParisiMeasure=>(algebraMap ℝ ((Icc (0:ℝ) 1×ℝ)→ᵇℝ) c)))
  | add f g hf hg =>
    convert hf.add hg using 1
    funext μ
    exact map_add (aeval (fun j=>bcfSpatialDerivative (parisiGradientBCF β μ) j)) f g
  | mul_X f j hf =>
    convert hf.mul (continuous_spatialDerivativeBCF β j) using 1
    funext μ
    simp only [polynomialJetBCF,map_mul,aeval_X,Pi.mul_apply]

 theorem norm_polynomialJetField_sub_le (β:ℝ) (μ ν:ParisiMeasure)
    (f:MomentPolynomial) (s x:ℝ) :
    ‖polynomialJetField β μ f s x-polynomialJetField β ν f s x‖≤
      ‖polynomialJetBCF β μ f-polynomialJetBCF β ν f‖ := by
  rw [polynomialJetField_eq_extension,polynomialJetField_eq_extension]
  exact norm_parisiSlabExtend_sub_le (by norm_num) _ _ _

end FRSB
