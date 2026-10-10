module

public import FRSB.PolynomialGenerator
public import FRSB.PolynomialMomentConvergence

@[expose] public section


/-! Genuine continuous bounded polynomial jet fields, their spatial chain
rule and differentiated PDE on every actual finite cell. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter MvPolynomial Paper
open scoped Topology BigOperators ContDiff
namespace FRSB
set_option maxHeartbeats 1000000

 def polynomialJetField (β:ℝ) (μ:ParisiMeasure) (f:MomentPolynomial) (s x:ℝ) : ℝ :=
  eval (fun j=>parisiSpatialJet β μ (j+1) s x) f

 theorem continuous_polynomialJetField (β:ℝ) (μ:ParisiMeasure) (f:MomentPolynomial) :
    Continuous (fun p:ℝ×ℝ=>polynomialJetField β μ f p.1 p.2) := by
  unfold polynomialJetField
  rw [show (fun p:ℝ×ℝ=>eval (fun j=>parisiSpatialJet β μ (j+1) p.1 p.2) f)=
      (fun p=>∑d∈f.support,f.coeff d*∏j∈d.support,parisiSpatialJet β μ (j+1) p.1 p.2^d j) by
    funext p;exact eval_eq _ _]
  apply continuous_finsetSum
  intro d _
  apply continuous_const.mul
  apply continuous_finsetProd
  intro j _
  exact (continuous_parisiSpatialJet_succ β μ j).pow _

 theorem norm_polynomialJetField_le_uniform (β:ℝ) (μ:ParisiMeasure)
    (f:MomentPolynomial) (s x:ℝ) :
    ‖polynomialJetField β μ f s x‖≤uniformPolynomialMomentBound β f := by
  unfold polynomialJetField uniformPolynomialMomentBound
  rw [eval_eq]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d _
  rw [norm_mul,norm_prod]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
  intro j _
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _)
    ((norm_parisiSpatialJet_succ_le β μ j s x).trans (norm_spatialDerivativeBCF_le_uniform β μ j)) _

 theorem contDiff_polynomialJetField_spatial (β:ℝ) (μ:ParisiMeasure)
    (f:MomentPolynomial) (s:ℝ) : ContDiff ℝ ∞ (polynomialJetField β μ f s) := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    convert (contDiff_const (c:=c) : ContDiff ℝ ∞ (fun _ : ℝ=>c)) using 1
    funext x
    simp only [polynomialJetField,eval_C]
  | add f g hf hg =>
    convert hf.add hg using 1
    funext x
    simp only [polynomialJetField,map_add]
  | mul_X f j hf =>
    convert hf.mul (contDiff_parisiSpatialJet_succ β μ j s) using 1
    funext x
    simp only [polynomialJetField,map_mul,eval_X]

 theorem hasDerivAt_polynomialJetField_spatial (β:ℝ) (μ:ParisiMeasure)
    (f:MomentPolynomial) (s x:ℝ) :
    HasDerivAt (polynomialJetField β μ f s)
      (polynomialJetField β μ (polynomialSpatialDerivative f) s x) x :=
  hasDerivAt_polynomialJet_spatial β μ f s x

 theorem hasDerivAt_finiteCell_polynomialJetField_time (β:ℝ) (hβ:β≠0)
    {k:ℕ} (s:SpinGlass.Targets.RSBScheme k) {p:ℕ} (hp:p≤k+1)
    (hq:s.q p<s.q (p+1)) (f:MomentPolynomial) {t:ℝ}
    (ht:t∈Ioo (s.q p) (s.q (p+1))) (x:ℝ) :
    HasDerivAt (fun r=>polynomialJetField β (parisiSchemeMeasure s) f r x)
      (β^2*polynomialJetField β (parisiSchemeMeasure s) (polynomialTimeDerivative (s.m p) f) t x) t := by
  have hd:=hasDerivAt_eval_chain
    (fun j r=>parisiSpatialJet β (parisiSchemeMeasure s) (j+1) r x)
    (fun j=>cellTimeForcing β (parisiSchemeMeasure s) (s.m p) (j+1) t x) t
    (fun j=>hasDerivAt_finiteCell_spatialJet_time s β hβ hp hq (j+1) ht x) f
  convert hd using 1
  · rfl
  · unfold polynomialJetField polynomialTimeDerivative
    rw [polynomialDirection_eq_sum,map_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [cellTimeForcing_eq_polynomial,map_mul]
    ring

 theorem polynomialJetField_generator_identity (β:ℝ) (μ:ParisiMeasure)
    (m:ℝ) (f:MomentPolynomial) (s x:ℝ) :
    β^2*polynomialJetField β μ (polynomialTimeDerivative m f) s x+
      polynomialJetField β μ (polynomialSpatialDerivative f) s x*
        (β^2*m*parisiSpatialJet β μ 1 s x)+
      (1/2:ℝ)*polynomialJetField β μ
        (polynomialSpatialDerivative (polynomialSpatialDerivative f)) s x*β^2 =
    β^2*(polynomialJetField β μ (momentDrift0 f) s x+
      m*polynomialJetField β μ (momentDrift1 f) s x) := by
  have he:=congrArg (eval (fun j=>parisiSpatialJet β μ (j+1) s x))
    (polynomial_generator_identity m f)
  simp only [map_add,map_mul,eval_C,eval_X,zero_add] at he
  unfold polynomialJetField
  linear_combination β^2*he

end FRSB
