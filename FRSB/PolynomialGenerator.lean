module

public import FRSB.PolynomialJetCalculus
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section


/-! Exact universal polynomial generator algebra for the actual positive
Parisi spatial jets. -/
noncomputable section
open Set MvPolynomial
open scoped BigOperators
namespace FRSB
set_option maxHeartbeats 1000000

 theorem vars_pderiv_subset (f:MomentPolynomial) (i:ℕ) : (pderiv i f).vars⊆f.vars := by
  classical
  have he:pderiv i f=∑d∈f.support,pderiv i (monomial d (f.coeff d)) := by
    rw [← map_sum, support_sum_monomial_coeff]
  rw [he]
  intro j hj
  obtain ⟨d,hd,hjd⟩:=Finset.mem_biUnion.mp (vars_sum_subset f.support (fun d=>pderiv i (monomial d (f.coeff d))) hj)
  rw [pderiv_monomial] at hjd
  have hs:(monomial (d-Finsupp.single i 1) (f.coeff d*(d i:ℝ)) : MomentPolynomial).vars⊆
      (d-Finsupp.single i 1).support := by
    by_cases hc:f.coeff d*(d i:ℝ)=0
    · simp only [hc,monomial_zero];exact Finset.empty_subset _
    · rw [vars_monomial hc]
  exact support_subset_vars_of_mem_support hd (Finsupp.support_tsub (hs hjd))

 theorem polynomialDirection_eq_sum_on (d:ℕ→MomentPolynomial) (f:MomentPolynomial)
    (S:Finset ℕ) (hS:f.vars⊆S) :
    polynomialDirection d f=∑i∈S,d i*pderiv i f := by
  rw [polynomialDirection_eq_sum]
  exact Finset.sum_subset hS (fun i _ hi=>by rw [pderiv_eq_zero_of_notMem_vars hi,mul_zero])

 theorem polynomialSpatialDerivative_eq (f:MomentPolynomial) :
    polynomialSpatialDerivative f=∑i∈f.vars,pderiv i f*X (i+1) := by
  rw [polynomialSpatialDerivative,polynomialDirection_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

 theorem polynomialSpatialDerivative_twice (f:MomentPolynomial) :
    polynomialSpatialDerivative (polynomialSpatialDerivative f)=
      (∑i∈f.vars,pderiv i f*X (i+2))+
        ∑i∈f.vars,∑j∈f.vars,pderiv j (pderiv i f)*X (i+1)*X (j+1) := by
  classical
  rw [polynomialSpatialDerivative_eq f]
  unfold polynomialSpatialDerivative
  rw [map_sum]
  have he:∀i∈f.vars,polynomialDirection (fun i=>X (i+1)) (pderiv i f*X (i+1))=
      pderiv i f*X (i+2)+∑j∈f.vars,pderiv j (pderiv i f)*X (i+1)*X (j+1) := by
    intro i hi
    rw [Derivation.leibniz,polynomialDirection,mkDerivation_X]
    rw [← polynomialDirection,polynomialDirection_eq_sum_on _ _ f.vars (vars_pderiv_subset f i)]
    simp only [smul_eq_mul,show i+1+1=i+2 by omega,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  exact (Finset.sum_congr rfl he).trans Finset.sum_add_distrib

 def nonlinearJetPolynomial (j:ℕ) : MomentPolynomial :=
  ∑k∈Finset.Icc 1 j,MvPolynomial.C ((j+1).choose k:ℝ)*X k*X (j+1-k)

 def polynomialTimeDerivative (m:ℝ) (f:MomentPolynomial) : MomentPolynomial :=
  polynomialDirection (fun j=>MvPolynomial.C (-1/2:ℝ)*(X (j+2)+MvPolynomial.C (2*m)*X 0*X (j+1)+MvPolynomial.C m*nonlinearJetPolynomial j)) f

/-- The drift polynomials are exactly the generator after the PDE transport
terms cancel; this is an equality of polynomials, not a supplied identity. -/
 theorem polynomial_generator_identity (m:ℝ) (f:MomentPolynomial) :
    polynomialTimeDerivative m f+MvPolynomial.C m*X 0*polynomialSpatialDerivative f+
        MvPolynomial.C (1/2:ℝ)*polynomialSpatialDerivative (polynomialSpatialDerivative f)=
      momentDrift0 f+MvPolynomial.C m*momentDrift1 f := by
  classical
  have ha:(MvPolynomial.C (-1/2:ℝ):MomentPolynomial)+MvPolynomial.C (1/2:ℝ)=0 := by
    rw [←map_add];norm_num
  have hb:(MvPolynomial.C (-1/2:ℝ):MomentPolynomial)*MvPolynomial.C (2:ℝ)+1=0 := by
    rw [←map_mul];norm_num
  have he:∀i∈f.vars,MvPolynomial.C (-1/2:ℝ)*(X (i+2)+MvPolynomial.C (2*m)*X 0*X (i+1)+
        MvPolynomial.C m*nonlinearJetPolynomial i)*pderiv i f+
      MvPolynomial.C m*X 0*(pderiv i f*X (i+1))+MvPolynomial.C (1/2:ℝ)*(pderiv i f*X (i+2)) =
      MvPolynomial.C m*(MvPolynomial.C (-1/2:ℝ)*(pderiv i f*nonlinearJetPolynomial i)) := by
    intro i _
    rw [map_mul]
    linear_combination (pderiv i f*X (i+2))*ha +
      (MvPolynomial.C m*X 0*X (i+1)*pderiv i f)*hb
  have hs:=Finset.sum_congr rfl he
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hs
  rw [polynomialTimeDerivative,polynomialDirection_eq_sum,
    polynomialSpatialDerivative_twice,polynomialSpatialDerivative_eq]
  unfold momentDrift0 momentDrift1
  change _ = MvPolynomial.C (1/2:ℝ)*
    (∑i∈f.vars,∑j∈f.vars,pderiv j (pderiv i f)*X (i+1)*X (j+1))+
      MvPolynomial.C m*(MvPolynomial.C (-1/2:ℝ)*∑i∈f.vars,pderiv i f*nonlinearJetPolynomial i)
  rw [mul_add]
  linear_combination hs

 theorem nonlinearJetPolynomial_full_split (j:ℕ) :
    (∑k∈Finset.range (j+2),MvPolynomial.C ((j+1).choose k:ℝ)*X k*X (j+1-k) : MomentPolynomial)=
      2*X 0*X (j+1)+nonlinearJetPolynomial j := by
  change (∑k∈Finset.range (j+1+1),MvPolynomial.C ((j+1).choose k:ℝ)*X k*X (j+1-k))=_
  rw [Finset.sum_range_succ,Finset.sum_range_eq_add_Ico _ (by omega : 0<j+1),
    Finset.Ico_add_one_right_eq_Icc]
  simp only [Nat.choose_zero_right,Nat.cast_one,map_one,one_mul,Nat.sub_zero,
    Nat.choose_self,Nat.sub_self]
  unfold nonlinearJetPolynomial
  ring

 theorem cellTimeForcing_eq_polynomial (β:ℝ) (μ:ParisiMeasure) (m:ℝ)
    (j:ℕ) (s x:ℝ) : cellTimeForcing β μ m (j+1) s x=
      β^2*eval (fun i=>parisiSpatialJet β μ (i+1) s x)
        (MvPolynomial.C (-1/2:ℝ)*(X (j+2)+MvPolynomial.C (2*m)*X 0*X (j+1)+
          MvPolynomial.C m*nonlinearJetPolynomial j)) := by
  rw [cellTimeForcing_eq]
  have he:=congrArg (eval (fun i=>parisiSpatialJet β μ (i+1) s x))
    (nonlinearJetPolynomial_full_split j)
  simp only [map_sum,map_mul,map_add,eval_C,eval_X] at he
  norm_num only [map_ofNat] at he
  simp only [map_mul,map_add,eval_C,eval_X,zero_add]
  rw [show j+1+1=j+2 by omega,he]
  ring

end FRSB
