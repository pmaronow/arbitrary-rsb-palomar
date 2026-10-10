module

public import FRSB.MomentPolynomials
public import FRSB.FiniteTimeHierarchy

@[expose] public section


/-! Genuine chain-rule calculus for polynomial functions of actual spatial jets. -/
noncomputable section
open Set MeasureTheory MvPolynomial
open scoped Topology BigOperators
namespace FRSB
set_option maxHeartbeats 1000000

/-- A polynomial-valued directional derivative, including infinite jet indices
but only finitely many variables in each polynomial. -/
def polynomialDirection (d : ℕ→MomentPolynomial) :
    Derivation ℝ MomentPolynomial MomentPolynomial := MvPolynomial.mkDerivation ℝ d

 theorem derivation_sum_apply (S:Finset ℕ) (d:ℕ→Derivation ℝ MomentPolynomial MomentPolynomial)
    (f:MomentPolynomial) : (∑i∈S,d i) f=∑i∈S,d i f := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => simp only [Finset.sum_insert hi,Derivation.add_apply,ih]

 theorem polynomialDirection_eq_sum (d : ℕ→MomentPolynomial) (f : MomentPolynomial) :
    polynomialDirection d f = ∑i∈f.vars,d i * pderiv i f := by
  classical
  let D:Derivation ℝ MomentPolynomial MomentPolynomial := ∑i∈f.vars,d i • pderiv i
  have he:polynomialDirection d f=D f := derivation_eq_of_forall_mem_vars (by
    intro i hi
    simp only [polynomialDirection,mkDerivation_X,D]
    have heval: (∑j∈f.vars,d j • pderiv j : Derivation ℝ MomentPolynomial MomentPolynomial) (X i) =
        ∑j∈f.vars,(d j • pderiv j : Derivation ℝ MomentPolynomial MomentPolynomial) (X i) := by
      exact derivation_sum_apply _ _ _
    rw [heval]
    simp [Derivation.smul_apply,pderiv_X,Pi.single_apply,hi])
  rw [he]
  simp only [D]
  have heval: (∑i∈f.vars,d i • pderiv i) f =∑i∈f.vars,(d i • pderiv i) f := by
    exact derivation_sum_apply _ _ _
  rw [heval]
  simp only [Derivation.smul_apply,smul_eq_mul]

 theorem hasDerivAt_eval_polynomialDirection (y : ℕ→ℝ→ℝ) (v : ℕ→ℝ)
    (x : ℝ) (hy:∀i,HasDerivAt (y i) (v i) x) (f : MomentPolynomial) :
    HasDerivAt (fun t=>eval (fun i=>y i t) f)
      (eval (fun i=>y i x) (polynomialDirection (fun i=>MvPolynomial.C (v i)) f)) x := by
  induction f using MvPolynomial.induction_on with
  | C c => simpa only [eval_C,polynomialDirection,derivation_C,map_zero] using hasDerivAt_const x c
  | add f g hf hg =>
    convert hf.add hg using 1
    · funext t; simp only [map_add,Pi.add_apply]
    · simp only [map_add]
  | mul_X f i hf =>
    convert hf.mul (hy i) using 1
    · funext t; simp only [map_mul,eval_X,Pi.mul_apply]
    · simp only [polynomialDirection,Derivation.leibniz,smul_eq_mul,map_add,map_mul,
        mkDerivation_X,eval_C,eval_X]
      ring

 theorem hasDerivAt_eval_chain (y : ℕ→ℝ→ℝ) (v : ℕ→ℝ)
    (x : ℝ) (hy:∀i,HasDerivAt (y i) (v i) x) (f : MomentPolynomial) :
    HasDerivAt (fun t=>eval (fun i=>y i t) f)
      (∑i∈f.vars,eval (fun j=>y j x) (pderiv i f)*v i) x := by
  have hd:=hasDerivAt_eval_polynomialDirection y v x hy f
  rw [polynomialDirection_eq_sum] at hd
  simp only [map_sum,map_mul,eval_C] at hd
  convert hd using 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Formal spatial differentiation shifts each positive-order jet to its successor. -/
def polynomialSpatialDerivative (f : MomentPolynomial) : MomentPolynomial :=
  polynomialDirection (fun i=>MvPolynomial.X (i+1)) f

 theorem hasDerivAt_polynomialJet_spatial (β:ℝ) (μ:ParisiMeasure)
    (f:MomentPolynomial) (s x:ℝ) :
    HasDerivAt (fun y=>eval (fun j=>parisiSpatialJet β μ (j+1) s y) f)
      (eval (fun j=>parisiSpatialJet β μ (j+1) s x) (polynomialSpatialDerivative f)) x := by
  have hd:=hasDerivAt_eval_chain (fun j=>parisiSpatialJet β μ (j+1) s)
    (fun j=>parisiSpatialJet β μ (j+2) s x) x
    (fun j=>hasDerivAt_parisiSpatialJet_succ β μ j s x) f
  unfold polynomialSpatialDerivative
  rw [polynomialDirection_eq_sum]
  simpa only [map_sum,map_mul,eval_X,mul_comm,
    show ∀j:ℕ,j+1+1=j+2 by omega] using hd

end FRSB
