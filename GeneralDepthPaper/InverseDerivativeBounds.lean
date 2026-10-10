module

public import GeneralDepthPaper.AnalyticDerivativeBound
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Normed.Operator.Mul

@[expose] public section


/-! Quantitative derivatives of genuine Banach-algebra inversion. These
estimates depend on the actual inverse norm, and have no mass denominator. -/
noncomputable section
open Set Filter
open scoped Topology NNReal ENNReal
namespace GeneralDepthPaper
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [NormOneClass A] [Nontrivial A]
set_option maxSynthPendingDepth 64

theorem norm_iteratedFDeriv_inverse_le (z : Aˣ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n Ring.inverse (z:A)‖ ≤
      (n.factorial:ℝ)*‖((z⁻¹:Aˣ):A)‖^(n+1) := by
  let L : A→L[ℝ] A := ContinuousLinearMap.mul ℝ A ((z⁻¹:Aˣ):A)
  let R : A→L[ℝ] A := (ContinuousLinearMap.mul ℝ A).flip ((z⁻¹:Aˣ):A)
  have hL : ‖L‖≤‖((z⁻¹:Aˣ):A)‖ := ContinuousLinearMap.opNorm_mul_apply_le _ _ _
  have hR : ‖R‖≤‖((z⁻¹:Aˣ):A)‖ := by
    apply R.opNorm_le_bound (norm_nonneg _)
    intro x
    exact (norm_mul_le x _).trans_eq (mul_comm _ _)
  have hs0 : HasFPowerSeriesOnBall (fun x:A=>Ring.inverse (1+x))
      (alternatingGeometricSeries ℝ A) (L 0) 1 := by
    simpa using hasFPowerSeriesOnBall_inverse_one_add ℝ A
  have hs := R.comp_hasFPowerSeriesOnBall hs0.compContinuousLinearMap
  have he : (fun q:A => (R ∘ (fun x:A=>Ring.inverse (1+x)) ∘ L) (q-(z:A)))=
      Ring.inverse := by
    funext q
    change Ring.inverse (1+((z⁻¹:Aˣ):A)*(q-(z:A)))*((z⁻¹:Aˣ):A)=Ring.inverse q
    have hq : (z:A)*(1+((z⁻¹:Aˣ):A)*(q-(z:A)))=q := by
      rw [mul_add,mul_one,←mul_assoc,Units.mul_inv,one_mul]
      abel
    calc
      _ = Ring.inverse ((z:A)*(1+((z⁻¹:Aˣ):A)*(q-(z:A)))) := by
        rw [Ring.inverse_mul (Or.inl z.isUnit),Ring.inverse_unit]
      _ = Ring.inverse q := congrArg Ring.inverse hq
  have ht := hs.comp_sub (z:A)
  rw [zero_add,he] at ht
  refine (norm_iteratedFDeriv_le_factorial_coefficient ht n).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  calc
    ‖R.compFormalMultilinearSeries
        ((alternatingGeometricSeries ℝ A).compContinuousLinearMap L) n‖
      ≤‖R‖*‖((alternatingGeometricSeries ℝ A).compContinuousLinearMap L) n‖ :=
        R.norm_compContinuousMultilinearMap_le _
    _≤‖((z⁻¹:Aˣ):A)‖*(‖alternatingGeometricSeries ℝ A n‖*‖L‖^n) := by
      exact mul_le_mul hR ((alternatingGeometricSeries ℝ A n).norm_compContinuousLinearMap_le
        (fun _=>L) |>.trans_eq (by simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]))
        (norm_nonneg _) (norm_nonneg _)
    _≤‖((z⁻¹:Aˣ):A)‖*(1*‖((z⁻¹:Aˣ):A)‖^n) := by
      rw [alternatingGeometricSeries_apply_norm]
      gcongr
    _=‖((z⁻¹:Aˣ):A)‖^(n+1) := by rw [pow_succ]; ring

end GeneralDepthPaper
