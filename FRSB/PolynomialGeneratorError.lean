module

public import FRSB.PolynomialJetFields

@[expose] public section


/-! Actual polynomial generator perturbation on a fixed optimal state. -/
noncomputable section
open Set MvPolynomial Paper
open scoped Topology
namespace FRSB
set_option maxHeartbeats 1000000

 theorem polynomial_generator_drift_error (β:ℝ) (μ:ParisiMeasure) (m a v:ℝ)
    (f:MomentPolynomial) (t x eps:ℝ) (ha:a∈Icc (0:ℝ) 1) (heps:0≤eps)
    (hclose:‖v-parisiSpatialJet β μ 1 t x‖≤eps)
    (hB:‖parisiSpatialJet β μ 1 t x‖≤1) :
    ‖β^2*polynomialJetField β μ (polynomialTimeDerivative m f) t x+
      polynomialJetField β μ (polynomialSpatialDerivative f) t x*(β^2*a*v)+
      (1/2:ℝ)*polynomialJetField β μ
        (polynomialSpatialDerivative (polynomialSpatialDerivative f)) t x*β^2-
      β^2*(polynomialJetField β μ (momentDrift0 f) t x+
        a*polynomialJetField β μ (momentDrift1 f) t x)‖ ≤
    β^2*((uniformPolynomialMomentBound β (momentDrift1 f)+
      uniformPolynomialMomentBound β (polynomialSpatialDerivative f))*|a-m|+
        uniformPolynomialMomentBound β (polynomialSpatialDerivative f)*eps) := by
  have hid:=polynomialJetField_generator_identity β μ m f t x
  have hdecomp : β^2*polynomialJetField β μ (polynomialTimeDerivative m f) t x+
      polynomialJetField β μ (polynomialSpatialDerivative f) t x*(β^2*a*v)+
      (1/2:ℝ)*polynomialJetField β μ
        (polynomialSpatialDerivative (polynomialSpatialDerivative f)) t x*β^2-
      β^2*(polynomialJetField β μ (momentDrift0 f) t x+
        a*polynomialJetField β μ (momentDrift1 f) t x)=
      β^2*((m-a)*polynomialJetField β μ (momentDrift1 f) t x+
        (a*v-m*parisiSpatialJet β μ 1 t x)*
          polynomialJetField β μ (polynomialSpatialDerivative f) t x) := by
    linear_combination hid
  have hd:‖a*v-m*parisiSpatialJet β μ 1 t x‖≤|a-m|+eps := by
    rw [show a*v-m*parisiSpatialJet β μ 1 t x=
      (a-m)*parisiSpatialJet β μ 1 t x+a*(v-parisiSpatialJet β μ 1 t x) by ring]
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_mul,Real.norm_of_nonneg ha.1,Real.norm_eq_abs]
    apply add_le_add
    · exact (mul_le_mul_of_nonneg_left hB (abs_nonneg _)).trans_eq (mul_one _)
    · exact (mul_le_mul ha.2 hclose (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  rw [hdecomp,norm_mul,Real.norm_of_nonneg (sq_nonneg β)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg β)
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_mul,Real.norm_eq_abs,abs_sub_comm m a]
  apply (add_le_add
    (mul_le_mul_of_nonneg_left (norm_polynomialJetField_le_uniform β μ (momentDrift1 f) t x)
      (abs_nonneg _))
    (mul_le_mul hd (norm_polynomialJetField_le_uniform β μ (polynomialSpatialDerivative f) t x)
      (norm_nonneg _) (add_nonneg (abs_nonneg _) heps))).trans_eq
  ring

end FRSB
