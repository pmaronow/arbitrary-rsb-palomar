module

public import FRSB.FiniteTimeHierarchy
public import FRSB.ItoSquareTest

@[expose] public section


/-! Exact differentiated finite-cell generator identities for the actual
positive spatial jets. -/
noncomputable section
open Set Paper
namespace FRSB
set_option maxHeartbeats 1000000

 theorem cellTimeForcing_two (β : ℝ) (μ : ParisiMeasure) (m s x : ℝ) :
    cellTimeForcing β μ m 2 s x = -(β^2/2)*
      (parisiSpatialJet β μ 4 s x + 2*m*(parisiSpatialJet β μ 1 s x*
        parisiSpatialJet β μ 3 s x+parisiSpatialJet β μ 2 s x^2)) := by
  rw [cellTimeForcing_eq]
  norm_num [Finset.sum_range_succ,Nat.choose]
  ring_nf
  simp

 theorem cellTimeForcing_three (β : ℝ) (μ : ParisiMeasure) (m s x : ℝ) :
    cellTimeForcing β μ m 3 s x = -(β^2/2)*
      (parisiSpatialJet β μ 5 s x + 2*m*(parisiSpatialJet β μ 1 s x*
        parisiSpatialJet β μ 4 s x+3*parisiSpatialJet β μ 2 s x*parisiSpatialJet β μ 3 s x)) := by
  rw [cellTimeForcing_eq]
  norm_num [Finset.sum_range_succ,Nat.choose]
  ring_nf
  simp

 theorem cellTimeForcing_four (β : ℝ) (μ : ParisiMeasure) (m s x : ℝ) :
    cellTimeForcing β μ m 4 s x = -(β^2/2)*
      (parisiSpatialJet β μ 6 s x + 2*m*(parisiSpatialJet β μ 1 s x*
        parisiSpatialJet β μ 5 s x+4*parisiSpatialJet β μ 2 s x*parisiSpatialJet β μ 4 s x+
          3*parisiSpatialJet β μ 3 s x^2)) := by
  rw [cellTimeForcing_eq]
  norm_num [Finset.sum_range_succ,Nat.choose]
  ring_nf
  simp

 theorem cellTimeForcing_five (β : ℝ) (μ : ParisiMeasure) (m s x : ℝ) :
    cellTimeForcing β μ m 5 s x = -(β^2/2)*
      (parisiSpatialJet β μ 7 s x + 2*m*(parisiSpatialJet β μ 1 s x*
        parisiSpatialJet β μ 6 s x+5*parisiSpatialJet β μ 2 s x*parisiSpatialJet β μ 5 s x+
          10*parisiSpatialJet β μ 3 s x*parisiSpatialJet β μ 4 s x)) := by
  rw [cellTimeForcing_eq]
  norm_num [Finset.sum_range_succ,Nat.choose]
  ring_nf
  simp

 theorem curvature_square_generator_algebra (β : ℝ) (μ : ParisiMeasure)
    (m a v s x : ℝ) :
    2*parisiSpatialJet β μ 2 s x*
        (cellTimeForcing β μ m 2 s x+parisiSpatialJet β μ 3 s x*(β^2*a*v)+
          (1/2:ℝ)*parisiSpatialJet β μ 4 s x*β^2)+β^2*parisiSpatialJet β μ 3 s x^2 -
      β^2*(parisiSpatialJet β μ 3 s x^2-2*a*parisiSpatialJet β μ 2 s x^3) =
    2*β^2*((a-m)*parisiSpatialJet β μ 2 s x^3+
      parisiSpatialJet β μ 2 s x*parisiSpatialJet β μ 3 s x*
        (a*v-m*parisiSpatialJet β μ 1 s x)) := by
  rw [cellTimeForcing_two]
  ring

 theorem curvature_square_generator_error (β : ℝ) (μ : ParisiMeasure)
    (m a v s x eps K : ℝ) (ha:a∈Icc (0:ℝ) 1) (_heps:0≤eps) (hK:0≤K)
    (hgrad:‖v-parisiSpatialJet β μ 1 s x‖≤eps)
    (hB:‖parisiSpatialJet β μ 1 s x‖≤1)
    (hC:‖parisiSpatialJet β μ 2 s x‖≤1)
    (hD:‖parisiSpatialJet β μ 3 s x‖≤K) :
    ‖2*parisiSpatialJet β μ 2 s x*
        (cellTimeForcing β μ m 2 s x+parisiSpatialJet β μ 3 s x*(β^2*a*v)+
          (1/2:ℝ)*parisiSpatialJet β μ 4 s x*β^2)+β^2*parisiSpatialJet β μ 3 s x^2 -
      β^2*(parisiSpatialJet β μ 3 s x^2-2*a*parisiSpatialJet β μ 2 s x^3)‖ ≤
      2*β^2*((1+K)*|a-m|+K*eps) := by
  have htransport:‖a*v-m*parisiSpatialJet β μ 1 s x‖≤|a-m|+eps := by
    have he:a*v-m*parisiSpatialJet β μ 1 s x =
        (a-m)*parisiSpatialJet β μ 1 s x+a*(v-parisiSpatialJet β μ 1 s x) := by ring
    rw [he]
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_mul,Real.norm_eq_abs a,abs_of_nonneg ha.1]
    exact (add_le_add (by simpa only [mul_one,Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_left hB (norm_nonneg (a-m)))
      ((mul_le_mul ha.2 hgrad (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)))
  rw [curvature_square_generator_algebra,norm_mul,norm_mul,
    show ‖(2:ℝ)‖=2 by norm_num,Real.norm_of_nonneg (sq_nonneg β)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_pow,norm_mul,norm_mul]
  have hcube:=pow_le_one₀ (norm_nonneg _) hC (n:=3)
  have hfirst:‖a-m‖*‖parisiSpatialJet β μ 2 s x‖^3≤|a-m| := by
    simpa only [mul_one,Real.norm_eq_abs] using mul_le_mul_of_nonneg_left hcube (norm_nonneg (a-m))
  have hsecond:‖parisiSpatialJet β μ 2 s x‖*‖parisiSpatialJet β μ 3 s x‖*
      ‖a*v-m*parisiSpatialJet β μ 1 s x‖≤K*(|a-m|+eps) := by
    apply mul_le_mul ((mul_le_mul hC hD (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))
      htransport (norm_nonneg _)
    exact hK
  exact (add_le_add hfirst hsecond).trans_eq (by ring)

end FRSB
