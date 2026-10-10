module

public import GeneralDepthPaper.GibbsWeightCalculus
public import Lemmas.Cavity.Interpolation
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section


/-! Actual single-spin covariance differences and Gaussian integration by
parts for the constructed Hamiltonian and Gibbs weights. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace ContDiff
namespace GeneralDepthPaper
open FourPapersCommon OverlapPaper PhysLean.Probability.GaussianIBP
open PhysLean.Probability.GaussianIBP.ProbabilityTheory

theorem mixture_value_difference_le (ξ : AdmissibleEvenMixture) {r q : ℝ}
    (hr : r∈Icc (-1 : ℝ) 1) (hq : q∈Icc (-1 : ℝ) 1) :
    |ξ.value r-ξ.value q| ≤ ξ.variance*|r-q| := by
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x hx=>(ξ.hasDerivAt_value_unit hx).hasDerivWithinAt)
      (fun x hx=>by simpa only [Real.norm_eq_abs] using ξ.abs_first_le_variance (abs_le.mpr hx))
      (convex_Icc (-1 : ℝ) 1) hq hr

theorem overlap_spinFlip {n : ℕ} (i : Fin n) (σ τ : Configuration n) :
    overlap (flipSpin i σ) τ=overlap σ τ-(2/(n : ℝ))*spin (σ i)*spin (τ i) := by
  have H := SpinGlass.AT.overlap_flipSite_left i σ τ
  have he (a b : Configuration n) : SpinGlass.overlap n a b=overlap a b := by
    simp only [SpinGlass.overlap,overlap,SpinGlass.spin,spin,div_eq_mul_inv]
    ring
  simp only [he] at H
  exact H

theorem abs_overlap_spinFlip_difference {n : ℕ} (i : Fin n) (σ τ : Configuration n) :
    |overlap σ τ-overlap (flipSpin i σ) τ|=2/(n : ℝ) := by
  rw [overlap_spinFlip]
  have he : overlap σ τ-(overlap σ τ-2/(n : ℝ)*spin (σ i)*spin (τ i))=
      2/(n : ℝ)*spin (σ i)*spin (τ i) := by ring
  rw [he,abs_mul,abs_mul,abs_spin,abs_spin,mul_one,mul_one,abs_of_nonneg (by positivity)]

theorem abs_spinFlip_covariance_difference_le (ξ : AdmissibleEvenMixture) {n : ℕ}
    (i : Fin n) (σ τ : Configuration n) :
    |(n : ℝ)*(ξ.value (overlap σ τ)-ξ.value (overlap (flipSpin i σ) τ))| ≤ 2*ξ.variance := by
  have hn : 0<n := Nat.pos_of_ne_zero (fun hh=>by subst n; exact Fin.elim0 i)
  have hnR : (0 : ℝ)<(n : ℝ) := by exact_mod_cast hn
  rw [abs_mul,abs_of_pos hnR]
  calc
    _ ≤ (n : ℝ)*(ξ.variance*|overlap σ τ-overlap (flipSpin i σ) τ|) :=
      mul_le_mul_of_nonneg_left
        (mixture_value_difference_le ξ (overlap_mem_unit σ τ) (overlap_mem_unit (flipSpin i σ) τ)) hnR.le
    _ = 2*ξ.variance := by rw [abs_overlap_spinFlip_difference]; field_simp

theorem inner_spinFlip_basis {n : ℕ} (g : Disorder n) (i : Fin n) (σ : Configuration n) :
    ⟪g,SpinGlass.std_basis n σ-SpinGlass.std_basis n (flipSpin i σ)⟫=spinFlipEnergyGap g i σ := by
  rw [inner_sub_right,real_inner_comm (SpinGlass.std_basis n σ) g,
    real_inner_comm (SpinGlass.std_basis n (flipSpin i σ)) g,SpinGlass.inner_std_basis_apply,
    SpinGlass.inner_std_basis_apply]
  rfl

theorem covOp_spinFlip_basis_apply (ξ : AdmissibleEvenMixture) {n : ℕ}
    (i : Fin n) (σ τ : Configuration n) :
    (letI : MeasureSpace (Disorder n) := ⟨disorderLaw ξ n⟩
     letI : IsProbabilityMeasure (volume : Measure (Disorder n)) := disorderLaw_isProbabilityMeasure ξ n
     covOp (canonicalMixedDisorder ξ n).hU
       (SpinGlass.std_basis n σ-SpinGlass.std_basis n (flipSpin i σ)) τ)=
      (n : ℝ)*(ξ.value (overlap σ τ)-ξ.value (overlap (flipSpin i σ) τ)) := by
  letI : MeasureSpace (Disorder n) := ⟨disorderLaw ξ n⟩
  letI : IsProbabilityMeasure (volume : Measure (Disorder n)) := disorderLaw_isProbabilityMeasure ξ n
  have H := gaussian_covariance_clm (canonicalMixedDisorder ξ n).hU (SpinGlass.evalCLM n τ)
    (SpinGlass.std_basis n σ-SpinGlass.std_basis n (flipSpin i σ))
  change (∫ g : Disorder n,⟪g,SpinGlass.std_basis n σ-SpinGlass.std_basis n (flipSpin i σ)⟫*g τ
    ∂disorderLaw ξ n)=_ at H
  change (SpinGlass.evalCLM n τ) (covOp (canonicalMixedDisorder ξ n).hU
    (SpinGlass.std_basis n σ-SpinGlass.std_basis n (flipSpin i σ)))=_
  rw [← H]
  simp_rw [inner_spinFlip_basis,spinFlipEnergyGap,sub_mul]
  have hi1 : Integrable (fun g : Disorder n=>g σ*g τ) (disorderLaw ξ n) := by
    exact ((hamiltonian_memLp_two ξ σ).integrable_mul (hamiltonian_memLp_two ξ τ)).congr
      (.of_forall fun g=>rfl)
  have hi2 : Integrable (fun g : Disorder n=>g (flipSpin i σ)*g τ) (disorderLaw ξ n) := by
    exact ((hamiltonian_memLp_two ξ (flipSpin i σ)).integrable_mul (hamiltonian_memLp_two ξ τ)).congr
      (.of_forall fun g=>rfl)
  rw [integral_sub hi1 hi2]
  change (∫ g : Disorder n,hamiltonian g σ*hamiltonian g τ ∂disorderLaw ξ n)-
    (∫ g : Disorder n,hamiltonian g (flipSpin i σ)*hamiltonian g τ ∂disorderLaw ξ n)=_
  rw [integral_hamiltonian_product,integral_hamiltonian_product]
  ring

theorem gibbs_spinFlip_integration_by_parts (ξ : AdmissibleEvenMixture) {n : ℕ}
    (i : Fin n) (σ : Configuration n) :
    (∫ g : Disorder n,gibbsWeight 0 g σ*spinFlipEnergyGap g i σ ∂disorderLaw ξ n)=
    ∫ g : Disorder n,gibbsWeight 0 g σ*
      ((n : ℝ)*(ξ.value (overlap σ σ)-ξ.value (overlap (flipSpin i σ) σ))-
      ∑ τ,gibbsWeight 0 g τ*((n : ℝ)*(ξ.value (overlap σ τ)-ξ.value (overlap (flipSpin i σ) τ))))
      ∂disorderLaw ξ n := by
  letI : MeasureSpace (Disorder n) := ⟨disorderLaw ξ n⟩
  letI : IsProbabilityMeasure (volume : Measure (Disorder n)) := disorderLaw_isProbabilityMeasure ξ n
  have H := gaussian_integration_by_parts_hilbert_cov_op (canonicalMixedDisorder ξ n).hU
    (SpinGlass.std_basis n σ-SpinGlass.std_basis n (flipSpin i σ))
    ((contDiff_gibbsWeight_zero σ).of_le (by norm_num)) (gibbsWeight_zero_moderateGrowth σ)
  change (∫ g : Disorder n,⟪g,SpinGlass.std_basis n σ-SpinGlass.std_basis n (flipSpin i σ)⟫*
    gibbsWeight 0 g σ ∂disorderLaw ξ n)=_ at H
  calc
    _ = ∫ g : Disorder n,⟪g,SpinGlass.std_basis n σ-SpinGlass.std_basis n (flipSpin i σ)⟫*
        gibbsWeight 0 g σ ∂disorderLaw ξ n := by
      apply integral_congr_ae
      exact .of_forall (fun g=>by dsimp only; rw [inner_spinFlip_basis,mul_comm])
    _ = _ := H.trans (by simp_rw [fderiv_gibbsWeight_zero_apply,covOp_spinFlip_basis_apply,
      canonicalMixedDisorder_U,id_eq])

end GeneralDepthPaper
