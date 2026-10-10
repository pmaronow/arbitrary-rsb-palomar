module

public import GeneralDepthPaper.SpinFlipCovariance

@[expose] public section


/-! Actual annealed one-spin energy-gap bound, from Gaussian integration by
parts and the exact mixed Hamiltonian covariance. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace GeneralDepthPaper
open FourPapersCommon OverlapPaper

theorem norm_gibbsWeight_zero_le_one {n : ℕ} (g : Disorder n) (σ : Configuration n) :
    ‖gibbsWeight 0 g σ‖ ≤ 1 := by
  rw [Real.norm_eq_abs,abs_of_pos (gibbsWeight_pos 0 g σ)]
  exact (gibbsFiniteProbability g).weight_le_one σ

theorem integrable_gibbsWeight_zero (ξ : AdmissibleEvenMixture) {n : ℕ}
    (σ : Configuration n) : Integrable (fun g : Disorder n=>gibbsWeight 0 g σ) (disorderLaw ξ n) :=
  (integrable_const (1 : ℝ)).mono' (continuous_gibbsWeight 0 σ).aestronglyMeasurable
    (.of_forall fun g=>norm_gibbsWeight_zero_le_one g σ)

theorem integrable_gibbs_spinFlip_gap (ξ : AdmissibleEvenMixture) {n : ℕ}
    (i : Fin n) (σ : Configuration n) :
    Integrable (fun g : Disorder n=>gibbsWeight 0 g σ*spinFlipEnergyGap g i σ) (disorderLaw ξ n) := by
  have hi : Integrable (fun g : Disorder n=>spinFlipEnergyGap g i σ) (disorderLaw ξ n) :=
    (((hamiltonian_memLp_two ξ σ).sub (hamiltonian_memLp_two ξ (flipSpin i σ))).integrable
      (by norm_num)).congr (.of_forall fun g=>rfl)
  exact hi.bdd_mul (continuous_gibbsWeight 0 σ).aestronglyMeasurable
    (.of_forall fun g=>norm_gibbsWeight_zero_le_one g σ)

theorem gibbs_average_abs_le {n : ℕ} (g : Disorder n) (f : Configuration n→ℝ) {C : ℝ}
    (hC : ∀ τ,|f τ| ≤ C) : |∑ τ,gibbsWeight 0 g τ*f τ| ≤ C := by
  calc
    _ ≤ ∑ τ,|gibbsWeight 0 g τ*f τ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ τ,gibbsWeight 0 g τ*C := by
      apply Finset.sum_le_sum
      intro τ _
      rw [abs_mul,abs_of_pos (gibbsWeight_pos 0 g τ)]
      exact mul_le_mul_of_nonneg_left (hC τ) (gibbsWeight_pos 0 g τ).le
    _ = C := by rw [← Finset.sum_mul,sum_gibbsWeight,one_mul]

def spinFlipCovariance {n : ℕ} (ξ : AdmissibleEvenMixture) (i : Fin n)
    (σ τ : Configuration n) : ℝ :=
  (n : ℝ)*(ξ.value (overlap σ τ)-ξ.value (overlap (flipSpin i σ) τ))

def gibbsSpinFlipCorrection {n : ℕ} (ξ : AdmissibleEvenMixture) (i : Fin n)
    (σ : Configuration n) (g : Disorder n) : ℝ :=
  gibbsWeight 0 g σ*(spinFlipCovariance ξ i σ σ-
    ∑ τ,gibbsWeight 0 g τ*spinFlipCovariance ξ i σ τ)

theorem abs_gibbsSpinFlipCorrection_le {n : ℕ} (ξ : AdmissibleEvenMixture)
    (i : Fin n) (σ : Configuration n) (g : Disorder n) :
    |gibbsSpinFlipCorrection ξ i σ g| ≤ gibbsWeight 0 g σ*(4*ξ.variance) := by
  unfold gibbsSpinFlipCorrection
  rw [abs_mul,abs_of_pos (gibbsWeight_pos 0 g σ)]
  apply mul_le_mul_of_nonneg_left _ (gibbsWeight_pos 0 g σ).le
  calc
    _ ≤ |spinFlipCovariance ξ i σ σ|+|∑ τ,gibbsWeight 0 g τ*spinFlipCovariance ξ i σ τ| := abs_sub _ _
    _ ≤ 2*ξ.variance+2*ξ.variance := add_le_add
      (abs_spinFlip_covariance_difference_le ξ i σ σ)
      (gibbs_average_abs_le g _ (fun τ=>abs_spinFlip_covariance_difference_le ξ i σ τ))
    _ = _ := by ring

theorem continuous_gibbsSpinFlipCorrection {n : ℕ} (ξ : AdmissibleEvenMixture)
    (i : Fin n) (σ : Configuration n) : Continuous (gibbsSpinFlipCorrection ξ i σ) := by
  unfold gibbsSpinFlipCorrection
  apply (continuous_gibbsWeight 0 σ).mul
  apply continuous_const.sub
  apply continuous_finset_sum
  intro τ _
  exact (continuous_gibbsWeight 0 τ).mul continuous_const

theorem integrable_gibbsSpinFlipCorrection {n : ℕ} (ξ : AdmissibleEvenMixture)
    (i : Fin n) (σ : Configuration n) :
    Integrable (gibbsSpinFlipCorrection ξ i σ) (disorderLaw ξ n) := by
  apply ((integrable_gibbsWeight_zero ξ σ).mul_const (4*ξ.variance)).mono'
    (continuous_gibbsSpinFlipCorrection ξ i σ).aestronglyMeasurable
  exact .of_forall (fun g=>by rw [Real.norm_eq_abs]; exact abs_gibbsSpinFlipCorrection_le ξ i σ g)

theorem integral_gibbs_spinFlip_gap_le {n : ℕ} (ξ : AdmissibleEvenMixture)
    (i : Fin n) (σ : Configuration n) :
    (∫ g : Disorder n,gibbsWeight 0 g σ*spinFlipEnergyGap g i σ ∂disorderLaw ξ n) ≤
      4*ξ.variance*(∫ g : Disorder n,gibbsWeight 0 g σ ∂disorderLaw ξ n) := by
  rw [gibbs_spinFlip_integration_by_parts]
  change (∫ g,gibbsSpinFlipCorrection ξ i σ g ∂disorderLaw ξ n) ≤ _
  calc
    _ ≤ ∫ g : Disorder n,gibbsWeight 0 g σ*(4*ξ.variance) ∂disorderLaw ξ n :=
      integral_mono (integrable_gibbsSpinFlipCorrection ξ i σ)
        ((integrable_gibbsWeight_zero ξ σ).mul_const _) (fun g=>
          (le_abs_self _).trans (abs_gibbsSpinFlipCorrection_le ξ i σ g))
    _ = _ := by rw [integral_mul_const]; ring

theorem integral_gibbs_mean_spinFlip_gap_le {n : ℕ} (ξ : AdmissibleEvenMixture)
    (i : Fin n) :
    (∫ g : Disorder n,∑ σ,gibbsWeight 0 g σ*spinFlipEnergyGap g i σ ∂disorderLaw ξ n) ≤
      4*ξ.variance := by
  rw [integral_finsetSum _ (fun σ _=>integrable_gibbs_spinFlip_gap ξ i σ)]
  calc
    _ ≤ ∑ σ,4*ξ.variance*(∫ g : Disorder n,gibbsWeight 0 g σ ∂disorderLaw ξ n) :=
      Finset.sum_le_sum (fun σ _=>integral_gibbs_spinFlip_gap_le ξ i σ)
    _ = 4*ξ.variance*(∫ g : Disorder n,∑ σ,gibbsWeight 0 g σ ∂disorderLaw ξ n) := by
      rw [integral_finsetSum _ (fun σ _=>integrable_gibbsWeight_zero ξ σ),Finset.mul_sum]
    _ = 4*ξ.variance := by simp only [sum_gibbsWeight,integral_const,probReal_univ,one_smul,mul_one]

end GeneralDepthPaper
