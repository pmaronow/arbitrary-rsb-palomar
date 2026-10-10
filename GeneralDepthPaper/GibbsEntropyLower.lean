module

public import GeneralDepthPaper.GibbsReplicaIntegral

@[expose] public section


/-! Positive finite-volume annealed entropy density for the actual mixed
Hamiltonian. Every expectation and Gaussian identity uses its constructed law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace GeneralDepthPaper
open FourPapersCommon OverlapPaper

theorem integrable_gibbs_energy (ξ : AdmissibleEvenMixture) {n : ℕ}
    (σ : Configuration n) :
    Integrable (fun g : Disorder n=>gibbsWeight 0 g σ*g σ) (disorderLaw ξ n) :=
  (integrable_hamiltonian ξ σ).bdd_mul (continuous_gibbsWeight 0 σ).aestronglyMeasurable
    (.of_forall fun g=>norm_gibbsWeight_zero_le_one g σ)

theorem integrable_gibbsEntropy (ξ : AdmissibleEvenMixture) (n : ℕ) :
    Integrable (fun g : Disorder n=>gibbsEntropy g) (disorderLaw ξ n) := by
  have hi := (integrable_log_partitionFunction ξ (n := n) 0).sub
    (integrable_finsetSum Finset.univ (fun σ _=>integrable_gibbs_energy ξ σ))
  exact hi.congr (.of_forall fun g=>(gibbsEntropy_eq_log_partition_sub_energy g).symm)

theorem integrable_gibbs_spinFlip_penalty (ξ : AdmissibleEvenMixture) {n : ℕ}
    (i : Fin n) (σ : Configuration n) :
    Integrable (fun g : Disorder n=>gibbsWeight 0 g σ*entropyPenalty (spinFlipEnergyGap g i σ))
      (disorderLaw ξ n) :=
  (integrable_entropyPenalty _ (integrable_spinFlipEnergyGap_slice ξ i σ)).bdd_mul
    (continuous_gibbsWeight 0 σ).aestronglyMeasurable
    (.of_forall fun g=>norm_gibbsWeight_zero_le_one g σ)

theorem entropyPenalty_le_gibbs_spinFlip_expectation (ξ : AdmissibleEvenMixture)
    {n : ℕ} (i : Fin n) :
    entropyPenalty (4*ξ.variance) ≤
      ∫ g : Disorder n,∑ σ,gibbsWeight 0 g σ*entropyPenalty (spinFlipEnergyGap g i σ) ∂disorderLaw ξ n := by
  have H := entropyPenalty_integral_ge_of_mean_le _
    (integrable_spinFlipEnergyGap_oneReplica ξ i) (integral_spinFlipEnergyGap_oneReplica_le ξ i)
  rw [integral_oneReplica_of_slices ξ _
    (fun σ=>continuous_entropyPenalty.measurable.comp (measurable_spinFlipEnergyGap_slice i σ))
    (fun σ=>integrable_entropyPenalty _ (integrable_spinFlipEnergyGap_slice ξ i σ))] at H
  exact H

theorem expected_gibbsEntropy_lower_bound (ξ : AdmissibleEvenMixture) (n : ℕ) :
    (n : ℝ)*entropyPenalty (4*ξ.variance) ≤
      ∫ g : Disorder n,gibbsEntropy g ∂disorderLaw ξ n := by
  have hsum : Integrable (fun g : Disorder n=>∑ i : Fin n,∑ σ,
      gibbsWeight 0 g σ*entropyPenalty (spinFlipEnergyGap g i σ)) (disorderLaw ξ n) :=
    integrable_finsetSum _ (fun i _=>integrable_finsetSum _
      (fun σ _=>integrable_gibbs_spinFlip_penalty ξ i σ))
  calc
    _ = ∑ i : Fin n,entropyPenalty (4*ξ.variance) := by simp
    _ ≤ ∑ i : Fin n,∫ g : Disorder n,∑ σ,
        gibbsWeight 0 g σ*entropyPenalty (spinFlipEnergyGap g i σ) ∂disorderLaw ξ n :=
      Finset.sum_le_sum (fun i _=>entropyPenalty_le_gibbs_spinFlip_expectation ξ i)
    _ = ∫ g : Disorder n,∑ i : Fin n,∑ σ,
        gibbsWeight 0 g σ*entropyPenalty (spinFlipEnergyGap g i σ) ∂disorderLaw ξ n := by
      rw [integral_finsetSum _ (fun i _=>integrable_finsetSum _
        (fun σ _=>integrable_gibbs_spinFlip_penalty ξ i σ))]
    _ ≤ _ := integral_mono hsum (integrable_gibbsEntropy ξ n) gibbsEntropy_ge_conditional_penalties

def expectedEntropyDensity (ξ : AdmissibleEvenMixture) (n : ℕ) : ℝ :=
  (∫ g : Disorder n,gibbsEntropy g ∂disorderLaw ξ n)/(n : ℝ)

theorem expectedEntropyDensity_ge_penalty (ξ : AdmissibleEvenMixture) {n : ℕ}
    (hn : 0<n) : entropyPenalty (4*ξ.variance) ≤ expectedEntropyDensity ξ n := by
  have hnR : (0 : ℝ)<(n : ℝ) := by exact_mod_cast hn
  apply (le_div_iff₀ hnR).mpr
  simpa only [mul_comm] using expected_gibbsEntropy_lower_bound ξ n

theorem expectedEntropyDensity_pos (ξ : AdmissibleEvenMixture) {n : ℕ}
    (hn : 0<n) : 0<expectedEntropyDensity ξ n :=
  (entropyPenalty_pos _).trans_le (expectedEntropyDensity_ge_penalty ξ hn)

end GeneralDepthPaper
