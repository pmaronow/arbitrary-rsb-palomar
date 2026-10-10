module

public import GeneralDepthPaper.GibbsSpinFlipMean
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section


/-! Actual integration over the annealed disorder-and-one-replica law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace GeneralDepthPaper
open FourPapersCommon OverlapPaper

theorem integral_gibbsLaw {n : ℕ} (g : Disorder n) (f : Configuration n→ℝ) :
    (∫ σ,f σ ∂gibbsLaw 0 g)=∑ σ,gibbsWeight 0 g σ*f σ := by
  rw [gibbsLaw,PMF.integral_eq_sum]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [gibbsPMF,PMF.ofFintype_apply,ENNReal.toReal_ofReal (gibbsWeight_pos 0 g σ).le,
    smul_eq_mul]

theorem integrable_oneReplica_of_slices {n : ℕ} (ξ : AdmissibleEvenMixture)
    (f : Disorder n×Configuration n→ℝ)
    (hm : ∀ σ,Measurable (fun g=>f (g,σ)))
    (hi : ∀ σ,Integrable (fun g=>f (g,σ)) (disorderLaw ξ n)) :
    Integrable f (oneReplicaLaw ξ n) := by
  have hmeas : Measurable f := measurable_from_prod_countable_left hm
  unfold oneReplicaLaw
  apply (Measure.integrable_compProd_iff hmeas.aestronglyMeasurable).mpr
  refine ⟨.of_forall (fun g=>Integrable.of_finite),?_⟩
  simp_rw [gibbsKernel_apply,integral_gibbsLaw]
  apply integrable_finsetSum
  intro σ _
  exact (hi σ).norm.bdd_mul (continuous_gibbsWeight 0 σ).aestronglyMeasurable
    (.of_forall fun g=>norm_gibbsWeight_zero_le_one g σ)

theorem integral_oneReplica_of_slices {n : ℕ} (ξ : AdmissibleEvenMixture)
    (f : Disorder n×Configuration n→ℝ)
    (hm : ∀ σ,Measurable (fun g=>f (g,σ)))
    (hi : ∀ σ,Integrable (fun g=>f (g,σ)) (disorderLaw ξ n)) :
    (∫ z,f z ∂oneReplicaLaw ξ n)=
      ∫ g : Disorder n,∑ σ,gibbsWeight 0 g σ*f (g,σ) ∂disorderLaw ξ n := by
  have H := Measure.integral_compProd (integrable_oneReplica_of_slices ξ f hm hi)
  simpa only [oneReplicaLaw,gibbsKernel_apply,integral_gibbsLaw] using H

theorem measurable_spinFlipEnergyGap_slice {n : ℕ} (i : Fin n) (σ : Configuration n) :
    Measurable (fun g : Disorder n=>spinFlipEnergyGap g i σ) := by
  unfold spinFlipEnergyGap
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Configuration n=>ℝ) σ).measurable.sub
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Configuration n=>ℝ) (flipSpin i σ)).measurable

theorem integrable_spinFlipEnergyGap_slice {n : ℕ} (ξ : AdmissibleEvenMixture)
    (i : Fin n) (σ : Configuration n) :
    Integrable (fun g : Disorder n=>spinFlipEnergyGap g i σ) (disorderLaw ξ n) :=
  ((integrable_hamiltonian ξ σ).sub (integrable_hamiltonian ξ (flipSpin i σ))).congr
    (.of_forall fun g=>rfl)

theorem integrable_spinFlipEnergyGap_oneReplica {n : ℕ} (ξ : AdmissibleEvenMixture)
    (i : Fin n) :
    Integrable (fun z : Disorder n×Configuration n=>spinFlipEnergyGap z.1 i z.2) (oneReplicaLaw ξ n) :=
  integrable_oneReplica_of_slices ξ _ (measurable_spinFlipEnergyGap_slice i)
    (integrable_spinFlipEnergyGap_slice ξ i)

theorem integral_spinFlipEnergyGap_oneReplica_le {n : ℕ} (ξ : AdmissibleEvenMixture)
    (i : Fin n) :
    (∫ z : Disorder n×Configuration n,spinFlipEnergyGap z.1 i z.2 ∂oneReplicaLaw ξ n) ≤
      4*ξ.variance := by
  rw [integral_oneReplica_of_slices ξ _ (measurable_spinFlipEnergyGap_slice i)
    (integrable_spinFlipEnergyGap_slice ξ i)]
  exact integral_gibbs_mean_spinFlip_gap_le ξ i

end GeneralDepthPaper
