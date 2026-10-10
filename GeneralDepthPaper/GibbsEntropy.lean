module

public import OverlapPaper.ReplicaProcess
public import FourPapersCommon.BinaryConditionalEntropy
public import FourPapersCommon.EntropyPenalty

@[expose] public section


/-! Literal finite Gibbs entropy and one-spin conditional entropy from the
paper's actual Hamiltonian, without thermodynamic assumptions. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace GeneralDepthPaper
open FourPapersCommon OverlapPaper

def gibbsFiniteProbability {n : ℕ} (g : Disorder n) : StrictFiniteProbability (Configuration n) :=
  ⟨gibbsWeight 0 g,gibbsWeight_pos 0 g,sum_gibbsWeight 0 g⟩

def gibbsEntropy {n : ℕ} (g : Disorder n) : ℝ := (gibbsFiniteProbability g).entropy

def spinFlipEnergyGap {n : ℕ} (g : Disorder n) (i : Fin n) (σ : Configuration n) : ℝ :=
  g σ-g (flipSpin i σ)

theorem gibbsEntropy_eq_log_partition_sub_energy {n : ℕ} (g : Disorder n) :
    gibbsEntropy g = Real.log (partitionFunction 0 g)-∑ σ,gibbsWeight 0 g σ*g σ := by
  have hlog (σ : Configuration n) : Real.log (gibbsWeight 0 g σ) =
      g σ-Real.log (partitionFunction 0 g) := by
    unfold gibbsWeight totalHamiltonian hamiltonian
    simp only [zero_mul,add_zero]
    rw [Real.log_div (Real.exp_ne_zero _) (partitionFunction_pos 0 g).ne',Real.log_exp]
  unfold gibbsEntropy StrictFiniteProbability.entropy gibbsFiniteProbability
  simp only [hlog,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,sum_gibbsWeight,mul_one,one_mul]
  ring

theorem fullConditional_gibbs_eq {n : ℕ} (g : Disorder n) (i : Fin n) (σ : Configuration n) :
    fullConditional (gibbsFiniteProbability g) i σ =
      (1+Real.exp (-spinFlipEnergyGap g i σ))⁻¹ := by
  unfold fullConditional gibbsFiniteProbability
  simp only [gibbsWeight,totalHamiltonian,hamiltonian,zero_mul,add_zero]
  rw [← add_div]
  have he : Real.exp (-spinFlipEnergyGap g i σ)=Real.exp (g (flipSpin i σ))/Real.exp (g σ) := by
    rw [spinFlipEnergyGap,neg_sub,Real.exp_sub]
  rw [he]
  field_simp [Real.exp_ne_zero (g σ),Real.exp_ne_zero (g (flipSpin i σ)),
    (add_pos (Real.exp_pos (g σ)) (Real.exp_pos (g (flipSpin i σ)))).ne',
    (partitionFunction_pos 0 g).ne']

theorem neg_log_fullConditional_gibbs {n : ℕ} (g : Disorder n) (i : Fin n) (σ : Configuration n) :
    -Real.log (fullConditional (gibbsFiniteProbability g) i σ) =
      entropyPenalty (spinFlipEnergyGap g i σ) := by
  rw [fullConditional_gibbs_eq,Real.log_inv,neg_neg]
  rfl

theorem gibbsEntropy_ge_conditional_penalties {n : ℕ} (g : Disorder n) :
    (∑ i : Fin n,∑ σ,gibbsWeight 0 g σ*entropyPenalty (spinFlipEnergyGap g i σ)) ≤ gibbsEntropy g := by
  have hh := entropy_ge_sum_full_conditional (gibbsFiniteProbability g)
  rw [← Finset.sum_neg_distrib] at hh
  simp only [← Finset.sum_neg_distrib,← mul_neg,neg_log_fullConditional_gibbs] at hh
  exact hh

def oneReplicaLaw (ξ : AdmissibleEvenMixture) (n : ℕ) : Measure (Disorder n × Configuration n) :=
  disorderLaw ξ n ⊗ₘ gibbsKernel n 0

instance oneReplicaLaw_isProbabilityMeasure (ξ : AdmissibleEvenMixture) (n : ℕ) :
    IsProbabilityMeasure (oneReplicaLaw ξ n) := by unfold oneReplicaLaw; infer_instance

end GeneralDepthPaper
