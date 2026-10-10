module

public import GeneralDepthPaper.GibbsEntropy
public import OverlapPaper.MixedDisorderRealization
public import Lemmas.SpinGlass.Calculus

@[expose] public section


/-! Genuine differentiability and bounded derivative of the actual positive
Hamiltonian Gibbs weights, for the Gaussian integration by parts. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace Topology ContDiff
namespace GeneralDepthPaper
open OverlapPaper

theorem gibbsWeight_eq_negative_energy {n : ℕ} (g : Disorder n) (σ : Configuration n) :
    gibbsWeight 0 g σ=SpinGlass.gibbs_pmf n (-g) σ := by
  simp [gibbsWeight,totalHamiltonian,hamiltonian,partitionFunction,
    SpinGlass.gibbs_pmf,SpinGlass.Z,PiLp.neg_apply]

theorem contDiff_gibbsWeight_zero {n : ℕ} (σ : Configuration n) :
    ContDiff ℝ ∞ (fun g : Disorder n => gibbsWeight 0 g σ) := by
  simp_rw [gibbsWeight_eq_negative_energy]
  exact (SpinGlass.contDiff_gibbs_pmf n σ).comp contDiff_neg

theorem fderiv_gibbsWeight_zero_apply {n : ℕ} (g v : Disorder n) (σ : Configuration n) :
    fderiv ℝ (fun z : Disorder n => gibbsWeight 0 z σ) g v =
      gibbsWeight 0 g σ*(v σ-∑ τ,gibbsWeight 0 g τ*v τ) := by
  have hh := (SpinGlass.hasFDerivAt_gibbs_pmf n (H := -g) σ).comp g (hasFDerivAt_id g).neg
  have he : (fun z : Disorder n => gibbsWeight 0 z σ) =
      fun z => SpinGlass.gibbs_pmf n (-z) σ := by
    funext z; exact gibbsWeight_eq_negative_energy z σ
  rw [he]
  change (fderiv ℝ ((fun z => SpinGlass.gibbs_pmf n z σ) ∘ Neg.neg) g) v = _
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.neg_apply,ContinuousLinearMap.id_apply]
  rw [← (SpinGlass.hasFDerivAt_gibbs_pmf n (H := -g) σ).fderiv]
  rw [SpinGlass.fderiv_gibbs_pmf_apply]
  simp only [PiLp.neg_apply,← gibbsWeight_eq_negative_energy,mul_neg,Finset.sum_neg_distrib]
  ring

theorem abs_gibbs_average_le_norm {n : ℕ} (g v : Disorder n) :
    |∑ τ,gibbsWeight 0 g τ*v τ| ≤ ‖v‖ := by
  calc
    _ ≤ ∑ τ,|gibbsWeight 0 g τ*v τ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ τ,gibbsWeight 0 g τ*‖v‖ := by
      apply Finset.sum_le_sum
      intro τ _
      rw [abs_mul,abs_of_pos (gibbsWeight_pos 0 g τ)]
      exact mul_le_mul_of_nonneg_left (SpinGlass.abs_apply_le_norm n v τ) (gibbsWeight_pos 0 g τ).le
    _ = _ := by rw [← Finset.sum_mul,sum_gibbsWeight,one_mul]

theorem norm_fderiv_gibbsWeight_zero_le {n : ℕ} (g : Disorder n) (σ : Configuration n) :
    ‖fderiv ℝ (fun z : Disorder n => gibbsWeight 0 z σ) g‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  rw [fderiv_gibbsWeight_zero_apply,Real.norm_eq_abs,abs_mul,abs_of_pos (gibbsWeight_pos 0 g σ)]
  have hp : gibbsWeight 0 g σ ≤ 1 := (gibbsFiniteProbability g).weight_le_one σ
  have ha : |v σ-∑ τ,gibbsWeight 0 g τ*v τ| ≤ 2*‖v‖ := by
    calc
      _ ≤ |v σ|+|∑ τ,gibbsWeight 0 g τ*v τ| := abs_sub _ _
      _ ≤ ‖v‖+‖v‖ := add_le_add (SpinGlass.abs_apply_le_norm n v σ) (abs_gibbs_average_le_norm g v)
      _ = _ := by ring
  calc
    _ ≤ 1*(2*‖v‖) := mul_le_mul hp ha (abs_nonneg _) (by norm_num)
    _ = _ := one_mul _

def gibbsWeight_zero_moderateGrowth {n : ℕ} (σ : Configuration n) :
    PhysLean.Probability.GaussianIBP.HasModerateGrowth
      (fun g : Disorder n => gibbsWeight 0 g σ) := by
  refine ⟨3,0,by norm_num,?_,?_⟩
  · intro g
    rw [abs_of_pos (gibbsWeight_pos 0 g σ)]
    have hh : gibbsWeight 0 g σ ≤ 1 := (gibbsFiniteProbability g).weight_le_one σ
    simp only [pow_zero,mul_one]
    linarith
  · intro g
    simp only [pow_zero,mul_one]
    exact (norm_fderiv_gibbsWeight_zero_le g σ).trans (by norm_num)

end GeneralDepthPaper
