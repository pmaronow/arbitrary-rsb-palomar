module

public import GeneralDepthPaper.GibbsEntropyLower
public import QuantitativePaper.FiniteSpin
public import FourPapersCommon.GaussianFreeEnergyIBP
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section


/-! Genuine finite-volume pressure derivatives and convexity for the
constructed mixed Hamiltonian. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace GeneralDepthPaper
open FourPapersCommon OverlapPaper
set_option maxHeartbeats 1000000

def finitePressureObservable {n : ℕ} (g : Disorder n) (b : ℝ) : ℝ :=
  freeEnergy 0 (b • g)

def finitePressureResponse {n : ℕ} (g : Disorder n) (b : ℝ) : ℝ :=
  (∑ σ,gibbsWeight 0 (b • g) σ*g σ)/(n : ℝ)

theorem terminalWeight_scaled_eq {n : ℕ} (g : Disorder n) (b : ℝ) (σ : Configuration n) :
    QuantitativePaper.terminalWeight (fun τ=>b*g τ) σ=gibbsWeight 0 (b • g) σ := by
  simp only [QuantitativePaper.terminalWeight,QuantitativePaper.terminalPartition,gibbsWeight,
    partitionFunction,totalHamiltonian,hamiltonian,zero_mul,add_zero,PiLp.smul_apply,smul_eq_mul]

theorem terminalTilt_zero_scaled {n : ℕ} (g : Disorder n) (b : ℝ) :
    QuantitativePaper.terminalTilt (fun _ : Configuration n=>0) (fun σ=>g σ) b=
      fun σ=>b*g σ := by
  funext σ
  simp only [QuantitativePaper.terminalTilt,zero_add]

theorem hasDerivAt_finitePressureObservable {n : ℕ} (g : Disorder n) (b : ℝ) :
    HasDerivAt (finitePressureObservable g) (finitePressureResponse g b) b := by
  have H := (QuantitativePaper.hasDerivAt_terminalPotential_tilt (fun _ : Configuration n=>0)
    (fun σ=>g σ) b).div_const (n : ℝ)
  convert! H using 1
  · funext a
    simp [finitePressureObservable,freeEnergy,partitionFunction,totalHamiltonian,hamiltonian,
      QuantitativePaper.terminalPotential,QuantitativePaper.terminalPartition,
      QuantitativePaper.terminalTilt,PiLp.smul_apply,smul_eq_mul]
  · simp only [finitePressureResponse,QuantitativePaper.terminalMean,terminalTilt_zero_scaled,
      terminalWeight_scaled_eq]

theorem continuous_finitePressureObservable_slice {n : ℕ} (b : ℝ) :
    Continuous (fun g : Disorder n=>finitePressureObservable g b) := by
  unfold finitePressureObservable freeEnergy
  apply Continuous.div_const
  exact ((continuous_partitionFunction 0).log
    (fun g=>(partitionFunction_pos 0 g).ne')).comp
      ((continuous_id : Continuous (fun g : Disorder n=>g)).const_smul b)

theorem continuous_finitePressureResponse_slice {n : ℕ} (b : ℝ) :
    Continuous (fun g : Disorder n=>finitePressureResponse g b) := by
  unfold finitePressureResponse
  apply Continuous.div_const
  apply continuous_finset_sum
  intro σ _
  exact ((continuous_gibbsWeight 0 σ).comp
    ((continuous_id : Continuous (fun g : Disorder n=>g)).const_smul b)).mul
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Configuration n=>ℝ) σ).continuous

theorem norm_finitePressureResponse_le {n : ℕ} (g : Disorder n) (b : ℝ) :
    ‖finitePressureResponse g b‖ ≤ ‖g‖/(n : ℝ) := by
  rw [finitePressureResponse,Real.norm_eq_abs,abs_div,
    abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
  exact div_le_div_of_nonneg_right (abs_gibbs_average_le_norm (b • g) g) (Nat.cast_nonneg n)

theorem finitePressureObservable_eq_negative_energy {n : ℕ} (g : Disorder n) (b : ℝ) :
    finitePressureObservable g b=SpinGlass.free_energy_density n ((-b) • g) := by
  simp [finitePressureObservable,freeEnergy,partitionFunction,totalHamiltonian,hamiltonian,
    SpinGlass.free_energy_density,SpinGlass.Z,PiLp.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]

theorem integrable_finitePressureObservable (ξ : AdmissibleEvenMixture) (n : ℕ) (b : ℝ) :
    Integrable (fun g : Disorder n=>finitePressureObservable g b) (disorderLaw ξ n) := by
  letI : MeasureSpace (Disorder n) := ⟨disorderLaw ξ n⟩
  letI : IsProbabilityMeasure (volume : Measure (Disorder n)) := disorderLaw_isProbabilityMeasure ξ n
  have hg : Integrable (id : Disorder n→Disorder n) (disorderLaw ξ n) := IsGaussian.integrable_id
  have H := integrable_gaussianFreeEnergy_affine hg
    ((-b) • ContinuousLinearMap.id ℝ (Disorder n)) 0
  exact H.congr (.of_forall fun g=>by
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,id_eq,add_zero]
    exact (finitePressureObservable_eq_negative_energy g b).symm)

theorem hasDerivAt_gibbs_scaled_energy {n : ℕ} (g : Disorder n) (b : ℝ) :
    HasDerivAt (fun a=>∑ σ,gibbsWeight 0 (a • g) σ*g σ)
      (QuantitativePaper.terminalCovariance (fun σ=>b*g σ) (fun σ=>g σ) (fun σ=>g σ)) b := by
  have H := QuantitativePaper.hasDerivAt_terminalMean_tilt (fun _ : Configuration n=>0)
    (fun σ=>g σ) (fun σ=>g σ) b
  simpa only [QuantitativePaper.terminalMean,terminalTilt_zero_scaled,
    terminalWeight_scaled_eq] using H

theorem convexOn_finitePressureObservable {n : ℕ} (g : Disorder n) :
    ConvexOn ℝ univ (finitePressureObservable g) := by
  have hmono : Monotone (fun a=>∑ σ,gibbsWeight 0 (a • g) σ*g σ) :=
    monotone_of_hasDerivAt_nonneg (hasDerivAt_gibbs_scaled_energy g)
      (fun b=>QuantitativePaper.terminalCovariance_self_nonneg _ _)
  apply Monotone.convexOn_univ_of_deriv
    (fun b=>(hasDerivAt_finitePressureObservable g b).differentiableAt)
  intro x y hxy
  rw [(hasDerivAt_finitePressureObservable g x).deriv,(hasDerivAt_finitePressureObservable g y).deriv]
  exact div_le_div_of_nonneg_right (hmono hxy) (Nat.cast_nonneg n)

end GeneralDepthPaper
