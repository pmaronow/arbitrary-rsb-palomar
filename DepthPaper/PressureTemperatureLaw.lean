module

public import DepthPaper.ExpectedPressureCalculus
public import FourPapersCommon.MixtureTemperatureScale
public import OverlapPaper.ThermodynamicLimit

@[expose] public section


/-! Exact Gaussian disorder transport under temperature scaling and the
actual thermodynamic limit of the finite expected scaled pressure. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace DepthPaper
open FourPapersCommon OverlapPaper
set_option maxHeartbeats 1000000

theorem map_disorderLaw_temperatureScale (ξ : AdmissibleEvenMixture) (n : ℕ)
    (b : ℝ) (hb : b ≠ 0) :
    (disorderLaw ξ n).map (fun g : Disorder n=>b • g)=disorderLaw (ξ.temperatureScale b hb) n := by
  let μ := (disorderLaw ξ n).map (fun g : Disorder n=>b • g)
  let L : Disorder n →L[ℝ] Disorder n := b • ContinuousLinearMap.id ℝ _
  have he : (fun g : Disorder n=>b • g)=L := rfl
  haveI : IsGaussian μ := by dsimp only [μ]; rw [he]; infer_instance
  have hμ0 : (∫ g : Disorder n,g ∂μ)=0 := by
    change (∫ g : Disorder n,id g ∂(disorderLaw ξ n).map (fun g=>b • g))=0
    rw [he,integral_map_of_stronglyMeasurable L.continuous.measurable stronglyMeasurable_id]
    change (∫ g : Disorder n,b • g ∂disorderLaw ξ n)=0
    rw [integral_smul,integral_disorder_eq_zero,smul_zero]
  change μ=disorderLaw (ξ.temperatureScale b hb) n
  apply IsGaussian.ext
  · simpa only [id_eq] using hμ0.trans (integral_disorder_eq_zero (ξ.temperatureScale b hb) n).symm
  · rw [←ContinuousLinearMap.toBilinForm_inj]
    apply LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun (Configuration n) ℝ).toBasis
    intro σ τ
    rw [ContinuousLinearMap.toBilinForm_apply,ContinuousLinearMap.toBilinForm_apply,
      covarianceBilin_apply_eq_cov,covarianceBilin_apply_eq_cov]
    · change cov[fun g : Disorder n=>inner ℝ (EuclideanSpace.basisFun (Configuration n) ℝ σ) g,
        fun g=>inner ℝ (EuclideanSpace.basisFun (Configuration n) ℝ τ) g;
        (disorderLaw ξ n).map (fun g=>b • g)] = _
      rw [he,covariance_map_fun
        (X := fun g : Disorder n=>inner ℝ (EuclideanSpace.basisFun (Configuration n) ℝ σ) g)
        (Y := fun g : Disorder n=>inner ℝ (EuclideanSpace.basisFun (Configuration n) ℝ τ) g)
        (by fun_prop) (by fun_prop) L.continuous.measurable.aemeasurable]
      simp only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_inner,L,ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply,PiLp.smul_apply,smul_eq_mul]
      rw [covariance_const_mul_left,covariance_const_mul_right]
      change b*(b*cov[fun g : Disorder n=>hamiltonian g σ,fun g=>hamiltonian g τ;disorderLaw ξ n])=
        cov[fun g : Disorder n=>hamiltonian g σ,fun g=>hamiltonian g τ;disorderLaw (ξ.temperatureScale b hb) n]
      rw [covariance_hamiltonian,covariance_hamiltonian,AdmissibleEvenMixture.temperatureScale_value]
      ring
    all_goals exact IsGaussian.memLp_two_id

theorem expectedScaledPressure_eq_scaled_covariance (ξ : AdmissibleEvenMixture) (n : ℕ)
    (b : ℝ) (hb : b ≠ 0) :
    expectedScaledPressure ξ n b=expectedFreeEnergy (ξ.temperatureScale b hb) 0 n := by
  unfold expectedScaledPressure expectedFreeEnergy finitePressureObservable
  rw [←map_disorderLaw_temperatureScale ξ n b hb]
  have hc : StronglyMeasurable (freeEnergy (n := n) 0) := by
    simpa only [finitePressureObservable,one_smul] using
      (continuous_finitePressureObservable_slice (n := n) 1).stronglyMeasurable
  exact (integral_map_of_stronglyMeasurable
    (show Measurable (fun g : Disorder n=>b • g) by fun_prop) hc).symm

def scaledThermodynamicPressure (ξ : AdmissibleEvenMixture) (b : ℝ) : ℝ :=
  if hb : b=0 then Real.log 2 else thermodynamicPressure (ξ.temperatureScale b hb) 0

theorem tendsto_expectedScaledPressure (ξ : AdmissibleEvenMixture) (b : ℝ) :
    Tendsto (fun n=>expectedScaledPressure ξ n b) atTop (𝓝 (scaledThermodynamicPressure ξ b)) := by
  by_cases hb : b=0
  · subst b
    have h0 : scaledThermodynamicPressure ξ 0=Real.log 2 := by simp [scaledThermodynamicPressure]
    rw [h0]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
    unfold expectedScaledPressure finitePressureObservable freeEnergy partitionFunction totalHamiltonian hamiltonian
    simp only [zero_smul,PiLp.zero_apply,zero_mul,add_zero,Real.exp_zero,Finset.sum_const,
      Finset.card_univ,Fintype.card_pi,Fintype.card_bool,Finset.prod_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
    rw [show ((2^n:ℕ):ℝ)=(2:ℝ)^n by norm_cast,Real.log_pow]
    simp only [integral_const,measure_univ,ENNReal.toReal_one,one_smul]
    field_simp
    simp
  · rw [scaledThermodynamicPressure,dif_neg hb]
    simpa only [expectedScaledPressure_eq_scaled_covariance ξ _ b hb] using
      tendsto_expectedFreeEnergy (ξ.temperatureScale b hb) 0

end DepthPaper
