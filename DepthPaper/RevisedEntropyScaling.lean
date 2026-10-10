module

public import DepthPaper.RevisedEntropyMassDerivative
public import DepthPaper.RevisedEntropyAtomicExpectation
public import DepthPaper.RevisedTemperatureFamily
public import DepthPaper.TemperatureMassColeHopf

@[expose] public section

/-! Literal temperature and cumulative-mass identities for the finite atomic
functional. These equalities use actual Gaussian integrals and actual measures. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ContDiff BigOperators
namespace DepthPaper.RevisedCovariance
open FourPapersCommon ColeHopfFoundation.ProbabilityTheory
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 64

def entropyMassMeasure (μ : ParisiMeasure) (m : ℝ) : ParisiMeasure :=
  Paper.parisiMix μ (Paper.diracOverlap 1 (by norm_num)) (1-m)

theorem entropyMassMeasure_cdf (μ : ParisiMeasure) {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1)
    {q : ℝ} (hq : q < 1) :
    Paper.parisiCDF (entropyMassMeasure μ m) q = m * Paper.parisiCDF μ q := by
  rw [entropyMassMeasure,Paper.parisiCDF_mix _ _ _ _ (by constructor <;> linarith [hm.1,hm.2]),
    Paper.parisiCDF_dirac,ite_eq_right (not_le.mpr hq)]
  ring

theorem entropyMassMeasure_correction (Ξ : RevisedCovariance) (μ : ParisiMeasure)
    {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) :
    (∫q in (0:ℝ)..1,q*Ξ.second q*Paper.parisiCDF (entropyMassMeasure μ m) q) =
      m*(∫q in (0:ℝ)..1,q*Ξ.second q*Paper.parisiCDF μ q) := by
  let w : ℝ → ℝ := fun q => q*Ξ.second q
  have hw : ContinuousOn w (Icc (0:ℝ) 1) :=
    (continuous_id.mul Ξ.continuous_second).continuousOn
  change weightedCDFIntegral w (Paper.parisiMix μ (Paper.diracOverlap 1 (by norm_num)) (1-m)) = _
  rw [weightedCDFIntegral_mix w hw _ _ (1-m) (by constructor <;> linarith [hm.1,hm.2])]
  have hd : weightedCDFIntegral w (Paper.diracOverlap 1 (by norm_num)) = 0 := by
    rw [weightedCDFIntegral_eq_measure_integral w hw]
    change (∫q,weightedTail w q ∂Measure.dirac (⟨1,by norm_num⟩ : Overlap)) = 0
    rw [integral_dirac]
    exact intervalIntegral.integral_same
  rw [hd]
  change (1-(1-m))*weightedCDFIntegral w μ+(1-m)*0=m*weightedCDFIntegral w μ
  ring

theorem entropyMassMeasure_potential_recursion (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) :
    potential Ξ (entropyMassMeasure (atomicMeasure z hz) m) 0 0 =
      terminalValue (coleHopfRecursion (r+1)
        (revisedMassRecursionData (atomicRecursionData Ξ z) m,logCoshTerminal)) 0 := by
  have H := revisedEntropy_grid_potential_recursion Ξ.toEvenMixture
    (entropyMassMeasure (atomicMeasure z hz) m) (r+1) (atomicNode z)
    (revisedMassRecursionData (atomicRecursionData Ξ z) m)
    (atomicNode_mem_unit z hz)
    (fun i => (atomicNode_strictMono z hz) i.castSucc_lt_succ)
    (atomicRecursionData_variance_pos Ξ z hz)
    (fun i => by simp only [revisedMassRecursionData,atomicRecursionData,toEvenMixture_first])
    (fun i s hs => by
      rw [entropyMassMeasure_cdf _ hm (hs.2.trans_le (atomicNode_mem_unit z hz i.succ).2),
        parisiCDF_atomicMeasure_cell z hz i hs]
      rfl)
    logCoshTerminal
    (fun x => by rw [atomicNode_last,mixedPotential_terminal,terminalValue_logCoshTerminal]) 0
  simpa only [atomicNode_zero,potential] using H

theorem entropyMassMeasure_functional_recursion (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) :
    parisiFunctional Ξ (entropyMassMeasure (atomicMeasure z hz) m) = Real.log 2 +
      terminalValue (coleHopfRecursion (r+1)
        (revisedMassRecursionData (atomicRecursionData Ξ z) m,logCoshTerminal)) 0 -
      (m/2)*atomicCorrection Ξ z := by
  rw [parisiFunctional_eq,entropyMassMeasure_potential_recursion Ξ z hz hm,
    entropyMassMeasure_correction Ξ _ hm,←atomicCorrection_eq_integral Ξ z hz]
  ring

theorem temperature_potential_mass_recursion (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) {m : ℝ} (hm : 0 < m) :
    m⁻¹*potential (Ξ.temperatureScale m hm.ne') (atomicMeasure z hz) 0 0 =
      terminalValue (coleHopfRecursion (r+1)
        (revisedMassRecursionData (atomicRecursionData Ξ z) m,scaledLogCoshTerminal m)) 0 := by
  let Ψ := Ξ.temperatureScale m hm.ne'
  have H := coleHopf_chain_eq_recursion (r+1)
    (revisedMassRecursionData (atomicRecursionData Ξ z) m) (scaledLogCoshTerminal m)
    (fun i x => m⁻¹*potential Ψ (atomicMeasure z hz) (atomicNode z i) (m*x))
    (atomicRecursionData_variance_pos Ξ z hz)
    (fun x => by
      rw [atomicNode_last]
      change m⁻¹*mixedPotential Ψ.toEvenMixture (atomicMeasure z hz) (1,m*x)=_
      rw [mixedPotential_terminal,terminalValue_scaledLogCoshTerminal m hm.ne'])
    (fun i x => by
      have hs := coleHopf_temperature_mass_scaling m hm.ne' (atomicLevel z i)
        (Ξ.first (atomicNode z i.succ)-Ξ.first (atomicNode z i.castSucc)).toNNReal
        (fun y => potential Ψ (atomicMeasure z hz) (atomicNode z i.succ) y)
        (continuous_mixedPotential_section Ψ.toEvenMixture _ _).measurable x
      have hvar : NNReal.mk (m^2) (sq_nonneg m)*
          (Ξ.first (atomicNode z i.succ)-Ξ.first (atomicNode z i.castSucc)).toNNReal =
          (Ψ.first (atomicNode z i.succ)-Ψ.first (atomicNode z i.castSucc)).toNNReal := by
        apply NNReal.coe_injective
        have hv0 : 0 < Ξ.first (atomicNode z i.succ)-Ξ.first (atomicNode z i.castSucc) :=
          atomicRecursionData_variance_pos Ξ z hz i
        rw [NNReal.coe_mul,NNReal.coe_mk,Real.coe_toNNReal _
          hv0.le]
        have he : Ψ.first (atomicNode z i.succ)-Ψ.first (atomicNode z i.castSucc)=
            m^2*(Ξ.first (atomicNode z i.succ)-Ξ.first (atomicNode z i.castSucc)) := by
          simp only [Ψ,temperatureScale_first]
          ring
        rw [he,Real.coe_toNNReal _ (mul_nonneg (sq_nonneg m)
          hv0.le)]
      rw [hvar] at hs
      have hstep := mixedPotential_atomic_step Ψ z hz i (m*x)
      change potential Ψ (atomicMeasure z hz) (atomicNode z i.castSucc) (m*x)=
        coleHopf (atomicLevel z i)
          (Ψ.first (atomicNode z i.succ)-Ψ.first (atomicNode z i.castSucc)).toNNReal
          (fun y=>potential Ψ (atomicMeasure z hz) (atomicNode z i.succ) y) (m*x)
        at hstep
      change m⁻¹*potential Ψ (atomicMeasure z hz) (atomicNode z i.castSucc) (m*x)=
        coleHopf (m*atomicLevel z i)
          (Ξ.first (atomicNode z i.succ)-Ξ.first (atomicNode z i.castSucc)).toNNReal
          (fun y=>m⁻¹*potential Ψ (atomicMeasure z hz) (atomicNode z i.succ) (m*y)) x
      rw [hs,←hstep]) 0
  simpa only [atomicNode_zero,mul_zero] using H

theorem temperature_atomicCorrection (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) {m : ℝ} (hm : m ≠ 0) :
    atomicCorrection (Ξ.temperatureScale m hm) z=m^2*atomicCorrection Ξ z := by
  simp only [atomicCorrection,covarianceCorrectionPrimitive,temperatureScale_first,
    temperatureScale_value,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem temperature_functional_mass_recursion (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) {m : ℝ} (hm : 0 < m) :
    m⁻¹*parisiFunctional (Ξ.temperatureScale m hm.ne') (atomicMeasure z hz) =
      m⁻¹*Real.log 2 + terminalValue (coleHopfRecursion (r+1)
        (revisedMassRecursionData (atomicRecursionData Ξ z) m,scaledLogCoshTerminal m)) 0 -
      (m/2)*atomicCorrection Ξ z := by
  rw [parisiFunctional_eq,←atomicCorrection_eq_integral _ z hz,
    temperature_atomicCorrection]
  rw [mul_sub,mul_add,temperature_potential_mass_recursion Ξ z hz hm]
  field_simp

theorem temperature_entropyMass_difference (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) {m : ℝ}
    (hm : m ∈ Ioc (0:ℝ) 1) :
    m⁻¹*parisiFunctional (Ξ.temperatureScale m hm.1.ne') (atomicMeasure z hz) =
      parisiFunctional Ξ (entropyMassMeasure (atomicMeasure z hz) m) +
      (m⁻¹-1)*Real.log 2 +
      (terminalValue (coleHopfRecursion (r+1)
        (revisedMassRecursionData (atomicRecursionData Ξ z) m,scaledLogCoshTerminal m)) 0 -
        terminalValue (coleHopfRecursion (r+1)
          (revisedMassRecursionData (atomicRecursionData Ξ z) m,logCoshTerminal)) 0) := by
  rw [temperature_functional_mass_recursion Ξ z hz hm.1,
    entropyMassMeasure_functional_recursion Ξ z hz ⟨hm.1.le,hm.2⟩]
  ring

end DepthPaper.RevisedCovariance
