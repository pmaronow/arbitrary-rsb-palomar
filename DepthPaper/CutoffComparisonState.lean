module

public import DepthPaper.CutoffComparisonPotential
public import DepthPaper.TemperatureMassMoments

@[expose] public section


/-! The ψ-comparison recursion has the same actual canonical diffusion as
the rescaled temperature model below qc. This is pathwise equality, proved
from the literal integral equation and Picard uniqueness. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace DepthPaper
open FourPapersCommon Paper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

theorem cutoffComparisonData_coefficient_eq (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc) (hc1 : qc≤1)
    (q : ℝ) (hq : q∈Ico (0:ℝ) qc) :
    (cutoffComparisonData Ξ z hz m hm qc hc).coefficient q=
      m*parisiCDF (atomicMeasure z hz) q := by
  obtain ⟨i,hi⟩:=exists_cutoff_right_cell z hz qc hc q hq
  rw [parisiCDF_atomicMeasure_cutoff_cell z hz qc hc hc1 i hi]
  exact truncatedCoefficient_eq_level (cutoffComparisonData Ξ z hz m hm qc hc).parameter
    (cutoffComparisonData Ξ z hz m hm qc hc).node_strictMono.monotone q i hi

theorem rateClock_cutoffComparisonData_eq (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc) (q : ℝ≥0) (hq : (q:ℝ)≤qc) :
    (rateClock (cutoffComparisonData Ξ z hz m hm qc hc).rateData q:ℝ)=Ξ.first q := by
  let d:=cutoffComparisonData Ξ z hz m hm qc hc
  change (∫s in (0:ℝ)..(q:ℝ),d.covarianceField 2 s.toNNReal)=Ξ.first q
  have he : (∫s in (0:ℝ)..(q:ℝ),d.covarianceField 2 s.toNNReal)=
      ∫s in (0:ℝ)..(q:ℝ),Ξ.second s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le q.coe_nonneg] at hs
    change d.covarianceField 2 (s.toNNReal:ℝ)=Ξ.second s
    rw [Real.coe_toNNReal _ hs.1]
    exact cutoffTruncatedData_covarianceField_two Ξ z hz m hm qc hc _ _ s
      ⟨hs.1,hs.2.trans hq⟩
  rw [he,intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _=>Ξ.hasDerivAt_first s) (Ξ.continuous_second.intervalIntegrable _ _),Ξ.first_zero,sub_zero]

theorem state_cutoffComparisonData (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Ioc (0:ℝ) 1)
    (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc) (hc1 : qc≤1)
    (q : ℝ) (hq : q∈Icc (0:ℝ) qc) (ω : BrownianSample) :
    (cutoffComparisonData Ξ z hz m ⟨hm.1.le,hm.2⟩ qc hc).state q.toNNReal ω=
      temperatureMassState Ξ (atomicMeasure z hz) m hm.1 q.toNNReal ω := by
  let d:=cutoffComparisonData Ξ z hz m ⟨hm.1.le,hm.2⟩ qc hc
  let X:ℝ→ℝ:=fun s=>temperatureMassState Ξ (atomicMeasure z hz) m hm.1 s.toNNReal ω
  have hX : Continuous X :=
    (continuous_clockedItoState _ _ _ _ _ ω).comp continuous_real_toNNReal
  have hXe : ∀t∈Icc (0:ℝ) qc,X t=0+rateNoiseReal d.rateData ω t+
      ∫s in (0:ℝ)..t,d.driftData.coefficient s*d.driftData.gradient s (X s) := by
    intro t ht
    have hn : rateNoiseReal d.rateData ω t=canonicalBrownian (Ξ.first t).toNNReal ω := by
      dsimp only [rateNoiseReal,timeChangedBrownian]
      congr 1
      apply NNReal.coe_injective
      rw [rateClock_cutoffComparisonData_eq Ξ z hz m ⟨hm.1.le,hm.2⟩ qc hc _
        (by rw [Real.coe_toNNReal _ ht.1];exact ht.2),Real.coe_toNNReal _ ht.1,
        Real.coe_toNNReal _ (Ξ.first_nonneg ht.1)]
    have H:=temperatureMassState_integral_equation Ξ (atomicMeasure z hz) m hm.1
      t.toNNReal (by rw [Real.coe_toNNReal _ ht.1];exact ht.2.trans hc1) ω
    rw [Real.coe_toNNReal _ ht.1] at H
    change X t=_ at H
    rw [H,zero_add,hn]
    congr 1
    apply intervalIntegral.integral_congr_uIoo
    rw [uIoo_of_le ht.1]
    intro s hs
    have hsC : s∈Icc (0:ℝ) qc:=⟨hs.1.le,hs.2.le.trans ht.2⟩
    have hsco : s∈Ico (0:ℝ) qc:=⟨hs.1.le,hs.2.trans_le ht.2⟩
    simp only [TruncatedParisiData.driftData]
    have hcv : d.covarianceField 2 s=Ξ.second s :=
      cutoffTruncatedData_covarianceField_two Ξ z hz m ⟨hm.1.le,hm.2⟩ qc hc _ _ s hsC
    rw [hcv,cutoffComparisonData_coefficient_eq Ξ z hz m ⟨hm.1.le,hm.2⟩ qc hc hc1 s hsco,
      gradient_cutoffComparisonData Ξ z hz m hm qc hc hc1 s hsC]
    ring
  have hu:=additiveStateReal_unique d.driftData 0 qc d.qc_pos.le
    (rateNoiseReal d.rateData ω) (continuous_rateNoiseReal d.rateData ω) X hX hXe
  change clockedItoState d.driftData d.rateData 0 qc d.qc_pos.le q.toNNReal ω=X q
  rw [clockedItoState_eq _ _ _ _ _ (by rw [Real.coe_toNNReal _ hq.1];exact hq.2),
    Real.coe_toNNReal _ hq.1]
  exact (hu hq).symm

theorem Gamma_cutoffComparisonData (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Ioc (0:ℝ) 1)
    (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc) (hc1 : qc≤1)
    (q : ℝ) (hq : q∈Icc (0:ℝ) qc) :
    (cutoffComparisonData Ξ z hz m ⟨hm.1.le,hm.2⟩ qc hc).Gamma q=
      Gamma ((temperatureCovarianceFamily Ξ).covariance m) (atomicMeasure z hz) q := by
  change (∫ω,(cutoffComparisonData Ξ z hz m ⟨hm.1.le,hm.2⟩ qc hc).spatialField 0
    (q,(cutoffComparisonData Ξ z hz m ⟨hm.1.le,hm.2⟩ qc hc).state q.toNNReal ω)^2
      ∂canonicalBrownianMeasure)=_
  simp_rw [gradient_cutoffComparisonData Ξ z hz m hm qc hc hc1 q hq,
    state_cutoffComparisonData Ξ z hz m hm qc hc hc1 q hq]
  exact temperature_mass_Gamma Ξ (atomicMeasure z hz) m hm.1 ⟨hq.1,hq.2.trans hc1⟩

theorem firstVariation_cutoffComparisonData (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Ioc (0:ℝ) 1)
    (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc) (hc1 : qc≤1)
    (q : ℝ) (hq : q∈Icc (0:ℝ) qc) :
    (cutoffComparisonData Ξ z hz m ⟨hm.1.le,hm.2⟩ qc hc).firstVariation q=
      (m^2)⁻¹*firstVariation ((temperatureCovarianceFamily Ξ).covariance m) (atomicMeasure z hz) q := by
  rw [TruncatedParisiData.firstVariation]
  have he : (∫s in (0:ℝ)..q,
      (cutoffComparisonData Ξ z hz m ⟨hm.1.le,hm.2⟩ qc hc).covarianceField 2 s*
        ((cutoffComparisonData Ξ z hz m ⟨hm.1.le,hm.2⟩ qc hc).Gamma s-s))=
      ∫s in (0:ℝ)..q,Ξ.second s*(temperatureMassGamma Ξ (atomicMeasure z hz) m hm.1 s-s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hq.1] at hs
    have hsC : s∈Icc (0:ℝ) qc:=⟨hs.1,hs.2.trans hq.2⟩
    change (cutoffComparisonData Ξ z hz m ⟨hm.1.le,hm.2⟩ qc hc).covarianceField 2 s*
      ((cutoffComparisonData Ξ z hz m ⟨hm.1.le,hm.2⟩ qc hc).Gamma s-s)=
        Ξ.second s*(temperatureMassGamma Ξ (atomicMeasure z hz) m hm.1 s-s)
    rw [Gamma_cutoffComparisonData Ξ z hz m hm qc hc hc1 s hsC,
      temperature_mass_Gamma Ξ (atomicMeasure z hz) m hm.1 ⟨hs.1,hsC.2.trans hc1⟩]
    have hcv : (cutoffComparisonData Ξ z hz m ⟨hm.1.le,hm.2⟩ qc hc).covarianceField 2 s=Ξ.second s :=
      cutoffTruncatedData_covarianceField_two Ξ z hz m ⟨hm.1.le,hm.2⟩ qc hc _ _ s hsC
    rw [hcv]
  rw [he]
  exact temperature_mass_firstVariation Ξ (atomicMeasure z hz) m hm.1 ⟨hq.1,hq.2.trans hc1⟩

end DepthPaper
