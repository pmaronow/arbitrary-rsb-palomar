module

public import GeneralDepthPaper.CutoffSelectedStateLaw
public import GeneralDepthPaper.TruncatedAtomicMoments

@[expose] public section


/-! Actual overlap observable and first-variation identity below the cutoff.
Both laws and both reconstructed spatial fields are identified beforehand. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GeneralDepthPaper
open FourPapersCommon
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem measurable_cutoffTruncatedStatePath (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (Q : Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc) (hcQ : qc≤(Q:ℝ)) :
    Measurable (cutoffTruncatedStatePath Ξ z hz m hm Q qc hc hcQ) := by
  let d:=cutoffCandidateData Ξ z hz m hm Q qc hc hcQ
  rw [show cutoffTruncatedStatePath Ξ z hz m hm Q qc hc hcQ=(fun ω=>
      additiveStatePath d.driftData 0 qc d.qc_pos.le (clockBrownianPath (cutoffCovarianceClock Ξ qc) ω)) from
    funext (cutoffTruncatedStatePath_eq_additive Ξ z hz m hm Q qc hc hcQ)]
  exact (measurable_additiveStatePath _ _ _ _).comp (measurable_clockBrownianPath _)

theorem measurable_cutoffOptimalStatePath (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (Q : Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc) (hcQ : qc≤(Q:ℝ)) :
    Measurable (cutoffOptimalStatePath Ξ z hz m Q qc) := by
  let d:=cutoffCandidateData Ξ z hz m hm Q qc hc hcQ
  rw [show cutoffOptimalStatePath Ξ z hz m Q qc=(fun ω=>
      additiveStatePath d.driftData 0 qc d.qc_pos.le
        (rescaledClockBrownianPath (mixedBeta Ξ.toEvenMixture) (cutoffCovarianceClock Ξ qc) ω)) from
    funext (cutoffOptimalStatePath_eq_additive Ξ z hz m hm Q qc hc hcQ)]
  exact (measurable_additiveStatePath _ _ _ _).comp (measurable_rescaledClockBrownianPath _ _)

theorem cutoffTruncatedMoment_eq_selected (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (Q : Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc) (hcQ : qc≤(Q:ℝ))
    (j : Fin 3) (q : TruncatedClockDomain qc) :
    (∫ω,(cutoffCandidateData Ξ z hz m hm Q qc hc hcQ).spatialField j
      (q,(cutoffCandidateData Ξ z hz m hm Q qc hc hcQ).state (q:ℝ).toNNReal ω)^2
        ∂Paper.canonicalBrownianMeasure)=
      ∫ω,(cutoffCandidateData Ξ z hz m hm Q qc hc hcQ).spatialField j
        (q,optimalState Ξ (twoLevelMeasure z hz m Q) ω q)^2 ∂Paper.canonicalBrownianMeasure := by
  let d:=cutoffCandidateData Ξ z hz m hm Q qc hc hcQ
  let F:C(TruncatedClockDomain qc,ℝ)→ℝ:=fun w=>d.spatialField j (q,w q)^2
  have hF : Continuous F := by
    exact (d.spatialField j).continuous.comp
      (continuous_const.prodMk (continuous_eval_const q)) |>.pow 2
  have he:=congrArg (fun ν:Measure C(TruncatedClockDomain qc,ℝ)=>∫w,F w ∂ν)
    (cutoff_truncated_state_path_law Ξ z hz m hm Q qc hc hcQ)
  rw [integral_map (measurable_cutoffTruncatedStatePath Ξ z hz m hm Q qc hc hcQ).aemeasurable
      hF.aestronglyMeasurable,
    integral_map (measurable_cutoffOptimalStatePath Ξ z hz m hm Q qc hc hcQ).aemeasurable
      hF.aestronglyMeasurable] at he
  exact he

theorem Gamma_twoLevelMeasure_eq_cutoff (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (Q : Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc) (hcQ : qc≤(Q:ℝ))
    (q : ℝ) (hq : q∈Icc (0:ℝ) qc) :
    Gamma Ξ (twoLevelMeasure z hz m Q) q=
      (cutoffCandidateData Ξ z hz m hm Q qc hc hcQ).Gamma q := by
  change (∫ω,gradient Ξ (twoLevelMeasure z hz m Q) q
    (optimalState Ξ (twoLevelMeasure z hz m Q) ω q)^2 ∂Paper.canonicalBrownianMeasure)=_
  simp_rw [gradient_twoLevelMeasure_eq_cutoff Ξ z hz m hm Q qc hc hcQ q hq]
  exact (cutoffTruncatedMoment_eq_selected Ξ z hz m hm Q qc hc hcQ 0 ⟨q,hq⟩).symm

theorem curvatureMoment_twoLevelMeasure_eq_cutoff (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (Q : Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc) (hcQ : qc≤(Q:ℝ))
    (q : ℝ) (hq : q∈Icc (0:ℝ) qc) :
    curvatureMoment Ξ (twoLevelMeasure z hz m Q) q=
      (cutoffCandidateData Ξ z hz m hm Q qc hc hcQ).Gamma2 q := by
  rw [curvatureMoment,mixedCurvatureMoment2_eq_integral Ξ.toEvenMixture 0
    (twoLevelMeasure z hz m Q) ⟨hq.1,hq.2.trans (hcQ.trans Q.property.2)⟩]
  change (∫ω,hessian Ξ (twoLevelMeasure z hz m Q) q
    (optimalState Ξ (twoLevelMeasure z hz m Q) ω q)^2 ∂Paper.canonicalBrownianMeasure)=_
  simp_rw [hessian_twoLevelMeasure_eq_cutoff Ξ z hz m hm Q qc hc hcQ q hq]
  exact (cutoffTruncatedMoment_eq_selected Ξ z hz m hm Q qc hc hcQ 1 ⟨q,hq⟩).symm

theorem firstVariation_twoLevelMeasure_eq_cutoff (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (Q : Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc) (hcQ : qc≤(Q:ℝ))
    (q : ℝ) (hq : q∈Icc (0:ℝ) qc) :
    firstVariation Ξ (twoLevelMeasure z hz m Q) q=
      (cutoffCandidateData Ξ z hz m hm Q qc hc hcQ).firstVariation q := by
  rw [firstVariation_eq,TruncatedParisiData.firstVariation]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hq.1] at hs
  have hsu : s∈Icc (0:ℝ) qc := ⟨hs.1,hs.2.trans hq.2⟩
  change Ξ.second s*(Gamma Ξ (twoLevelMeasure z hz m Q) s-s)=
    (cutoffCandidateData Ξ z hz m hm Q qc hc hcQ).covarianceField 2 s*
      ((cutoffCandidateData Ξ z hz m hm Q qc hc hcQ).Gamma s-s)
  rw [Gamma_twoLevelMeasure_eq_cutoff Ξ z hz m hm Q qc hc hcQ s hsu]
  have hcv : (cutoffCandidateData Ξ z hz m hm Q qc hc hcQ).covarianceField 2 s=Ξ.second s :=
    cutoffTruncatedData_covarianceField_two Ξ z hz m hm qc hc _ _ s hsu
  rw [hcv]

end GeneralDepthPaper
