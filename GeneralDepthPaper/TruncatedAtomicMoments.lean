module

public import GeneralDepthPaper.TruncatedAtomicStateLaw

@[expose] public section


/-! Exact actual Γ, curvature-square and first-variation identification with
Appendix A.2. Every expectation uses the genuine canonical Brownian law. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GeneralDepthPaper
open FourPapersCommon
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem measurable_atomicTruncatedStatePath (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) : Measurable (atomicTruncatedStatePath Ξ z hz) := by
  have he : atomicTruncatedStatePath Ξ z hz=(fun ω=>additiveStatePath (atomicTruncatedData Ξ z hz).driftData
      0 1 (by norm_num) (clockBrownianPath (atomicCovarianceClock Ξ) ω)) :=
    funext (atomicTruncatedStatePath_eq_additive Ξ z hz)
  rw [he]
  exact (measurable_additiveStatePath _ _ _ _).comp (measurable_clockBrownianPath _)

theorem measurable_atomicOptimalStatePath (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) : Measurable (atomicOptimalStatePath Ξ z hz) := by
  have he : atomicOptimalStatePath Ξ z hz=(fun ω=>additiveStatePath (atomicTruncatedData Ξ z hz).driftData
      0 1 (by norm_num) (rescaledClockBrownianPath (mixedBeta Ξ.toEvenMixture) (atomicCovarianceClock Ξ) ω)) :=
    funext (atomicOptimalStatePath_eq_additive Ξ z hz)
  rw [he]
  exact (measurable_additiveStatePath _ _ _ _).comp (measurable_rescaledClockBrownianPath _ _)

theorem atomicTruncatedMoment_eq_selected (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (j : Fin 3) (q : Overlap) :
    (∫ω,(atomicTruncatedData Ξ z hz).spatialField j
      (q,(atomicTruncatedData Ξ z hz).state (q:ℝ).toNNReal ω)^2 ∂Paper.canonicalBrownianMeasure)=
    ∫ω,(atomicTruncatedData Ξ z hz).spatialField j
      (q,optimalState Ξ (atomicMeasure z hz) ω q)^2 ∂Paper.canonicalBrownianMeasure := by
  let F:C(TruncatedClockDomain 1,ℝ)→ℝ:=fun w=>(atomicTruncatedData Ξ z hz).spatialField j (q,w q)^2
  have hF : Continuous F := by
    exact ((atomicTruncatedData Ξ z hz).spatialField j).continuous.comp
      (continuous_const.prodMk (continuous_eval_const q)) |>.pow 2
  have he:=congrArg (fun ν:Measure C(TruncatedClockDomain 1,ℝ)=>∫w,F w ∂ν)
    (atomic_truncated_state_path_law Ξ z hz)
  rw [integral_map (measurable_atomicTruncatedStatePath Ξ z hz).aemeasurable
      hF.aestronglyMeasurable,
    integral_map (measurable_atomicOptimalStatePath Ξ z hz).aemeasurable
      hF.aestronglyMeasurable] at he
  exact he

theorem Gamma_atomicMeasure_eq_truncated (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (q : ℝ) (hq : q∈Icc (0:ℝ) 1) :
    Gamma Ξ (atomicMeasure z hz) q=(atomicTruncatedData Ξ z hz).Gamma q := by
  change (∫ω,gradient Ξ (atomicMeasure z hz) q (optimalState Ξ (atomicMeasure z hz) ω q)^2
    ∂Paper.canonicalBrownianMeasure)=_
  simp_rw [gradient_atomicMeasure_eq_truncated Ξ z hz q hq]
  exact (atomicTruncatedMoment_eq_selected Ξ z hz 0 ⟨q,hq⟩).symm

theorem curvatureMoment_atomicMeasure_eq_truncated (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (q : ℝ) (hq : q∈Icc (0:ℝ) 1) :
    curvatureMoment Ξ (atomicMeasure z hz) q=(atomicTruncatedData Ξ z hz).Gamma2 q := by
  rw [curvatureMoment,mixedCurvatureMoment2_eq_integral Ξ.toEvenMixture 0 (atomicMeasure z hz) hq]
  change (∫ω,hessian Ξ (atomicMeasure z hz) q (optimalState Ξ (atomicMeasure z hz) ω q)^2
    ∂Paper.canonicalBrownianMeasure)=_
  simp_rw [hessian_atomicMeasure_eq_truncated Ξ z hz q hq]
  exact (atomicTruncatedMoment_eq_selected Ξ z hz 1 ⟨q,hq⟩).symm

theorem firstVariation_atomicMeasure_eq_truncated (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (q : ℝ) (hq : q∈Icc (0:ℝ) 1) :
    firstVariation Ξ (atomicMeasure z hz) q=(atomicTruncatedData Ξ z hz).firstVariation q := by
  rw [firstVariation_eq,TruncatedParisiData.firstVariation]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hq.1] at hs
  have hsu : s∈Icc (0:ℝ) 1 := ⟨hs.1,hs.2.trans hq.2⟩
  change Ξ.second s*(Gamma Ξ (atomicMeasure z hz) s-s)=
    (atomicTruncatedData Ξ z hz).covarianceField 2 s*
      ((atomicTruncatedData Ξ z hz).Gamma s-s)
  rw [Gamma_atomicMeasure_eq_truncated Ξ z hz s hsu,
    atomicTruncatedData_covarianceField_two Ξ z hz s hsu]

end GeneralDepthPaper
