module

public import GeneralDepthPaper.AtomicPotentialRegularity
public import FourPapersCommon.WeakTimeLipschitz
public import FRSB.BackwardsJets

@[expose] public section


/-! The actual time equation in the original overlap coordinate, for
arbitrary probability measures. The derivative holds almost everywhere;
time sections are absolutely continuous, including the closed endpoints. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff NNReal
namespace GeneralDepthPaper
open FourPapersCommon
set_option maxHeartbeats 1000000

def originalClockTimeField (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (p : ℝ × ℝ) : ℝ :=
  -(Ξ.second p.1/2) * (hessian Ξ μ p.1 p.2 +
    Paper.parisiCDF μ p.1 * gradient Ξ μ p.1 p.2 ^ 2)

theorem continuous_potential_originalClock (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) :
    Continuous (fun p : ℝ × ℝ => potential Ξ μ p.1 p.2) := by
  simpa only [potential,mixedPotential,AdmissibleCovariance.toEvenMixture_clock,Function.comp_def] using
    (Paper.continuous_parisiPotential (mixedBeta Ξ.toEvenMixture)
      (mixedMeasure Ξ.toEvenMixture μ)).comp
      ((Ξ.continuous_clock.comp continuous_fst).prodMk continuous_snd)

theorem measurable_originalClockTimeField (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) :
    Measurable (originalClockTimeField Ξ μ) := by
  have hc : Continuous (fun p : ℝ × ℝ => (Ξ.clock p.1,p.2)) :=
    (Ξ.continuous_clock.comp continuous_fst).prodMk continuous_snd
  unfold originalClockTimeField
  simp only [hessian,gradient,mixedHessian,mixedGradient,
    AdmissibleCovariance.toEvenMixture_clock]
  exact
    (((Ξ.continuous_second.comp continuous_fst).measurable.div_const 2).neg).mul
    (((Paper.continuous_parisiHessian_all (mixedBeta Ξ.toEvenMixture)
      (mixedMeasure Ξ.toEvenMixture μ)).comp hc).measurable.add
      (((Paper.parisiCDF_measurable μ).comp measurable_fst).mul
        (((Paper.continuous_parisiGradient (mixedBeta Ξ.toEvenMixture)
          (mixedMeasure Ξ.toEvenMixture μ)).comp hc).measurable.pow_const 2)))

theorem originalClockTimeField_eq_normalized (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (x : ℝ) :
    originalClockTimeField Ξ μ (q,x) =
      Paper.parisiTimeField (mixedBeta Ξ.toEvenMixture) (mixedMeasure Ξ.toEvenMixture μ) 0
        (Ξ.clock q,x) * (Ξ.second q/Ξ.variance) := by
  have ht := Ξ.clock_mem_unit hq
  have hH : Paper.parisiSpatialField (mixedBeta Ξ.toEvenMixture)
      (mixedMeasure Ξ.toEvenMixture μ) 2 (Ξ.clock q,x) =
      Paper.parisiHessian (mixedBeta Ξ.toEvenMixture)
        (mixedMeasure Ξ.toEvenMixture μ) (Ξ.clock q,x) :=
    FRSB.backwardC_eq_hessian _ _ _ _ ht
  rw [Paper.parisiTimeField,Paper.parisiSquareSpatialField_zero,hH]
  simp only [Nat.zero_add,mixedBeta_sq,AdmissibleCovariance.toEvenMixture_variance]
  rw [←AdmissibleCovariance.toEvenMixture_clock Ξ q,parisiCDF_mixedMeasure _ _ q hq]
  simp only [originalClockTimeField,hessian,gradient,mixedHessian,mixedGradient,
    AdmissibleCovariance.toEvenMixture_clock]
  field_simp [Ξ.variance_pos.ne']

theorem ae_hasDerivAt_potential_originalClock (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (x : ℝ) : ∀ᵐ q ∂volume, q ∈ Ioo (0 : ℝ) 1 →
      HasDerivAt (fun s => potential Ξ μ s x) (originalClockTimeField Ξ μ (q,x)) q := by
  let ν := mixedMeasure Ξ.toEvenMixture μ
  let β := mixedBeta Ξ.toEvenMixture
  let S := {q : ℝ | q ∈ Ioo (0 : ℝ) 1 ∧ ¬ContinuousAt (Paper.parisiCDF ν) (Ξ.clock q)}
  have hS : S.Countable := by
    apply Set.MapsTo.countable_of_injOn (f := Ξ.clock)
      (t := {t : ℝ | ¬ContinuousAt (Paper.parisiCDF ν) t})
      (fun q hq => hq.2)
    · exact Ξ.clock_strictMonoOn.injOn.mono (fun q hq => hq.1.1.le)
    · exact (Paper.parisiCDF_monotone ν).countable_not_continuousAt
  filter_upwards [hS.ae_notMem volume] with q hq hqu
  have ht : Ξ.clock q ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · simpa only [Ξ.clock_zero] using Ξ.clock_strictMonoOn
        (show (0 : ℝ) ∈ Ici 0 by simp) hqu.1.le hqu.1
    · simpa only [Ξ.clock_one] using Ξ.clock_strictMonoOn hqu.1.le
        (show (1 : ℝ) ∈ Ici 0 by norm_num) hqu.2
  have hCDF : ContinuousAt (Paper.parisiCDF ν) (Ξ.clock q) := by
    by_contra hn
    exact hq ⟨hqu,hn⟩
  have hc : ContinuousAt (Paper.parisiTimeField β ν 0) (Ξ.clock q,x) := by
    have hcf : ContinuousAt (fun p : ℝ × ℝ => Paper.parisiCDF ν p.1) (Ξ.clock q,x) :=
      hCDF.comp_of_eq continuousAt_fst rfl
    change ContinuousAt (fun p : ℝ × ℝ => -(β^2/2) *
      (Paper.parisiSpatialField β ν 2 p + Paper.parisiCDF ν p.1 *
        Paper.parisiSquareSpatialField β ν 0 p)) (Ξ.clock q,x)
    exact continuousAt_const.mul
      ((Paper.continuous_parisiSpatialField β ν 2).continuousAt.add
        (hcf.mul
          (Paper.continuous_parisiSquareSpatialField β ν 0).continuousAt))
  have hd := (hasDerivAt_time_of_weak_continuousAt _ _
    (Paper.continuous_parisiPotential β ν)
    (Paper.isParisiWeakTimeDerivative_potential β (mixedBeta_ne_zero _) ν)
    (Paper.measurable_parisiTimeField β ν 0) _ x ht hc).comp q (Ξ.hasDerivAt_clock q)
  rw [originalClockTimeField_eq_normalized Ξ μ ⟨hqu.1.le,hqu.2.le⟩ x]
  simpa only [potential,mixedPotential,AdmissibleCovariance.toEvenMixture_clock,
    Function.comp_def,β,ν] using hd

theorem absolutelyContinuous_potential_originalClock (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) (x : ℝ) :
    AbsolutelyContinuousOnInterval (fun q => potential Ξ μ q x) 0 1 := by
  let β := mixedBeta Ξ.toEvenMixture
  let ν := mixedMeasure Ξ.toEvenMixture μ
  obtain ⟨M,hM⟩ := Paper.parisiTimeField_bounded β ν 0
  have hLip := lipschitzOnWith_weakTime_section _ _
    (Paper.continuous_parisiPotential β ν)
    (Paper.isParisiWeakTimeDerivative_potential β (mixedBeta_ne_zero _) ν)
    (Paper.measurable_parisiTimeField β ν 0) M hM x
  have hclock : ContDiff ℝ ∞ Ξ.clock := Ξ.contDiff_first.div_const Ξ.variance
  have hh : AbsolutelyContinuousOnInterval
      (fun q => Paper.parisiPotential β ν (Ξ.clock q,x)) 0 1 :=
    hLip.comp_absolutelyContinuousOnInterval
    (by intro q hq; exact Ξ.clock_mem_unit (by simpa only [uIcc_of_le zero_le_one] using hq))
      (hclock.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).contDiffOn.absolutelyContinuousOnInterval
  simpa only [potential,mixedPotential,AdmissibleCovariance.toEvenMixture_clock,β,ν] using hh

theorem originalClockTimeField_bounded_strip (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) :
    ∃ M ≥ 0, ∀ q ∈ Icc (0 : ℝ) 1, ∀ x, ‖originalClockTimeField Ξ μ (q,x)‖ ≤ M := by
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    Ξ.continuous_second.continuousOn
  refine ⟨max B 0,le_max_right _ _,fun q hq x => ?_⟩
  have hh : ‖hessian Ξ μ q x‖ ≤ 1 := Paper.norm_parisiHessian_le_one_all _ _ _
  have hg : ‖gradient Ξ μ q x‖ ≤ 1 := norm_mixedGradient_le_one _ _ _
  have hc : ‖Paper.parisiCDF μ q‖ ≤ 1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (Paper.parisiCDF_nonneg μ q)]
    exact Paper.parisiCDF_le_one μ q
  have hgs : ‖gradient Ξ μ q x ^ 2‖ ≤ 1 := by
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) hg 2).trans_eq (by norm_num)
  have hsum : ‖hessian Ξ μ q x + Paper.parisiCDF μ q * gradient Ξ μ q x ^ 2‖ ≤ 2 :=
    (norm_add_le _ _).trans (by rw [norm_mul]; nlinarith [norm_nonneg (gradient Ξ μ q x ^ 2)])
  have hs := (hB q hq).trans (le_max_left B 0)
  rw [originalClockTimeField,norm_mul,norm_neg,norm_div,Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans (by linarith)

end GeneralDepthPaper
