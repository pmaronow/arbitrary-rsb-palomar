module

public import FourPapersCommon.MixedModel
public import FourPapersCommon.MixtureAnalysis
public import FourPapersCommon.AllFieldMoments

set_option backward.privateInPublic true

@[expose] public section


/-! The original-overlap dynamics of the constructed mixed Parisi model.
The Jacobian substitution is valid across atoms of the cumulative mass. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 500000

private theorem abs_unit_lt {q : ℝ} (hq : q∈Icc (0:ℝ) 1) : |q|<5/4 := by
  rw [abs_of_nonneg hq.1]
  linarith [hq.2]

private theorem clock_rate_nonneg (ξ : AdmissibleEvenMixture) {q : ℝ}
    (hq : 0≤q) : 0≤ ξ.second q/ξ.variance := by
  apply div_nonneg _ ξ.variance_pos.le
  unfold AdmissibleEvenMixture.second
  exact tsum_nonneg fun p=>mul_nonneg
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (ξ.nonneg p))
    (pow_nonneg hq _)

/-- Genuine substitution by the variance clock; no continuity of the integrand
is required, so cumulative mass jumps remain included. -/
theorem integral_mixedClock_substitution (ξ : AdmissibleEvenMixture)
    (g : ℝ→ℝ) {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    (∫s in 0..q,g (ξ.clock s)*(ξ.second s/ξ.variance)) =
      ∫t in 0..ξ.clock q,g t := by
  have hc : ContinuousOn ξ.clock (uIcc (0:ℝ) q) := by
    rw [uIcc_of_le hq.1]
    exact ξ.continuousOn_clock.mono (Icc_subset_Icc_right hq.2)
  have hd (s : ℝ) (hs : s∈Ioo (min (0:ℝ) q) (max (0:ℝ) q)) :
      HasDerivAt ξ.clock (ξ.second s/ξ.variance) s := by
    rw [min_eq_left hq.1,max_eq_right hq.1] at hs
    exact ξ.hasDerivAt_clock (abs_unit_lt ⟨hs.1.le,hs.2.le.trans hq.2⟩)
  have hn (s : ℝ) (hs : s∈Ioo (min (0:ℝ) q) (max (0:ℝ) q)) :
      0≤ ξ.second s/ξ.variance := by
    rw [min_eq_left hq.1,max_eq_right hq.1] at hs
    exact clock_rate_nonneg ξ hs.1.le
  simpa only [ξ.clock_zero,Function.comp_apply] using
    intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg hc hd hn (g:=g)

/-- The actual constructed state satisfies the manuscript's drift equation
in its original overlap coordinate. Its Gaussian driver has variance ξ′(q). -/
theorem mixedState_integral_equation (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : ParisiMeasure) (sample : BrownianSample) {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    mixedState ξ h μ sample q = h+mixedBeta ξ*Paper.canonicalBrownian (ξ.clock q).toNNReal sample+
      ∫s in 0..q,ξ.second s*Paper.parisiCDF μ s*
        mixedGradient ξ μ (s,mixedState ξ h μ sample s) := by
  let g : ℝ→ℝ := fun t=>mixedBeta ξ^2*Paper.parisiCDF (mixedMeasure ξ μ) t*
    Paper.parisiGradient (mixedBeta ξ) (mixedMeasure ξ μ)
      (t,Paper.selectedParisiStateReal (mixedBeta ξ) h (mixedBeta_ne_zero ξ)
        (mixedMeasure ξ μ) sample t)
  have he := Paper.selectedParisiState_integral_equation (mixedBeta ξ) h
    (mixedBeta_ne_zero ξ) (mixedMeasure ξ μ) sample (ξ.clock_mem_unitInterval hq)
  have hi := integral_mixedClock_substitution ξ g hq
  have hc : (∫s in 0..q,g (ξ.clock s)*(ξ.second s/ξ.variance)) =
      ∫s in 0..q,ξ.second s*Paper.parisiCDF μ s*
        mixedGradient ξ μ (s,mixedState ξ h μ sample s) := by
    apply intervalIntegral.integral_congr_uIoo
    rw [uIoo_of_le hq.1]
    intro s hs
    dsimp only [g]
    rw [mixedBeta_sq,parisiCDF_mixedMeasure ξ μ s ⟨hs.1.le,hs.2.le.trans hq.2⟩]
    unfold mixedGradient mixedState
    field_simp [ξ.variance_pos.ne']
  rw [hc] at hi
  change mixedState ξ h μ sample q = h+mixedBeta ξ*Paper.canonicalBrownian
    (ξ.clock q).toNNReal sample+∫t in 0..ξ.clock q,g t at he
  exact he.trans (congrArg (fun a=>h+mixedBeta ξ*Paper.canonicalBrownian
    (ξ.clock q).toNNReal sample+a) hi.symm)

def mixedCurvatureMoment2 (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : ParisiMeasure) (q : ℝ) : ℝ :=
  fieldCurvatureMoment2 (mixedBeta ξ) h (mixedBeta_ne_zero ξ) (mixedMeasure ξ μ) (ξ.clock q)

theorem mixedCurvatureMoment2_eq_integral (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : ParisiMeasure) {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    mixedCurvatureMoment2 ξ h μ q =
      ∫ sample,mixedHessian ξ μ (q,mixedState ξ h μ sample q)^2 ∂Paper.canonicalBrownianMeasure := by
  have hclock := ξ.clock_mem_unitInterval hq
  have hnn : ((ξ.clock q).toNNReal:ℝ)=ξ.clock q := Real.coe_toNNReal _ hclock.1
  unfold mixedCurvatureMoment2 fieldCurvatureMoment2
  apply integral_congr_ae
  exact .of_forall fun sample=>by
    change Paper.parisiHessian (mixedBeta ξ) (mixedMeasure ξ μ)
      (ξ.clock q,Paper.selectedParisiItoState (mixedBeta ξ) h (mixedBeta_ne_zero ξ)
        (mixedMeasure ξ μ) (ξ.clock q).toNNReal sample)^2 =
      Paper.parisiHessian (mixedBeta ξ) (mixedMeasure ξ μ)
      (ξ.clock q,Paper.selectedParisiStateReal (mixedBeta ξ) h (mixedBeta_ne_zero ξ)
        (mixedMeasure ξ μ) sample (ξ.clock q))^2
    rw [Paper.selectedParisiItoState_eq (mixedBeta ξ) h (mixedBeta_ne_zero ξ)
      (mixedMeasure ξ μ) (t := (ξ.clock q).toNNReal)
      (by simpa only [hnn] using hclock.2) sample,hnn]

theorem mixedCurvatureMoment2_nonneg (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : ParisiMeasure) (q : ℝ) : 0≤ mixedCurvatureMoment2 ξ h μ q :=
  integral_nonneg (fun _=>sq_nonneg _)

theorem mixedCurvatureMoment2_le_one (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : ParisiMeasure) (q : ℝ) : mixedCurvatureMoment2 ξ h μ q≤1 :=
  fieldCurvatureMoment2_le_one (mixedBeta ξ) h (mixedBeta_ne_zero ξ)
    (mixedMeasure ξ μ) (ξ.clock q)

theorem mixedCurvatureMoment2_pos (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : ParisiMeasure) {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    0< mixedCurvatureMoment2 ξ h μ q :=
  fieldCurvatureMoment2_pos (mixedBeta ξ) h (mixedBeta_ne_zero ξ)
    (mixedMeasure ξ μ) (ξ.clock_mem_unitInterval hq)

theorem mixedCurvatureMoment2_le_one_sub_Gamma (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : ParisiMeasure) {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    mixedCurvatureMoment2 ξ h μ q≤1-mixedGamma ξ h μ q := by
  have hq' := ξ.clock_mem_unitInterval hq
  have hg := Paper.integrable_selectedParisiSecondMoment_integrand (mixedBeta ξ) h
    (mixedBeta_ne_zero ξ) (mixedMeasure ξ μ) (ξ.clock q) hq'
  change Integrable (fun sample=>mixedGradient ξ μ (q,mixedState ξ h μ sample q)^2)
    Paper.canonicalBrownianMeasure at hg
  have hnn : ((ξ.clock q).toNNReal:ℝ)=ξ.clock q := Real.coe_toNNReal _ hq'.1
  have hcm : Integrable (fun sample=>mixedHessian ξ μ (q,mixedState ξ h μ sample q)^2)
      Paper.canonicalBrownianMeasure := by
    refine (integrable_fieldCurvature_square (mixedBeta ξ) h (mixedBeta_ne_zero ξ)
      (mixedMeasure ξ μ) (ξ.clock q)).congr (.of_forall fun sample=>?_) 
    change Paper.parisiHessian (mixedBeta ξ) (mixedMeasure ξ μ)
      (ξ.clock q,Paper.selectedParisiItoState (mixedBeta ξ) h (mixedBeta_ne_zero ξ)
        (mixedMeasure ξ μ) (ξ.clock q).toNNReal sample)^2 =
      Paper.parisiHessian (mixedBeta ξ) (mixedMeasure ξ μ)
      (ξ.clock q,Paper.selectedParisiStateReal (mixedBeta ξ) h (mixedBeta_ne_zero ξ)
        (mixedMeasure ξ μ) sample (ξ.clock q))^2
    rw [Paper.selectedParisiItoState_eq (mixedBeta ξ) h (mixedBeta_ne_zero ξ)
      (mixedMeasure ξ μ) (t := (ξ.clock q).toNNReal)
      (by simpa only [hnn] using hq'.2) sample,hnn]
  rw [mixedCurvatureMoment2_eq_integral ξ h μ hq]
  have hi := integral_mono hcm ((integrable_const (1:ℝ)).sub hg) (fun sample=>by
    let p : ℝ×ℝ := (q,mixedState ξ h μ sample q)
    have hc := mixedHessian_pos ξ μ q p.2 hq
    have hcg := mixedHessian_add_gradient_sq_le_one ξ μ p
    have hh : mixedHessian ξ μ p≤1 := by nlinarith [sq_nonneg (mixedGradient ξ μ p)]
    change mixedHessian ξ μ p^2≤1-mixedGradient ξ μ p^2
    nlinarith)
  simp only [Pi.sub_apply] at hi
  rw [integral_sub (integrable_const (1:ℝ)) hg,integral_const,probReal_univ,one_smul] at hi
  exact hi

/-- Every interior overlap, including atomic levels, has the genuine derivative. -/
theorem hasDerivAt_mixedGamma (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : ParisiMeasure) {q : ℝ} (hq : q∈Ioo (0:ℝ) 1) :
    HasDerivAt (mixedGamma ξ h μ) (ξ.second q*mixedCurvatureMoment2 ξ h μ q) q := by
  have hclock : ξ.clock q∈Ioo (0:ℝ) 1 := by
    constructor
    · simpa only [ξ.clock_zero] using ξ.clock_strictMonoOn
        (by norm_num : (0:ℝ)∈Icc (0:ℝ) 1) ⟨hq.1.le,hq.2.le⟩ hq.1
    · simpa only [ξ.clock_one] using ξ.clock_strictMonoOn
        ⟨hq.1.le,hq.2.le⟩ (by norm_num : (1:ℝ)∈Icc (0:ℝ) 1) hq.2
  have hd := (hasDerivAt_Gamma (mixedBeta ξ) h (mixedBeta_ne_zero ξ)
    (mixedMeasure ξ μ) hclock).comp q
      (ξ.hasDerivAt_clock (abs_unit_lt ⟨hq.1.le,hq.2.le⟩))
  have he : mixedBeta ξ^2*fieldCurvatureMoment2 (mixedBeta ξ) h (mixedBeta_ne_zero ξ)
      (mixedMeasure ξ μ) (ξ.clock q)*(ξ.second q/ξ.variance) =
      ξ.second q*mixedCurvatureMoment2 ξ h μ q := by
    unfold mixedCurvatureMoment2
    rw [mixedBeta_sq]
    field_simp [ξ.variance_pos.ne']
  rw [he] at hd
  exact hd

theorem hasDerivWithinAt_mixedGamma (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : ParisiMeasure) {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (mixedGamma ξ h μ) (ξ.second q*mixedCurvatureMoment2 ξ h μ q)
      (Icc (0:ℝ) 1) q := by
  have hd := (hasDerivWithinAt_Gamma (mixedBeta ξ) h (mixedBeta_ne_zero ξ)
    (mixedMeasure ξ μ) (ξ.clock_mem_unitInterval hq)).comp q
      (ξ.hasDerivAt_clock (abs_unit_lt hq)).hasDerivWithinAt
      (fun _ hs=>ξ.clock_mem_unitInterval hs)
  have he : mixedBeta ξ^2*fieldCurvatureMoment2 (mixedBeta ξ) h (mixedBeta_ne_zero ξ)
      (mixedMeasure ξ μ) (ξ.clock q)*(ξ.second q/ξ.variance) =
      ξ.second q*mixedCurvatureMoment2 ξ h μ q := by
    unfold mixedCurvatureMoment2
    rw [mixedBeta_sq]
    field_simp [ξ.variance_pos.ne']
  rw [he] at hd
  exact hd

theorem contDiffOn_mixedGamma_one (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : ParisiMeasure) : ContDiffOn ℝ 1 (mixedGamma ξ h μ) (Icc (0:ℝ) 1) := by
  have hc : ContDiffOn ℝ 1 ξ.clock (Icc (0:ℝ) 1) :=
    ((ξ.contDiffOn_first.of_le (by norm_num : (1:ℕ∞)≤∞)).mono
      (by intro q hq;exact ⟨by linarith [hq.1],hq.2⟩)).div_const _
  exact (contDiffOn_Gamma_one (mixedBeta ξ) h (mixedBeta_ne_zero ξ)
    (mixedMeasure ξ μ)).comp hc (fun _ hq=>ξ.clock_mem_unitInterval hq)

end FourPapersCommon
