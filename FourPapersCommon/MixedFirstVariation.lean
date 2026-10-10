module

public import FourPapersCommon.MixedMinimizer
public import FourPapersCommon.MixedClockDynamics
public import Paper.ParisiFirstVariation
public import Paper.ParisiMixConvexity

@[expose] public section


/-! Actual directional derivatives of the mixed functional in its original
overlap coordinate, including arbitrary atomic cumulative masses. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace FourPapersCommon
set_option maxHeartbeats 500000

theorem hasDerivWithinAt_mixedPotential_mix (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ ν : Paper.ParisiMeasure) :
    HasDerivWithinAt (fun ε => mixedPotential ξ (Paper.parisiMix μ ν ε) (0,h))
      ((1/2:ℝ)*∫q in (0:ℝ)..1,ξ.second q*
        (Paper.parisiCDF ν q-Paper.parisiCDF μ q)*mixedGamma ξ h μ q)
      (Ioi (0:ℝ)) 0 := by
  let β := mixedBeta ξ
  let ρ := mixedMeasure ξ μ
  let σ := mixedMeasure ξ ν
  have hd := Paper.hasDerivWithinAt_parisiPotential_mix_control_right β h
    (mixedBeta_ne_zero ξ) ρ σ
  rw [Paper.integral_selectedParisiControlDerivative_of_terminal_pairing β h
    (mixedBeta_ne_zero ξ) ρ σ
    (fun s hs => Paper.selectedParisiFeedbackControl_terminal_pairing β h
      (mixedBeta_ne_zero ξ) ρ s hs)] at hd
  let g : ℝ → ℝ := fun s => (Paper.parisiCDF σ s-Paper.parisiCDF ρ s)*
    Paper.selectedParisiSecondMoment β h (mixedBeta_ne_zero ξ) ρ s
  have hi := integral_mixedClock_substitution ξ g (q:=1) (by norm_num)
  rw [ξ.clock_one] at hi
  have he : β^2/2*(∫s in (0:ℝ)..1,g s) =
      (1/2:ℝ)*∫q in (0:ℝ)..1,ξ.second q*
        (Paper.parisiCDF ν q-Paper.parisiCDF μ q)*mixedGamma ξ h μ q := by
    rw [←hi,←intervalIntegral.integral_const_mul,
      ←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro q hq
    rw [uIcc_of_le zero_le_one] at hq
    dsimp only [g,β,ρ,σ]
    rw [parisiCDF_mixedMeasure ξ ν q hq,parisiCDF_mixedMeasure ξ μ q hq,
      ←mixedGamma_eq_selected,mixedBeta_sq]
    field_simp [ξ.variance_pos.ne']
  change HasDerivWithinAt _ (β^2/2*(∫s in (0:ℝ)..1,g s)) _ _ at hd
  rw [he] at hd
  apply hd.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono
        (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)) (a:=0))] with ε hε hε1
    simp only [mixedPotential,ξ.clock_zero,
      mixedMeasure_mix ξ μ ν ε ⟨hε.le,hε1.le⟩,β,ρ,σ]
  · simp only [mixedPotential,ξ.clock_zero,Paper.parisiMix_zero,β,ρ]

theorem mixedMomentWeight_intervalIntegrable (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ ν : Paper.ParisiMeasure) : IntervalIntegrable
      (fun q => ξ.second q*(mixedGamma ξ h μ q-q)*Paper.parisiCDF ν q)
      volume 0 1 := by
  have hc : ContinuousOn (fun q => ξ.second q*(mixedGamma ξ h μ q-q)) (uIcc (0:ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact (ξ.continuousOn_second.mono
      (fun _ hq => ⟨by linarith [hq.1],hq.2⟩)).mul
        ((continuousOn_mixedGamma ξ h μ).sub continuousOn_id)
  simpa only [mul_comm] using (Paper.parisiCDF_monotone ν).intervalIntegrable.mul_continuousOn hc

theorem hasDerivWithinAt_mixedFunctional_mix_cdf (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ ν : Paper.ParisiMeasure) :
    HasDerivWithinAt (fun ε => mixedFunctional ξ h (Paper.parisiMix μ ν ε))
      ((1/2:ℝ)*∫q in (0:ℝ)..1,ξ.second q*
        (Paper.parisiCDF ν q-Paper.parisiCDF μ q)*(mixedGamma ξ h μ q-q))
      (Ioi (0:ℝ)) 0 := by
  have hp := hasDerivWithinAt_mixedPotential_mix ξ h μ ν
  have hc := (Paper.hasDerivWithinAt_of_affine_mixing
    (weightedCDFIntegral_mix _ (continuousOn_mixedCorrectionWeight ξ) μ ν)).const_mul (1/2:ℝ)
  have hd := ((hasDerivAt_const (0:ℝ) (Real.log 2)).hasDerivWithinAt.add hp).sub hc
  have hI (ρ : Paper.ParisiMeasure) : IntervalIntegrable
      (fun q => q*ξ.second q*Paper.parisiCDF ρ q) volume 0 1 := by
    have hw : ContinuousOn (fun q : ℝ => q*ξ.second q) (uIcc (0:ℝ) 1) := by
      rw [uIcc_of_le zero_le_one]
      exact continuousOn_mixedCorrectionWeight ξ
    simpa only [mul_comm] using
      (Paper.parisiCDF_monotone ρ).intervalIntegrable.mul_continuousOn hw
  have hG : IntervalIntegrable (fun q => ξ.second q*
      (Paper.parisiCDF ν q-Paper.parisiCDF μ q)*mixedGamma ξ h μ q) volume 0 1 := by
    have hv := (mixedMomentWeight_intervalIntegrable ξ h μ ν).add (hI ν)
    have hu := (mixedMomentWeight_intervalIntegrable ξ h μ μ).add (hI μ)
    convert hv.sub hu using 1
    funext q
    ring
  have he : (0+(1/2:ℝ)*∫q in (0:ℝ)..1,ξ.second q*
      (Paper.parisiCDF ν q-Paper.parisiCDF μ q)*mixedGamma ξ h μ q) -
      (1/2:ℝ)*(weightedCDFIntegral (fun q => q*ξ.second q) ν-
        weightedCDFIntegral (fun q => q*ξ.second q) μ) =
      (1/2:ℝ)*∫q in (0:ℝ)..1,ξ.second q*
        (Paper.parisiCDF ν q-Paper.parisiCDF μ q)*(mixedGamma ξ h μ q-q) := by
    unfold weightedCDFIntegral
    rw [zero_add,←intervalIntegral.integral_sub (hI ν) (hI μ),
      ←mul_sub,←intervalIntegral.integral_sub hG ((hI ν).sub (hI μ))]
    congr 1
    apply intervalIntegral.integral_congr
    intro q _
    ring
  exact hd.congr_deriv he

theorem mixedFunctional_mix_le (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ ν : Paper.ParisiMeasure) (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
    mixedFunctional ξ h (Paper.parisiMix μ ν t) ≤
      (1-t)*mixedFunctional ξ h μ+t*mixedFunctional ξ h ν := by
  by_cases hne : μ=ν
  · subst ν
    have hm : Paper.parisiMix μ μ t=μ := by
      apply probabilityMeasure_eq_of_cdf_on_unit
      intro q hq
      rw [Paper.parisiCDF_mix μ μ t q ht]
      ring
    rw [hm]
    nlinarith
  · rcases ht.1.eq_or_lt with h0 | h0
    · simp only [←h0,Paper.parisiMix_zero,sub_zero,one_mul,zero_mul,add_zero,le_refl]
    rcases ht.2.eq_or_lt with h1 | h1
    · simp only [h1,Paper.parisiMix_one,sub_self,zero_mul,one_mul,zero_add,le_refl]
    exact (mixedFunctional_mix_lt ξ h μ ν hne t ⟨h0,h1⟩).le

theorem convexOn_mixedFunctional_mix (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ ν : Paper.ParisiMeasure) :
    ConvexOn ℝ (Icc (0:ℝ) 1) (fun ε => mixedFunctional ξ h (Paper.parisiMix μ ν ε)) := by
  refine ⟨convex_Icc _ _,?_⟩
  intro a ha b hb u v hu hv huv
  have hv1 : v∈Icc (0:ℝ) 1 := ⟨hv,by linarith⟩
  have hu1 : 1-v=u := by linarith
  have he := mixedFunctional_mix_le ξ h (Paper.parisiMix μ ν a) (Paper.parisiMix μ ν b) v hv1
  rw [Paper.parisiMix_parisiMix μ ν a b v ha hb hv1,hu1] at he
  simpa only [smul_eq_mul] using he

def mixedTailVariation (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) : ℝ :=
  weightedTail (fun s => (1/2:ℝ)*ξ.second s*(mixedGamma ξ h μ s-s)) q

theorem continuousOn_mixedVariationWeight (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : Paper.ParisiMeasure) :
    ContinuousOn (fun s => (1/2:ℝ)*ξ.second s*(mixedGamma ξ h μ s-s)) (Icc (0:ℝ) 1) :=
  (continuousOn_const.mul (ξ.continuousOn_second.mono
    (fun _ hs => ⟨by linarith [hs.1],hs.2⟩))).mul
      ((continuousOn_mixedGamma ξ h μ).sub continuousOn_id)

theorem continuous_mixedTailVariation (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : Paper.ParisiMeasure) : Continuous (mixedTailVariation ξ h μ) :=
  continuous_weightedTail _ (continuousOn_mixedVariationWeight ξ h μ)

theorem integral_mixedTailVariation_sub_eq_cdf (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ ν : Paper.ParisiMeasure) :
    (∫q,mixedTailVariation ξ h μ q ∂(ν : Measure Paper.Overlap))-
      (∫q,mixedTailVariation ξ h μ q ∂(μ : Measure Paper.Overlap)) =
      (1/2:ℝ)*∫q in (0:ℝ)..1,ξ.second q*
        (Paper.parisiCDF ν q-Paper.parisiCDF μ q)*(mixedGamma ξ h μ q-q) := by
  change (∫q,weightedTail _ q ∂(ν : Measure Paper.Overlap))-
      (∫q,weightedTail _ q ∂(μ : Measure Paper.Overlap)) = _
  rw [←weightedCDFIntegral_eq_measure_integral _
      (continuousOn_mixedVariationWeight ξ h μ) ν,
    ←weightedCDFIntegral_eq_measure_integral _
      (continuousOn_mixedVariationWeight ξ h μ) μ]
  unfold weightedCDFIntegral
  have hI (ρ : Paper.ParisiMeasure) : IntervalIntegrable
      (fun q => (1/2:ℝ)*ξ.second q*(mixedGamma ξ h μ q-q)*Paper.parisiCDF ρ q) volume 0 1 := by
    convert (mixedMomentWeight_intervalIntegrable ξ h μ ρ).const_mul (1/2:ℝ) using 1
    funext q
    ring
  rw [←intervalIntegral.integral_sub (hI ν) (hI μ),←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro q _
  ring

theorem hasDerivWithinAt_mixedFunctional_mix_tail (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ ν : Paper.ParisiMeasure) :
    HasDerivWithinAt (fun ε => mixedFunctional ξ h (Paper.parisiMix μ ν ε))
      ((∫q,mixedTailVariation ξ h μ q ∂(ν : Measure Paper.Overlap))-
        (∫q,mixedTailVariation ξ h μ q ∂(μ : Measure Paper.Overlap)))
      (Ioi (0:ℝ)) 0 := by
  rw [integral_mixedTailVariation_sub_eq_cdf]
  exact hasDerivWithinAt_mixedFunctional_mix_cdf ξ h μ ν

theorem isMixedMinimizer_iff_support_tail_argmin (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : Paper.ParisiMeasure) :
    IsMixedMinimizer ξ h μ ↔ (μ : Measure Paper.Overlap).support ⊆
      Paper.overlapArgmin (mixedTailVariation ξ h μ) :=
  Paper.jt_support_criterion_of_firstVariation (mixedFunctional ξ h) μ _
    (continuous_mixedTailVariation ξ h μ)
    (convexOn_mixedFunctional_mix ξ h μ)
    (hasDerivWithinAt_mixedFunctional_mix_tail ξ h μ)

theorem mixedTailVariation_eq_total_sub (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    mixedTailVariation ξ h μ q = mixedFirstVariation ξ h μ 1-
      mixedFirstVariation ξ h μ q := by
  have hc : ContinuousOn (fun s => ξ.second s*(mixedGamma ξ h μ s-s)) (Icc (0:ℝ) 1) :=
    (ξ.continuousOn_second.mono (fun _ hs => ⟨by linarith [hs.1],hs.2⟩)).mul
      ((continuousOn_mixedGamma ξ h μ).sub continuousOn_id)
  have hi : IntervalIntegrable (fun s => ξ.second s*(mixedGamma ξ h μ s-s)) volume 0 1 := by
    exact (show ContinuousOn _ (uIcc (0:ℝ) 1) by
      rw [uIcc_of_le zero_le_one];exact hc).intervalIntegrable
  have h0q : IntervalIntegrable (fun s => ξ.second s*(mixedGamma ξ h μ s-s)) volume 0 (q:ℝ) :=
    hi.mono_set (uIcc_subset_uIcc (by norm_num) (by
      rw [uIcc_of_le zero_le_one];exact q.property))
  have hq1 : IntervalIntegrable (fun s => ξ.second s*(mixedGamma ξ h μ s-s)) volume (q:ℝ) 1 :=
    hi.mono_set (uIcc_subset_uIcc (by
      rw [uIcc_of_le zero_le_one];exact q.property) (by norm_num))
  have he := intervalIntegral.integral_add_adjacent_intervals h0q hq1
  unfold mixedTailVariation weightedTail mixedFirstVariation
  simp_rw [show ∀ s,(1/2:ℝ)*ξ.second s*(mixedGamma ξ h μ s-s)=
    (1/2:ℝ)*(ξ.second s*(mixedGamma ξ h μ s-s)) by intro s;ring]
  rw [intervalIntegral.integral_const_mul]
  linarith

theorem isMixedMinimizer_iff_support_firstVariation_max (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : Paper.ParisiMeasure) :
    IsMixedMinimizer ξ h μ ↔ ∀q∈(μ : Measure Paper.Overlap).support,
      ∀r : Paper.Overlap,mixedFirstVariation ξ h μ r ≤ mixedFirstVariation ξ h μ q := by
  rw [isMixedMinimizer_iff_support_tail_argmin]
  simp only [subset_def,Paper.overlapArgmin,mem_ofPred_eq,mixedTailVariation_eq_total_sub]
  constructor
  · intro hh q hq r
    have := hh q hq r
    linarith
  · intro hh q hq r
    have := hh q hq r
    linarith

end FourPapersCommon
