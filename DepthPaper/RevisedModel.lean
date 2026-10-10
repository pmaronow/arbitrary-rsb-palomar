module

public import DepthPaper.RevisedCovariance
public import FourPapersCommon.MixedClockDynamics
public import FourPapersCommon.MixedFirstVariation

set_option backward.privateInPublic true

@[expose] public section

/-! The actual mixed Parisi model for every finite positive even covariance,
including quadratic interactions. No minimizing or regularity assertion is
assumed as part of the covariance or measure data. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ContDiff
namespace DepthPaper.RevisedCovariance
open FourPapersCommon
set_option maxHeartbeats 500000

abbrev ParisiMeasure := Paper.ParisiMeasure
abbrev Overlap := Paper.Overlap
abbrev BrownianSample := Paper.BrownianSample

def potential (Ξ : RevisedCovariance) (μ : ParisiMeasure) (q x : ℝ) : ℝ :=
  mixedPotential Ξ.toEvenMixture μ (q,x)

def gradient (Ξ : RevisedCovariance) (μ : ParisiMeasure) (q x : ℝ) : ℝ :=
  mixedGradient Ξ.toEvenMixture μ (q,x)

def hessian (Ξ : RevisedCovariance) (μ : ParisiMeasure) (q x : ℝ) : ℝ :=
  mixedHessian Ξ.toEvenMixture μ (q,x)

def optimalState (Ξ : RevisedCovariance) (μ : ParisiMeasure)
    (sample : BrownianSample) (q : ℝ) : ℝ :=
  mixedState Ξ.toEvenMixture 0 μ sample q

def Gamma (Ξ : RevisedCovariance) (μ : ParisiMeasure) : ℝ→ℝ :=
  mixedGamma Ξ.toEvenMixture 0 μ

def curvatureMoment (Ξ : RevisedCovariance) (μ : ParisiMeasure) : ℝ→ℝ :=
  mixedCurvatureMoment2 Ξ.toEvenMixture 0 μ

def firstVariation (Ξ : RevisedCovariance) (μ : ParisiMeasure) : ℝ→ℝ :=
  mixedFirstVariation Ξ.toEvenMixture 0 μ

def parisiFunctional (Ξ : RevisedCovariance) : ParisiMeasure→ℝ :=
  mixedFunctional Ξ.toEvenMixture 0

def parisiPressure (Ξ : RevisedCovariance) : ℝ :=
  mixedPressure Ξ.toEvenMixture 0

def IsParisiMinimizer (Ξ : RevisedCovariance) (μ : ParisiMeasure) : Prop :=
  IsMixedMinimizer Ξ.toEvenMixture 0 μ

theorem parisiFunctional_eq (Ξ : RevisedCovariance) (μ : ParisiMeasure) :
    parisiFunctional Ξ μ = Real.log 2+potential Ξ μ 0 0-
      (1/2:ℝ)*∫q in (0:ℝ)..1,q*Ξ.second q*Paper.parisiCDF μ q := by
  simp only [parisiFunctional,mixedFunctional,potential,
    RevisedCovariance.toEvenMixture_second]

theorem firstVariation_eq (Ξ : RevisedCovariance) (μ : ParisiMeasure) (q : ℝ) :
    firstVariation Ξ μ q = (1/2:ℝ)*∫s in (0:ℝ)..q,Ξ.second s*(Gamma Ξ μ s-s) := by
  simp only [firstVariation,mixedFirstVariation,RevisedCovariance.toEvenMixture_second,Gamma]

theorem optimalState_integral_equation (Ξ : RevisedCovariance) (μ : ParisiMeasure)
    (sample : BrownianSample) {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    optimalState Ξ μ sample q = mixedBeta Ξ.toEvenMixture*
      Paper.canonicalBrownian (Ξ.clock q).toNNReal sample+
      ∫s in 0..q,Ξ.second s*Paper.parisiCDF μ s*gradient Ξ μ s (optimalState Ξ μ sample s) := by
  simpa only [zero_add,RevisedCovariance.toEvenMixture_clock,
    RevisedCovariance.toEvenMixture_second,optimalState,gradient] using
    mixedState_integral_equation Ξ.toEvenMixture 0 μ sample hq

theorem hasDerivAt_Gamma (Ξ : RevisedCovariance) (μ : ParisiMeasure)
    {q : ℝ} (hq : q∈Ioo (0:ℝ) 1) :
    HasDerivAt (Gamma Ξ μ) (Ξ.second q*curvatureMoment Ξ μ q) q := by
  simpa only [Gamma,curvatureMoment,RevisedCovariance.toEvenMixture_second] using
    hasDerivAt_mixedGamma Ξ.toEvenMixture 0 μ hq

theorem hasDerivWithinAt_Gamma (Ξ : RevisedCovariance) (μ : ParisiMeasure)
    {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (Gamma Ξ μ) (Ξ.second q*curvatureMoment Ξ μ q) (Icc (0:ℝ) 1) q := by
  simpa only [Gamma,curvatureMoment,RevisedCovariance.toEvenMixture_second] using
    hasDerivWithinAt_mixedGamma Ξ.toEvenMixture 0 μ hq

theorem contDiffOn_Gamma_one (Ξ : RevisedCovariance) (μ : ParisiMeasure) :
    ContDiffOn ℝ 1 (Gamma Ξ μ) (Icc (0:ℝ) 1) :=
  contDiffOn_mixedGamma_one Ξ.toEvenMixture 0 μ

theorem continuousOn_Gamma (Ξ : RevisedCovariance) (μ : ParisiMeasure) :
    ContinuousOn (Gamma Ξ μ) (Icc (0:ℝ) 1) :=
  continuousOn_mixedGamma Ξ.toEvenMixture 0 μ

@[simp] theorem Gamma_zero (Ξ : RevisedCovariance) (μ : ParisiMeasure) :
    Gamma Ξ μ 0=0 := mixedGamma_zero Ξ.toEvenMixture μ

theorem Gamma_nonneg (Ξ : RevisedCovariance) (μ : ParisiMeasure) (q : ℝ) :
    0 ≤ Gamma Ξ μ q := mixedGamma_nonneg Ξ.toEvenMixture 0 μ q

theorem Gamma_le_one (Ξ : RevisedCovariance) (μ : ParisiMeasure) (q : ℝ) :
    Gamma Ξ μ q ≤ 1 := mixedGamma_le_one Ξ.toEvenMixture 0 μ q

theorem curvatureMoment_nonneg (Ξ : RevisedCovariance) (μ : ParisiMeasure) (q : ℝ) :
    0 ≤ curvatureMoment Ξ μ q := mixedCurvatureMoment2_nonneg Ξ.toEvenMixture 0 μ q

theorem curvatureMoment_le_one (Ξ : RevisedCovariance) (μ : ParisiMeasure) (q : ℝ) :
    curvatureMoment Ξ μ q ≤ 1 := mixedCurvatureMoment2_le_one Ξ.toEvenMixture 0 μ q

theorem curvatureMoment_le_one_sub_Gamma (Ξ : RevisedCovariance) (μ : ParisiMeasure)
    {q : ℝ} (hq : q∈Icc (0:ℝ) 1) : curvatureMoment Ξ μ q ≤ 1-Gamma Ξ μ q :=
  mixedCurvatureMoment2_le_one_sub_Gamma Ξ.toEvenMixture 0 μ hq

@[simp] theorem firstVariation_zero (Ξ : RevisedCovariance) (μ : ParisiMeasure) :
    firstVariation Ξ μ 0=0 := mixedFirstVariation_zero Ξ.toEvenMixture 0 μ

def GammaPrime (Ξ : RevisedCovariance) (μ : ParisiMeasure) (q : ℝ) : ℝ :=
  Ξ.second q*curvatureMoment Ξ μ q

theorem GammaPrime_nonneg (Ξ : RevisedCovariance) (μ : ParisiMeasure)
    {q : ℝ} (hq : q∈Icc (0:ℝ) 1) : 0≤GammaPrime Ξ μ q :=
  mul_nonneg (Ξ.second_nonneg hq.1) (curvatureMoment_nonneg Ξ μ q)

theorem GammaPrime_le (Ξ : RevisedCovariance) (μ : ParisiMeasure)
    {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    GammaPrime Ξ μ q≤Ξ.second q*(1-Gamma Ξ μ q) :=
  mul_le_mul_of_nonneg_left (curvatureMoment_le_one_sub_Gamma Ξ μ hq)
    (Ξ.second_nonneg hq.1)

theorem derivWithin_Gamma (Ξ : RevisedCovariance) (μ : ParisiMeasure)
    {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    derivWithin (Gamma Ξ μ) (Icc (0:ℝ) 1) q=GammaPrime Ξ μ q :=
  (hasDerivWithinAt_Gamma Ξ μ hq).derivWithin (uniqueDiffOn_Icc (by norm_num) q hq)

theorem Gamma_le_first (Ξ : RevisedCovariance) (μ : ParisiMeasure)
    {q : ℝ} (hq : q∈Icc (0:ℝ) 1) : Gamma Ξ μ q≤Ξ.first q := by
  have hm : MonotoneOn (fun s=>Ξ.first s-Gamma Ξ μ s) (Icc (0:ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (Ξ.continuous_first.continuousOn.sub (continuousOn_Gamma Ξ μ))
        (f':=fun s=>Ξ.second s-Ξ.second s*curvatureMoment Ξ μ s)
    · intro s hs
      rw [interior_Icc] at hs
      exact ((Ξ.hasDerivAt_first s).sub (hasDerivAt_Gamma Ξ μ hs)).hasDerivWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hn := Ξ.second_nonneg hs.1.le
      have hc := curvatureMoment_le_one Ξ μ s
      nlinarith
  have hh := hm (by norm_num : (0:ℝ)∈Icc (0:ℝ) 1) hq hq.1
  simpa only [Ξ.first_zero,Gamma_zero,sub_self,sub_nonneg] using hh

theorem norm_gradient_le_one (Ξ : RevisedCovariance) (μ : ParisiMeasure)
    (q x : ℝ) : ‖gradient Ξ μ q x‖≤1 :=
  FourPapersCommon.norm_mixedGradient_le_one Ξ.toEvenMixture μ (q,x)

theorem hessian_pos (Ξ : RevisedCovariance) (μ : ParisiMeasure)
    {q : ℝ} (hq : q∈Icc (0:ℝ) 1) (x : ℝ) : 0<hessian Ξ μ q x :=
  FourPapersCommon.mixedHessian_pos Ξ.toEvenMixture μ q x hq

theorem hessian_le_one_sub_gradient_sq (Ξ : RevisedCovariance) (μ : ParisiMeasure)
    (q x : ℝ) : hessian Ξ μ q x≤1-gradient Ξ μ q x^2 := by
  have h := FourPapersCommon.mixedHessian_add_gradient_sq_le_one Ξ.toEvenMixture μ (q,x)
  change hessian Ξ μ q x+gradient Ξ μ q x^2≤1 at h
  linarith

private theorem firstVariation_source_continuousOn (Ξ : RevisedCovariance)
    (μ : ParisiMeasure) :
    ContinuousOn (fun s=>Ξ.second s*(Gamma Ξ μ s-s)) (Icc (0:ℝ) 1) :=
  Ξ.continuous_second.continuousOn.mul ((continuousOn_Gamma Ξ μ).sub continuousOn_id)

theorem continuousOn_firstVariation (Ξ : RevisedCovariance) (μ : ParisiMeasure) :
    ContinuousOn (firstVariation Ξ μ) (Icc (0:ℝ) 1) := by
  have hi : IntegrableOn (fun s=>Ξ.second s*(Gamma Ξ μ s-s)) (uIcc (0:ℝ) 1) := by
    rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)]
    exact (firstVariation_source_continuousOn Ξ μ).integrableOn_compact isCompact_Icc
  have hc := intervalIntegral.continuousOn_primitive_interval hi
  rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)] at hc
  have he : firstVariation Ξ μ=(fun q=>(1/2:ℝ)*∫s in 0..q,Ξ.second s*(Gamma Ξ μ s-s)) :=
    funext (firstVariation_eq Ξ μ)
  rw [he]
  exact hc.const_mul (1/2:ℝ)

theorem hasDerivAt_firstVariation (Ξ : RevisedCovariance) (μ : ParisiMeasure)
    {q : ℝ} (hq : q∈Ioo (0:ℝ) 1) :
    HasDerivAt (firstVariation Ξ μ) ((1/2:ℝ)*Ξ.second q*(Gamma Ξ μ q-q)) q := by
  have hc := firstVariation_source_continuousOn Ξ μ
  have hi : IntervalIntegrable (fun s=>Ξ.second s*(Gamma Ξ μ s-s)) volume 0 q :=
    (hc.mono (Icc_subset_Icc_right hq.2.le)).intervalIntegrable_of_Icc hq.1.le
  have hca := hc.continuousAt (Icc_mem_nhds hq.1 hq.2)
  have hd := (intervalIntegral.integral_hasDerivAt_right hi
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
      (hc.mono Ioo_subset_Icc_self) q hq) hca).const_mul (1/2:ℝ)
  have he : firstVariation Ξ μ=(fun q=>(1/2:ℝ)*∫s in 0..q,Ξ.second s*(Gamma Ξ μ s-s)) :=
    funext (firstVariation_eq Ξ μ)
  rw [he]
  simpa only [mul_assoc] using hd

theorem continuous_firstVariation_overlap (Ξ : RevisedCovariance) (μ : ParisiMeasure) :
    Continuous (fun q : Overlap=>firstVariation Ξ μ q) :=
  (continuousOn_firstVariation Ξ μ).comp_continuous continuous_subtype_val
    (fun q=>q.property)

theorem hasDerivWithinAt_parisiFunctional_mix (Ξ : RevisedCovariance)
    (μ ν : ParisiMeasure) :
    HasDerivWithinAt (fun ε=>parisiFunctional Ξ (Paper.parisiMix μ ν ε))
      (-((∫q : Overlap,firstVariation Ξ μ q ∂(ν : Measure Overlap))-
        (∫q : Overlap,firstVariation Ξ μ q ∂(μ : Measure Overlap)))) (Ioi (0:ℝ)) 0 := by
  have hd := hasDerivWithinAt_mixedFunctional_mix_tail Ξ.toEvenMixture 0 μ ν
  have hf : Continuous (fun q : Overlap=>mixedFirstVariation Ξ.toEvenMixture 0 μ q) :=
    continuous_firstVariation_overlap Ξ μ
  have he : ∀ ρ : ParisiMeasure,
      (∫q,mixedTailVariation Ξ.toEvenMixture 0 μ q ∂(ρ : Measure Overlap)) =
        mixedFirstVariation Ξ.toEvenMixture 0 μ 1-
        ∫q,mixedFirstVariation Ξ.toEvenMixture 0 μ q ∂(ρ : Measure Overlap) := by
    intro ρ
    simp_rw [mixedTailVariation_eq_total_sub]
    rw [integral_sub (integrable_const _) (Paper.integrable_overlap_continuous hf ρ)]
    simp only [integral_const,probReal_univ,one_smul]
  rw [he ν,he μ] at hd
  convert hd using 1 <;> dsimp only [parisiFunctional,firstVariation] <;> ring

theorem isParisiMinimizer_iff_support_firstVariation_max
    (Ξ : RevisedCovariance) (μ : ParisiMeasure) :
    IsParisiMinimizer Ξ μ ↔ ∀q∈(μ : Measure Overlap).support,
      ∀r : Overlap,firstVariation Ξ μ r≤firstVariation Ξ μ q :=
  isMixedMinimizer_iff_support_firstVariation_max Ξ.toEvenMixture 0 μ

theorem isParisiMinimizer_of_nonpos_zero_support
    (Ξ : RevisedCovariance) (μ : ParisiMeasure)
    (hle : ∀q∈Icc (0:ℝ) 1,firstVariation Ξ μ q≤0)
    (hzero : ∀q∈(μ : Measure Overlap).support,firstVariation Ξ μ q=0) :
    IsParisiMinimizer Ξ μ := by
  apply (isParisiMinimizer_iff_support_firstVariation_max Ξ μ).mpr
  intro q hq r
  rw [hzero q hq]
  exact hle r r.property

/-- Proposition 2.1's literal full-mass criterion. Continuity transfers its
almost-everywhere contact statement to the entire topological support. -/
theorem isParisiMinimizer_of_nonpos_full_zero_mass
    (Ξ : RevisedCovariance) (μ : ParisiMeasure)
    (hle : ∀q∈Icc (0:ℝ) 1,firstVariation Ξ μ q≤0)
    (hmass : (μ : Measure Overlap) {q|firstVariation Ξ μ q=0}=1) :
    IsParisiMinimizer Ξ μ := by
  have hclosed : IsClosed {q : Overlap|firstVariation Ξ μ q=0} :=
    isClosed_eq (continuous_firstVariation_overlap Ξ μ) continuous_const
  have hnull : (μ : Measure Overlap) {q|firstVariation Ξ μ q=0}ᶜ=0 := by
    rw [measure_compl hclosed.measurableSet (measure_ne_top _ _),hmass,measure_univ]
    simp
  exact isParisiMinimizer_of_nonpos_zero_support Ξ μ hle
    (fun q hq=>Measure.support_subset_of_isClosed hclosed (mem_ae_iff.mpr hnull) hq)

def parisiMinimizer (Ξ : RevisedCovariance) : ParisiMeasure :=
  mixedMinimizer Ξ.toEvenMixture 0

theorem isParisiMinimizer_selected (Ξ : RevisedCovariance) :
    IsParisiMinimizer Ξ (parisiMinimizer Ξ) :=
  isMixedMinimizer_selected Ξ.toEvenMixture 0

theorem parisiMinimizer_unique (Ξ : RevisedCovariance) (μ : ParisiMeasure)
    (hμ : IsParisiMinimizer Ξ μ) : μ=parisiMinimizer Ξ :=
  mixedMinimizer_unique Ξ.toEvenMixture 0 μ hμ

theorem existsUnique_parisiMinimizer (Ξ : RevisedCovariance) :
    ∃!μ,IsParisiMinimizer Ξ μ :=
  existsUnique_mixed_minimizer Ξ.toEvenMixture 0

theorem parisiMinimizer_value (Ξ : RevisedCovariance) :
    parisiFunctional Ξ (parisiMinimizer Ξ)=parisiPressure Ξ :=
  mixedMinimizer_value Ξ.toEvenMixture 0

theorem unique_minimizer_of_firstVariation_criterion
    (Ξ : RevisedCovariance) (μ : ParisiMeasure)
    (hle : ∀q∈Icc (0:ℝ) 1,firstVariation Ξ μ q≤0)
    (hmass : (μ : Measure Overlap) {q|firstVariation Ξ μ q=0}=1) :
    μ=parisiMinimizer Ξ :=
  parisiMinimizer_unique Ξ μ (isParisiMinimizer_of_nonpos_full_zero_mass Ξ μ hle hmass)

end DepthPaper.RevisedCovariance
