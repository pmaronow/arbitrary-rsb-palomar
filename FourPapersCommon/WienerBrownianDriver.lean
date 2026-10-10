module

public import StochasticCalculus.WienerIntegral
public import BrownianMotion.Gaussian.BrownianMotion

@[expose] public section

/-! Deterministic Wiener kernels with Brownian Gram matrix give a genuine
continuous Brownian driver on the original probability space. The Gaussian
family and covariance statements also allow independence from an existing
Brownian past to be checked by kernel orthogonality. -/

noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Filter
open scoped InnerProductSpace NNReal ENNReal

namespace FourPapersCommon

variable {Ω T : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

/-- Finite collections of deterministic Wiener integrals are jointly Gaussian. -/
theorem isGaussianProcess_wienerIntegral (hB : IsPreBrownianReal B P)
    (f : T → Lp ℝ 2 nonnegativeLebesgueMeasure) :
    IsGaussianProcess (fun t ω => wienerIntegral hB (f t) ω) P where
  hasGaussianLaw I := by
    classical
    let X : Ω → I → ℝ := fun ω i => wienerIntegral hB (f i) ω
    have hX : AEMeasurable X P := AEMeasurable.of_eval fun i =>
      (Lp.aestronglyMeasurable (wienerIntegral hB (f i))).aemeasurable
    refine ⟨hX, isGaussian_of_isGaussian_map fun L => ?_⟩
    let c : I → ℝ := fun i => L (Pi.single i 1)
    let k : Lp ℝ 2 nonnegativeLebesgueMeasure := ∑ i : I, c i • f i
    have he : (fun ω => L (X ω)) =ᵐ[P] (wienerIntegral hB k : Ω → ℝ) := by
      have hsum := Lp.coeFn_finsetSum (Finset.univ : Finset I)
        (fun i => c i • wienerIntegral hB (f i))
      have hsmul : ∀ᵐ ω ∂P, ∀ i : I,
          (c i • wienerIntegral hB (f i)) ω = c i * wienerIntegral hB (f i) ω :=
        ae_all_iff.mpr fun i => by
          filter_upwards [Lp.coeFn_smul (c i) (wienerIntegral hB (f i))] with ω hω
          exact hω
      filter_upwards [hsum, hsmul] with ω hs hc
      have hmap : wienerIntegral hB k = ∑ i : I, c i • wienerIntegral hB (f i) := by
        simp only [k, map_sum, map_smul]
      rw [hmap, hs]
      simp only [Finset.sum_apply, hc, X, c]
      change L (X ω) = ∑ i : I, L (Pi.single i 1) * X ω i
      refine (L.toLinearMap.pi_apply_eq_sum_univ (X ω)).trans ?_
      apply Finset.sum_congr rfl
      intro i _
      simp only [smul_eq_mul]
      have hb : (fun j : I => if i = j then (1 : ℝ) else 0) = Pi.single i 1 := by
        ext j
        by_cases hij : i = j
        · subst j; simp
        · simp [hij, Ne.symm hij]
      rw [hb]
      exact mul_comm _ _
    have hg := (hasGaussianLaw_wienerIntegral hB k).congr he.symm
    change IsGaussian ((P.map X).map L)
    rw [AEMeasurable.map_map_of_aemeasurable L.measurable.aemeasurable hX]
    exact hg.isGaussian_map

/-- Wiener covariance equals deterministic kernel inner product. -/
theorem covariance_wienerIntegral (hB : IsPreBrownianReal B P)
    (f g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    cov[wienerIntegral hB f, wienerIntegral hB g; P] = ⟪f, g⟫_ℝ := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [covariance_eq_sub (Lp.memLp (wienerIntegral hB f))
    (Lp.memLp (wienerIntegral hB g)), integral_wienerIntegral, integral_wienerIntegral,
    mul_zero, sub_zero, ← inner_wienerIntegral hB f g, L2.inner_def]
  congr 1
  ext ω
  simp only [Pi.mul_apply, RCLike.inner_apply, conj_trivial, mul_comm]

/-- A family of Wiener kernels with Gram matrix `min(s,t)` is pre-Brownian. -/
theorem isPreBrownianReal_wienerIntegral (hB : IsPreBrownianReal B P)
    (f : ℝ≥0 → Lp ℝ 2 nonnegativeLebesgueMeasure)
    (hGram : ∀ s t, ⟪f s, f t⟫_ℝ = (min s t : ℝ)) :
    IsPreBrownianReal (fun t ω => wienerIntegral hB (f t) ω) P := by
  apply (isGaussianProcess_wienerIntegral hB f).isPreBrownianReal_of_covariance
  · intro t
    exact integral_wienerIntegral hB (f t)
  · intro s t hst
    rw [covariance_wienerIntegral, hGram]
    exact min_eq_left (NNReal.coe_le_coe.mpr hst)

/-- The continuous modification supplied by Kolmogorov--Chentsov. Subtracting
its value at zero gives a driver which starts at zero on every sample path. -/
def wienerBrownianDriver (hB : IsPreBrownianReal B P)
    (f : ℝ≥0 → Lp ℝ 2 nonnegativeLebesgueMeasure)
    (hGram : ∀ s t, ⟪f s, f t⟫_ℝ = (min s t : ℝ))
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  let h := isPreBrownianReal_wienerIntegral hB f hGram
  h.mk (fun u ω => wienerIntegral hB (f u) ω) t ω -
    h.mk (fun u ω => wienerIntegral hB (f u) ω) 0 ω

theorem wienerBrownianDriver_zero (hB : IsPreBrownianReal B P)
    (f : ℝ≥0 → Lp ℝ 2 nonnegativeLebesgueMeasure)
    (hGram : ∀ s t, ⟪f s, f t⟫_ℝ = (min s t : ℝ)) (ω : Ω) :
    wienerBrownianDriver hB f hGram 0 ω = 0 := sub_self _

theorem measurable_wienerBrownianDriver (hB : IsPreBrownianReal B P)
    (f : ℝ≥0 → Lp ℝ 2 nonnegativeLebesgueMeasure)
    (hGram : ∀ s t, ⟪f s, f t⟫_ℝ = (min s t : ℝ)) (t : ℝ≥0) :
    Measurable (wienerBrownianDriver hB f hGram t) :=
  (isPreBrownianReal_wienerIntegral hB f hGram).measurable_mk t |>.sub
    ((isPreBrownianReal_wienerIntegral hB f hGram).measurable_mk 0)

theorem continuous_wienerBrownianDriver (hB : IsPreBrownianReal B P)
    (f : ℝ≥0 → Lp ℝ 2 nonnegativeLebesgueMeasure)
    (hGram : ∀ s t, ⟪f s, f t⟫_ℝ = (min s t : ℝ)) (ω : Ω) :
    Continuous (fun t => wienerBrownianDriver hB f hGram t ω) :=
  (isPreBrownianReal_wienerIntegral hB f hGram).continuous_mk ω |>.sub continuous_const

theorem wienerBrownianDriver_ae_eq (hB : IsPreBrownianReal B P)
    (f : ℝ≥0 → Lp ℝ 2 nonnegativeLebesgueMeasure)
    (hGram : ∀ s t, ⟪f s, f t⟫_ℝ = (min s t : ℝ)) (t : ℝ≥0) :
    wienerBrownianDriver hB f hGram t =ᵐ[P] wienerIntegral hB (f t) := by
  let h := isPreBrownianReal_wienerIntegral hB f hGram
  have hz := h.isBrownianReal_mk.toIsPreBrownianReal.eval_zero_ae_eq_zero
  filter_upwards [h.mk_ae_eq t, hz] with ω ht h0
  change h.mk _ t ω - h.mk _ 0 ω = _
  rw [h0, sub_zero, ht]

theorem isBrownianReal_wienerBrownianDriver (hB : IsPreBrownianReal B P)
    (f : ℝ≥0 → Lp ℝ 2 nonnegativeLebesgueMeasure)
    (hGram : ∀ s t, ⟪f s, f t⟫_ℝ = (min s t : ℝ)) :
    IsBrownianReal (wienerBrownianDriver hB f hGram) P :=
  ⟨(isPreBrownianReal_wienerIntegral hB f hGram).congr
      (fun t => (wienerBrownianDriver_ae_eq hB f hGram t).symm),
    Filter.Eventually.of_forall (continuous_wienerBrownianDriver hB f hGram)⟩

end FourPapersCommon
