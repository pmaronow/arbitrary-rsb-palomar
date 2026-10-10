module

public import GeneralDepthPaper.QuadraticFirstVariation
public import FourPapersCommon.MixedSharpGradient

@[expose] public section


/-! The exact JT gradient estimate quoted in the manuscript at lines 537--539.
The uniform norm is that of the actual spatial derivative of the difference
of the two constructed Parisi potentials. All probability profiles are allowed. -/
noncomputable section
open Set
open scoped Topology BoundedContinuousFunction
namespace GeneralDepthPaper
open FourPapersCommon

theorem gradient_sharp_d1_bound (Ξ : AdmissibleCovariance)
    (μ ν : ParisiMeasure) (q : ℝ) (hq : q ∈ Icc (0:ℝ) 1) (x : ℝ) :
    ‖gradient Ξ ν q x - gradient Ξ μ q x‖ ≤
      Real.exp (Ξ.first 1) * Ξ.second 1 * parisiMeasureD1 μ ν := by
  simpa only [gradient, AdmissibleCovariance.toEvenMixture_first,
    AdmissibleCovariance.toEvenMixture_second, parisiMeasureD1_eq_cdfDistance] using
    mixedGradient_sharp_CDF_L1_bound Ξ.toEvenMixture μ ν q hq x

theorem hasDerivAt_potential_difference (Ξ : AdmissibleCovariance)
    (μ ν : ParisiMeasure) (q : ℝ) (hq : q ∈ Icc (0:ℝ) 1) (x : ℝ) :
    HasDerivAt (fun y => potential Ξ ν q y - potential Ξ μ q y)
      (gradient Ξ ν q x - gradient Ξ μ q x) x :=
  (hasDerivAt_mixedPotential_spatial Ξ.toEvenMixture ν q x hq).sub
    (hasDerivAt_mixedPotential_spatial Ξ.toEvenMixture μ q x hq)

/-- The actual spatial derivative difference as a bounded continuous function
on the full physical time strip and the entire real field line. -/
def gradientDifferenceBCF (Ξ : AdmissibleCovariance) (μ ν : ParisiMeasure) :
    (Overlap × ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => gradient Ξ ν p.1 p.2 - gradient Ξ μ p.1 p.2)
    (by
      have hc (ρ : ParisiMeasure) : Continuous (fun p : Overlap × ℝ => gradient Ξ ρ p.1 p.2) := by
        unfold gradient mixedGradient
        simp only [AdmissibleCovariance.toEvenMixture_clock]
        exact (Paper.continuous_parisiGradient _ _).comp
          (((Ξ.continuous_clock.comp (continuous_subtype_val.comp continuous_fst))).prodMk continuous_snd)
      exact (hc ν).sub (hc μ)) 2
    (fun p => (norm_sub_le _ _).trans (by
      have hν := norm_mixedGradient_le_one Ξ.toEvenMixture ν ((p.1:ℝ),p.2)
      have hμ := norm_mixedGradient_le_one Ξ.toEvenMixture μ ((p.1:ℝ),p.2)
      change ‖gradient Ξ ν p.1 p.2‖ ≤ 1 at hν
      change ‖gradient Ξ μ p.1 p.2‖ ≤ 1 at hμ
      linarith))

/-- Exactly `‖w_x‖∞ ≤ exp(Ξ'(1)) Ξ''(1) d₁(μ,ν)`, with no cited estimate
or profile-response identity among the hypotheses. -/
theorem norm_gradientDifferenceBCF_le (Ξ : AdmissibleCovariance)
    (μ ν : ParisiMeasure) :
    ‖gradientDifferenceBCF Ξ μ ν‖ ≤
      Real.exp (Ξ.first 1) * Ξ.second 1 * parisiMeasureD1 μ ν := by
  have hC : 0 ≤ Real.exp (Ξ.first 1) * Ξ.second 1 * parisiMeasureD1 μ ν :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (Ξ.second_nonneg (q := 1) zero_le_one))
      (by rw [parisiMeasureD1_eq_cdfDistance]; exact parisiCDFDistance_nonneg μ ν)
  apply (BoundedContinuousFunction.norm_le hC).mpr
  intro p
  exact gradient_sharp_d1_bound Ξ μ ν p.1 p.1.property p.2

end GeneralDepthPaper
