module

public import StochasticCalculus.WienerIntegral

@[expose] public section

/-! Multiplication by a measurable coefficient bounded by one preserves
the deterministic Wiener integral's L² error bound. Independence is not
required for this estimate. -/

noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus
open scoped NNReal ENNReal
namespace FourPapersCommon

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

theorem memLp_boundedWienerMultiplier
    (hB : IsPreBrownianReal B P) (H : Ω → ℝ) (hH : AEStronglyMeasurable H P)
    (hBound : ∀ ω, ‖H ω‖ ≤ 1) (e : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    MemLp (fun ω => H ω * wienerIntegral hB e ω) 2 P :=
  (Lp.memLp (wienerIntegral hB e)).of_le
    (hH.mul (Lp.aestronglyMeasurable (wienerIntegral hB e)))
    (Filter.Eventually.of_forall fun ω => by
      rw [norm_mul]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (hBound ω) (norm_nonneg (wienerIntegral hB e ω)))

/-- The genuine L² random variable given by multiplying an actual Wiener
integral by the supplied bounded measurable coefficient. -/
def boundedWienerMultiplier
    (hB : IsPreBrownianReal B P) (H : Ω → ℝ) (hH : AEStronglyMeasurable H P)
    (hBound : ∀ ω, ‖H ω‖ ≤ 1) (e : Lp ℝ 2 nonnegativeLebesgueMeasure) : Lp ℝ 2 P :=
  (memLp_boundedWienerMultiplier hB H hH hBound e).toLp
    (fun ω => H ω * wienerIntegral hB e ω)

theorem boundedWienerMultiplier_coe_ae
    (hB : IsPreBrownianReal B P) (H : Ω → ℝ) (hH : AEStronglyMeasurable H P)
    (hBound : ∀ ω, ‖H ω‖ ≤ 1) (e : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    (boundedWienerMultiplier hB H hH hBound e : Ω → ℝ) =ᵐ[P]
      fun ω => H ω * wienerIntegral hB e ω := MemLp.coeFn_toLp _

theorem boundedWienerMultiplier_norm_le
    (hB : IsPreBrownianReal B P) (H : Ω → ℝ) (hH : AEStronglyMeasurable H P)
    (hBound : ∀ ω, ‖H ω‖ ≤ 1) (e : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    ‖boundedWienerMultiplier hB H hH hBound e‖ ≤ ‖e‖ := by
  rw [← norm_wienerIntegral hB e]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [boundedWienerMultiplier_coe_ae hB H hH hBound e] with ω hω
  rw [hω, norm_mul]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (hBound ω) (norm_nonneg (wienerIntegral hB e ω))

end FourPapersCommon
