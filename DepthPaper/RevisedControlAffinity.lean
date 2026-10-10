module

public import DepthPaper.RevisedAtomicMassLine
public import Paper.ParisiControlDerivative
public import FourPapersCommon.WeightedCDF

@[expose] public section

/-! Exact affinity of fixed-control drifts, costs and covariance corrections
from an affine cumulative distribution. The scalar parameter is unrestricted,
so these formulas apply to both sides of a valid mass-coordinate line. -/

noncomputable section
open Set MeasureTheory
open scoped Topology
namespace DepthPaper

theorem parisiControlDrift_affine_of_cdf {Ω : Type*} (β : ℝ)
    (μ ν ρ : Paper.ParisiMeasure) (a : ℝ)
    (hcdf : ∀ s ∈ Icc (0 : ℝ) 1, Paper.parisiCDF ρ s =
      Paper.parisiCDF μ s + a * (Paper.parisiCDF ν s - Paper.parisiCDF μ s))
    (A : ℝ → Ω → ℝ) (hA : ∀ ω, Measurable (fun s => A s ω))
    (hb : ∀ s ω, ‖A s ω‖ ≤ 1) (ω : Ω) :
    Paper.parisiControlDrift β ρ A ω = Paper.parisiControlDrift β μ A ω +
      a * (Paper.parisiControlDrift β ν A ω - Paper.parisiControlDrift β μ A ω) := by
  have hi := (Paper.parisiControl_intervalIntegrable μ A hA hb ω).1
  have hj := (Paper.parisiControl_intervalIntegrable ν A hA hb ω).1
  unfold Paper.parisiControlDrift
  have he : (∫ s in (0 : ℝ)..1, Paper.parisiCDF ρ s * A s ω) =
      (∫ s in (0 : ℝ)..1, Paper.parisiCDF μ s * A s ω) +
        a * ((∫ s in (0 : ℝ)..1, Paper.parisiCDF ν s * A s ω) -
          ∫ s in (0 : ℝ)..1, Paper.parisiCDF μ s * A s ω) := by
    calc
      _ = ∫ s in (0 : ℝ)..1, Paper.parisiCDF μ s * A s ω +
          a * (Paper.parisiCDF ν s * A s ω - Paper.parisiCDF μ s * A s ω) := by
        apply intervalIntegral.integral_congr
        intro s hs
        dsimp only
        rw [uIcc_of_le zero_le_one] at hs
        rw [hcdf s hs]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add hi ((hj.sub hi).const_mul a),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hj hi]
  rw [he]
  ring

theorem parisiControlCost_affine_of_cdf {Ω : Type*} (β : ℝ)
    (μ ν ρ : Paper.ParisiMeasure) (a : ℝ)
    (hcdf : ∀ s ∈ Icc (0 : ℝ) 1, Paper.parisiCDF ρ s =
      Paper.parisiCDF μ s + a * (Paper.parisiCDF ν s - Paper.parisiCDF μ s))
    (A : ℝ → Ω → ℝ) (hA : ∀ ω, Measurable (fun s => A s ω))
    (hb : ∀ s ω, ‖A s ω‖ ≤ 1) (ω : Ω) :
    Paper.parisiControlCost β ρ A ω = Paper.parisiControlCost β μ A ω +
      a * (Paper.parisiControlCost β ν A ω - Paper.parisiControlCost β μ A ω) := by
  have hi := (Paper.parisiControl_intervalIntegrable μ A hA hb ω).2
  have hj := (Paper.parisiControl_intervalIntegrable ν A hA hb ω).2
  unfold Paper.parisiControlCost
  have he : (∫ s in (0 : ℝ)..1, Paper.parisiCDF ρ s * A s ω ^ 2) =
      (∫ s in (0 : ℝ)..1, Paper.parisiCDF μ s * A s ω ^ 2) +
        a * ((∫ s in (0 : ℝ)..1, Paper.parisiCDF ν s * A s ω ^ 2) -
          ∫ s in (0 : ℝ)..1, Paper.parisiCDF μ s * A s ω ^ 2) := by
    calc
      _ = ∫ s in (0 : ℝ)..1, Paper.parisiCDF μ s * A s ω ^ 2 +
          a * (Paper.parisiCDF ν s * A s ω ^ 2 - Paper.parisiCDF μ s * A s ω ^ 2) := by
        apply intervalIntegral.integral_congr
        intro s hs
        dsimp only
        rw [uIcc_of_le zero_le_one] at hs
        rw [hcdf s hs]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add hi ((hj.sub hi).const_mul a),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hj hi]
  rw [he]
  ring

theorem parisiControlPayoff_affine_of_cdf {Ω : Type*} (β h : ℝ) (B : Ω → ℝ)
    (μ ν ρ : Paper.ParisiMeasure) (a : ℝ)
    (hcdf : ∀ s ∈ Icc (0 : ℝ) 1, Paper.parisiCDF ρ s =
      Paper.parisiCDF μ s + a * (Paper.parisiCDF ν s - Paper.parisiCDF μ s))
    (A : ℝ → Ω → ℝ) (hA : ∀ ω, Measurable (fun s => A s ω))
    (hb : ∀ s ω, ‖A s ω‖ ≤ 1) (ω : Ω) :
    Paper.parisiControlPayoff β h B A ρ ω =
      Paper.parisiAffineControlPayoff β h B A μ ν a ω := by
  unfold Paper.parisiControlPayoff Paper.parisiAffineControlPayoff
  rw [parisiControlDrift_affine_of_cdf β μ ν ρ a hcdf A hA hb ω,
    parisiControlCost_affine_of_cdf β μ ν ρ a hcdf A hA hb ω]
  congr 3 <;> ring

theorem weightedCDFIntegral_affine_of_cdf (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc (0 : ℝ) 1)) (μ ν ρ : Paper.ParisiMeasure) (a : ℝ)
    (hcdf : ∀ s ∈ Icc (0 : ℝ) 1, Paper.parisiCDF ρ s =
      Paper.parisiCDF μ s + a * (Paper.parisiCDF ν s - Paper.parisiCDF μ s)) :
    FourPapersCommon.weightedCDFIntegral g ρ = FourPapersCommon.weightedCDFIntegral g μ +
      a * (FourPapersCommon.weightedCDFIntegral g ν -
        FourPapersCommon.weightedCDFIntegral g μ) := by
  have hi (σ : Paper.ParisiMeasure) :
      IntervalIntegrable (fun s => g s * Paper.parisiCDF σ s) volume (0 : ℝ) 1 := by
    have hc : IntervalIntegrable (Paper.parisiCDF σ) volume (0 : ℝ) 1 :=
      (Paper.parisiCDF_monotone σ).intervalIntegrable
    simpa only [mul_comm] using hc.mul_continuousOn
      (show ContinuousOn g (uIcc (0 : ℝ) 1) by simpa only [uIcc_of_le zero_le_one] using hg)
  unfold FourPapersCommon.weightedCDFIntegral
  calc
    _ = ∫ s in (0 : ℝ)..1, g s * Paper.parisiCDF μ s +
        a * (g s * Paper.parisiCDF ν s - g s * Paper.parisiCDF μ s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      dsimp only
      rw [uIcc_of_le zero_le_one] at hs
      rw [hcdf s hs]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (hi μ) (((hi ν).sub (hi μ)).const_mul a),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (hi ν) (hi μ)]

end DepthPaper
