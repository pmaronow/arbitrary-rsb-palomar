module

public import FRSB.FixedStateMoments
public import FRSB.GammaPrime

@[expose] public section


/-! Genuine bounded measurable curvature evolution sources on the fixed
actual optimal state, and their uniform convergence under weak jet measures. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper
open scoped Topology
namespace FRSB
set_option maxHeartbeats 1000000

 def curvatureEvolutionSource (β : ℝ) (hβ : β≠0) (μ ν : ParisiMeasure) (t : ℝ) : ℝ :=
  β^2*(fixedStateJetPower β hβ μ ν 2 2 t-
    2*parisiCDF μ t*fixedStateJetPower β hβ μ ν 1 3 t)

 theorem measurable_curvatureEvolutionSource (β : ℝ) (hβ : β≠0) (μ ν : ParisiMeasure) :
    Measurable (curvatureEvolutionSource β hβ μ ν) :=
  measurable_const.mul ((continuous_fixedStateJetPower β hβ μ ν 2 2).measurable.sub
    ((measurable_const.mul (parisiCDF_measurable μ)).mul
      (continuous_fixedStateJetPower β hβ μ ν 1 3).measurable))

 theorem norm_curvatureEvolutionSource_le (β : ℝ) (hβ : β≠0) (μ ν : ParisiMeasure) (t : ℝ) :
    ‖curvatureEvolutionSource β hβ μ ν t‖ ≤
      β^2*(uniformSpatialConstant β 2^2+2*uniformSpatialConstant β 1^3) := by
  unfold curvatureEvolutionSource
  rw [norm_mul,Real.norm_of_nonneg (sq_nonneg β)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg β)
  apply (norm_sub_le _ _).trans
  apply add_le_add (norm_fixedStateJetPower_le β hβ μ ν 2 2 t)
  rw [norm_mul,norm_mul,show ‖(2:ℝ)‖=2 by norm_num,
    Real.norm_of_nonneg (parisiCDF_nonneg μ t)]
  exact (mul_le_mul (mul_le_mul_of_nonneg_left (parisiCDF_le_one μ t) (by norm_num : (0:ℝ)≤2))
    (norm_fixedStateJetPower_le β hβ μ ν 1 3 t) (norm_nonneg _)
    (by norm_num : (0:ℝ)≤2*1)).trans_eq (by ring)

 theorem curvatureEvolutionSource_intervalIntegrable (β : ℝ) (hβ : β≠0)
    (μ ν : ParisiMeasure) (a b : ℝ) :
    IntervalIntegrable (curvatureEvolutionSource β hβ μ ν) volume a b := by
  apply (intervalIntegrable_const (c:=β^2*(uniformSpatialConstant β 2^2+
    2*uniformSpatialConstant β 1^3))).mono_fun'
      (measurable_curvatureEvolutionSource β hβ μ ν).aestronglyMeasurable
  exact .of_forall fun t=>norm_curvatureEvolutionSource_le β hβ μ ν t

 theorem curvatureEvolutionSource_eq_integral (β : ℝ) (hβ : β≠0)
    (μ ν : ParisiMeasure) (t : ℝ) :
    curvatureEvolutionSource β hβ μ ν t =
      ∫ω,β^2*(parisiSpatialJet β ν 3 t (selectedParisiItoState β 0 hβ μ t.toNNReal ω)^2-
        2*parisiCDF μ t*parisiSpatialJet β ν 2 t (selectedParisiItoState β 0 hβ μ t.toNNReal ω)^3)
        ∂canonicalBrownianMeasure := by
  unfold curvatureEvolutionSource fixedStateJetPower
  rw [integral_const_mul,integral_sub (integrable_fixedStateJetPower β hβ μ ν 2 2 t)
    ((integrable_fixedStateJetPower β hβ μ ν 1 3 t).const_mul (2*parisiCDF μ t)),
    integral_const_mul]

 theorem curvatureEvolutionSource_sub_norm_le (β : ℝ) (hβ : β≠0)
    (μ ν ρ : ParisiMeasure) (t : ℝ) :
    ‖curvatureEvolutionSource β hβ μ ν t-curvatureEvolutionSource β hβ μ ρ t‖ ≤
      β^2*(‖bcfSpatialDerivative (parisiGradientBCF β ν) 2-
          bcfSpatialDerivative (parisiGradientBCF β ρ) 2‖*2*uniformSpatialConstant β 2+
        6*‖bcfSpatialDerivative (parisiGradientBCF β ν) 1-
          bcfSpatialDerivative (parisiGradientBCF β ρ) 1‖*uniformSpatialConstant β 1^2) := by
  have h2:=fixedStateJetPower_sub_norm_le β hβ μ ν ρ 2 2 t
  have h3:=fixedStateJetPower_sub_norm_le β hβ μ ν ρ 1 3 t
  unfold curvatureEvolutionSource
  rw [← mul_sub,show (fixedStateJetPower β hβ μ ν 2 2 t-
      2*parisiCDF μ t*fixedStateJetPower β hβ μ ν 1 3 t)-
      (fixedStateJetPower β hβ μ ρ 2 2 t-2*parisiCDF μ t*fixedStateJetPower β hβ μ ρ 1 3 t)=
      (fixedStateJetPower β hβ μ ν 2 2 t-fixedStateJetPower β hβ μ ρ 2 2 t)-
        2*parisiCDF μ t*(fixedStateJetPower β hβ μ ν 1 3 t-fixedStateJetPower β hβ μ ρ 1 3 t) by ring,
    norm_mul,Real.norm_of_nonneg (sq_nonneg β)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg β)
  apply (norm_sub_le _ _).trans
  apply add_le_add (by simpa using h2)
  rw [norm_mul,Real.norm_of_nonneg (mul_nonneg (by norm_num) (parisiCDF_nonneg μ t))]
  exact (mul_le_mul (mul_le_mul_of_nonneg_left (parisiCDF_le_one μ t) (by norm_num))
    h3 (norm_nonneg _) (by norm_num)).trans_eq (by norm_num;ring)

 theorem tendsto_curvatureEvolutionSource_integral_of_weak {ι : Type*} {L : Filter ι}
    (β : ℝ) (hβ : β≠0) (μ ρ : ParisiMeasure) (ν : ι→ParisiMeasure)
    (hν:Tendsto ν L (nhds ρ)) (a b : ℝ) :
    Tendsto (fun i=>∫t in a..b,curvatureEvolutionSource β hβ μ (ν i) t) L
      (nhds (∫t in a..b,curvatureEvolutionSource β hβ μ ρ t)) := by
  let E:ι→ℝ:=fun i=>β^2*(‖bcfSpatialDerivative (parisiGradientBCF β (ν i)) 2-
      bcfSpatialDerivative (parisiGradientBCF β ρ) 2‖*2*uniformSpatialConstant β 2+
    6*‖bcfSpatialDerivative (parisiGradientBCF β (ν i)) 1-
      bcfSpatialDerivative (parisiGradientBCF β ρ) 1‖*uniformSpatialConstant β 1^2)
  have hE:Tendsto E L (nhds 0) := by
    have h2:=(tendsto_spatialDerivativeBCF_of_weak β 2 ρ ν hν).sub_const
      (bcfSpatialDerivative (parisiGradientBCF β ρ) 2) |>.norm
    have h1:=(tendsto_spatialDerivativeBCF_of_weak β 1 ρ ν hν).sub_const
      (bcfSpatialDerivative (parisiGradientBCF β ρ) 1) |>.norm
    simpa only [E,sub_self,norm_zero,zero_mul,mul_zero,zero_add] using
      (((h2.mul_const 2).mul_const (uniformSpatialConstant β 2)).add
        ((h1.const_mul 6).mul_const (uniformSpatialConstant β 1^2))).const_mul (β^2)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (g:=fun i=>E i*|b-a|) (fun i=>norm_nonneg _)
  · intro i
    rw [← intervalIntegral.integral_sub (curvatureEvolutionSource_intervalIntegrable β hβ μ (ν i) a b)
      (curvatureEvolutionSource_intervalIntegrable β hβ μ ρ a b)]
    exact intervalIntegral.norm_integral_le_of_norm_le_const
      (fun t _=>curvatureEvolutionSource_sub_norm_le β hβ μ (ν i) ρ t)
  · simpa only [zero_mul] using hE.mul_const |b-a|

end FRSB
