module

public import DepthPaper.TruncatedState

@[expose] public section


/-! Actual overlap and squared-curvature expectations are continuous. Their
continuity follows from continuous state paths and bounded genuine jets; it is
not a premise in the truncated Parisi datum. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal BoundedContinuousFunction
namespace DepthPaper
open FourPapersCommon Paper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem measurable_bcf_clock_observable {Ω : Type*} [MeasurableSpace Ω]
    (G : (ℝ×ℝ) →ᵇ ℝ) (X : ℝ≥0 → Ω → ℝ) (hX : Measurable (Function.uncurry X)) :
    Measurable (fun p : ℝ×Ω => G (p.1,X p.1.toNNReal p.2)) := by
  have ht : Measurable (fun p : ℝ×Ω => (p.1.toNNReal,p.2)) :=
    (measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd
  have hx : Measurable (fun p : ℝ×Ω => X p.1.toNNReal p.2) := hX.comp ht
  exact G.continuous.measurable.comp (measurable_fst.prodMk hx)

namespace TruncatedParisiData

theorem measurable_spatial_observable {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc)
    (j : Fin 3) : Measurable (fun p : ℝ×BrownianSample => d.spatialField j (p.1,d.state p.1.toNNReal p.2)) :=
  measurable_bcf_clock_observable (Ω := BrownianSample) (d.spatialField j) d.state d.measurable_state

theorem integrable_spatial_observable_square {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc)
    (j : Fin 3) (t : ℝ) :
    Integrable (fun ω => (d.spatialField j (t,d.state t.toNNReal ω))^2) canonicalBrownianMeasure := by
  apply (integrable_const (‖d.spatialField j‖^2)).mono'
    (((d.measurable_spatial_observable j).comp
      (measurable_const.prodMk measurable_id)).pow_const 2).aestronglyMeasurable
  exact .of_forall fun ω => by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) ((d.spatialField j).norm_coe_le_norm _) 2

theorem continuous_spatial_observable_moment {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc)
    (j : Fin 3) :
    Continuous (fun t => ∫ω,(d.spatialField j (t,d.state t.toNNReal ω))^2 ∂canonicalBrownianMeasure) := by
  apply continuous_of_dominated (bound := fun _ => ‖d.spatialField j‖^2)
  · intro t
    exact (((d.measurable_spatial_observable j).comp
      (measurable_const.prodMk measurable_id)).pow_const 2).aestronglyMeasurable
  · intro t
    exact .of_forall fun ω => by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) ((d.spatialField j).norm_coe_le_norm _) 2
  · exact integrable_const _
  · exact .of_forall fun ω => ((d.spatialField j).continuous.comp
      (continuous_id.prodMk ((d.continuous_state ω).comp continuous_real_toNNReal))).pow 2

@[fun_prop] theorem continuous_Gamma {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) :
    Continuous d.Gamma := d.continuous_spatial_observable_moment 0

@[fun_prop] theorem continuous_Gamma2 {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) :
    Continuous d.Gamma2 := d.continuous_spatial_observable_moment 1

theorem Gamma_mem_Icc {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) (t : ℝ) :
    d.Gamma t ∈ Icc (0:ℝ) 1 := by
  refine ⟨integral_nonneg fun _ => sq_nonneg _,?_⟩
  calc
    d.Gamma t ≤ ∫ω,(1:ℝ) ∂canonicalBrownianMeasure :=
      integral_mono (d.integrable_spatial_observable_square 0 t) (integrable_const 1) (fun ω => by
        have hb := ((d.spatialField 0).norm_coe_le_norm (t,d.state t.toNNReal ω)).trans
          d.spatialField_zero_bound
        simpa only [Real.norm_eq_abs,sq_abs,one_pow] using
          (pow_le_pow_left₀ (abs_nonneg _) hb 2))
    _ = 1 := by simp

theorem Gamma2_nonneg {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) (t : ℝ) :
    0 ≤ d.Gamma2 t := integral_nonneg fun _ => sq_nonneg _

theorem hasDerivAt_firstVariation {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) (q : ℝ) :
    HasDerivAt d.firstVariation ((1/2:ℝ)*d.covarianceField 2 q*(d.Gamma q-q)) q := by
  have hc : Continuous (fun t => d.covarianceField 2 t*(d.Gamma t-t)) :=
    (d.continuous_covarianceField 2).mul (d.continuous_Gamma.sub continuous_id)
  have h := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 q)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  exact (h.const_mul (1/2:ℝ)).congr_deriv (by ring)

end TruncatedParisiData
end DepthPaper
