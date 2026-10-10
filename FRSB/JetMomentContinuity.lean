module

public import FRSB.OptimalDiffusion

@[expose] public section


/-! Integrability and physical-time continuity of all positive-jet powers,
for the actual canonical optimal state. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace FRSB
open Paper

theorem measurable_jetProcess_succ (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (j : ℕ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    Measurable (jetProcess β μ (j+1) s) := by
  have hm : Measurable (fun ω => optimalStateReal β μ ω s) := by
    rw [optimalStateReal_eq_selected β hβ μ]
    exact measurable_selectedParisiStateReal β 0 hβ μ s hs
  exact (continuous_parisiSpatialJet_succ β μ j).measurable.comp
    (f := fun ω : BrownianSample => (s, optimalStateReal β μ ω s))
    (measurable_const.prodMk hm)

theorem norm_jetProcess_pow_le (β : ℝ) (μ : ParisiMeasure) (j n : ℕ)
    (s : ℝ) (ω : BrownianSample) :
    ‖jetProcess β μ (j+1) s ω ^ n‖ ≤
      ‖bcfSpatialDerivative (parisiGradientBCF β μ) j‖ ^ n := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (norm_parisiSpatialJet_succ_le β μ j s _) n

theorem integrable_jetProcess_pow (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (j n : ℕ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    Integrable (fun ω => jetProcess β μ (j+1) s ω ^ n) canonicalBrownianMeasure :=
  (integrable_const (‖bcfSpatialDerivative (parisiGradientBCF β μ) j‖ ^ n)).mono'
    ((measurable_jetProcess_succ β hβ μ j hs).pow_const n).aestronglyMeasurable
    (.of_forall (norm_jetProcess_pow_le β μ j n s))

theorem continuousOn_integral_jetProcess_pow (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (j n : ℕ) :
    ContinuousOn (fun s => ∫ ω, jetProcess β μ (j+1) s ω ^ n
      ∂canonicalBrownianMeasure) (Icc (0 : ℝ) 1) := by
  apply continuousOn_of_dominated (μ := canonicalBrownianMeasure)
    (F := fun (s : ℝ) ω => jetProcess β μ (j+1) s ω ^ n)
    (bound := fun _ => ‖bcfSpatialDerivative (parisiGradientBCF β μ) j‖ ^ n)
  · intro s hs
    exact ((measurable_jetProcess_succ β hβ μ j hs).pow_const n).aestronglyMeasurable
  · intro s _
    exact .of_forall (norm_jetProcess_pow_le β μ j n s)
  · exact integrable_const _
  · exact .of_forall fun ω => (((continuous_parisiSpatialJet_succ β μ j).comp
      (continuous_id.prodMk (continuous_optimalStateReal β μ ω))).pow n).continuousOn

end FRSB
