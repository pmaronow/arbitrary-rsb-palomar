module

public import FRSB.GammaIdentity

@[expose] public section


/-! Bounded positive-order jet moments on the fixed actual optimal state,
with genuine uniform convergence under weak changes of the jet measure. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper
open scoped Topology
namespace FRSB
set_option maxHeartbeats 1000000

 def fixedStateJetPower (β : ℝ) (hβ : β≠0) (μ ν : ParisiMeasure)
    (j p : ℕ) (t : ℝ) : ℝ :=
  ∫ω,parisiSpatialJet β ν (j+1) t (selectedParisiItoState β 0 hβ μ t.toNNReal ω)^p
    ∂canonicalBrownianMeasure

 theorem fixedStateJetPower_measurable_integrand (β : ℝ) (hβ : β≠0)
    (μ ν : ParisiMeasure) (j p : ℕ) (t : ℝ) : Measurable
      (fun ω=>parisiSpatialJet β ν (j+1) t (selectedParisiItoState β 0 hβ μ t.toNNReal ω)^p) := by
  have hm:Measurable (selectedParisiItoState β 0 hβ μ t.toNNReal) :=
    (boundedDriftItoCharacteristics_selectedParisiState β 0 hβ μ).adapted_state t.toNNReal
      |>.measurable |>.mono (canonicalBrownianFiltration.le t.toNNReal) le_rfl
  exact ((continuous_parisiSpatialJet_succ β ν j).measurable.comp
    (measurable_const.prodMk hm)).pow_const p

 theorem integrable_fixedStateJetPower (β : ℝ) (hβ : β≠0)
    (μ ν : ParisiMeasure) (j p : ℕ) (t : ℝ) : Integrable
      (fun ω=>parisiSpatialJet β ν (j+1) t (selectedParisiItoState β 0 hβ μ t.toNNReal ω)^p)
      canonicalBrownianMeasure := by
  apply (integrable_const (uniformSpatialConstant β j^p)).mono'
    (fixedStateJetPower_measurable_integrand β hβ μ ν j p t).aestronglyMeasurable
  exact .of_forall fun ω=>by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _)
      ((norm_parisiSpatialJet_succ_le β ν j t _).trans
        (norm_spatialDerivativeBCF_le_uniform β ν j)) p

 theorem continuous_fixedStateJetPower (β : ℝ) (hβ : β≠0)
    (μ ν : ParisiMeasure) (j p : ℕ) : Continuous (fixedStateJetPower β hβ μ ν j p) := by
  unfold fixedStateJetPower
  apply continuous_of_dominated (μ:=canonicalBrownianMeasure)
    (bound:=fun _=>uniformSpatialConstant β j^p)
  · intro t
    exact (fixedStateJetPower_measurable_integrand β hβ μ ν j p t).aestronglyMeasurable
  · intro t
    exact .of_forall fun ω=>by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _)
        ((norm_parisiSpatialJet_succ_le β ν j t _).trans
          (norm_spatialDerivativeBCF_le_uniform β ν j)) p
  · exact integrable_const _
  · exact .of_forall fun ω=>((continuous_parisiSpatialJet_succ β ν j).comp
      (continuous_id.prodMk (((boundedDriftItoCharacteristics_selectedParisiState β 0 hβ μ).continuous_state ω).comp
        continuous_real_toNNReal))).pow p

 theorem norm_fixedStateJetPower_le (β : ℝ) (hβ : β≠0)
    (μ ν : ParisiMeasure) (j p : ℕ) (t : ℝ) :
    ‖fixedStateJetPower β hβ μ ν j p t‖≤uniformSpatialConstant β j^p := by
  simpa [fixedStateJetPower] using norm_integral_le_of_norm_le_const
    (μ:=canonicalBrownianMeasure) (C:=uniformSpatialConstant β j^p)
    (f:=fun ω=>parisiSpatialJet β ν (j+1) t (selectedParisiItoState β 0 hβ μ t.toNNReal ω)^p)
    (.of_forall fun ω=>by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _)
        ((norm_parisiSpatialJet_succ_le β ν j t _).trans
          (norm_spatialDerivativeBCF_le_uniform β ν j)) p)

 theorem fixedStateJetPower_sub_norm_le (β : ℝ) (hβ : β≠0)
    (μ ν ρ : ParisiMeasure) (j p : ℕ) (t : ℝ) :
    ‖fixedStateJetPower β hβ μ ν j p t-fixedStateJetPower β hβ μ ρ j p t‖ ≤
      ‖bcfSpatialDerivative (parisiGradientBCF β ν) j-
          bcfSpatialDerivative (parisiGradientBCF β ρ) j‖ *
        (p:ℝ)*uniformSpatialConstant β j^(p-1) := by
  unfold fixedStateJetPower
  rw [← integral_sub (integrable_fixedStateJetPower β hβ μ ν j p t)
    (integrable_fixedStateJetPower β hβ μ ρ j p t)]
  have hb : ∀ ω : BrownianSample, ‖parisiSpatialJet β ν (j+1) t
      (selectedParisiItoState β 0 hβ μ t.toNNReal ω)^p-parisiSpatialJet β ρ (j+1) t
        (selectedParisiItoState β 0 hβ μ t.toNNReal ω)^p‖ ≤
      ‖bcfSpatialDerivative (parisiGradientBCF β ν) j-bcfSpatialDerivative (parisiGradientBCF β ρ) j‖*
        (p:ℝ)*uniformSpatialConstant β j^(p-1) := by
    intro ω
    rw [Real.norm_eq_abs]
    apply (abs_pow_sub_pow_le _ _ p).trans
    have hdiff:|parisiSpatialJet β ν (j+1) t (selectedParisiItoState β 0 hβ μ t.toNNReal ω)-
        parisiSpatialJet β ρ (j+1) t (selectedParisiItoState β 0 hβ μ t.toNNReal ω)| ≤
        ‖bcfSpatialDerivative (parisiGradientBCF β ν) j-bcfSpatialDerivative (parisiGradientBCF β ρ) j‖ := by
      rw [← Real.norm_eq_abs]
      change ‖parisiSlabExtend (by norm_num : (0:ℝ)≤1)
        (bcfSpatialDerivative (parisiGradientBCF β ν) j) _-
        parisiSlabExtend (by norm_num : (0:ℝ)≤1)
          (bcfSpatialDerivative (parisiGradientBCF β ρ) j) _‖≤_
      exact norm_parisiSlabExtend_sub_le (by norm_num) _ _ _
    have hmax : max (|parisiSpatialJet β ν (j+1) t (selectedParisiItoState β 0 hβ μ t.toNNReal ω)|)
        (|parisiSpatialJet β ρ (j+1) t (selectedParisiItoState β 0 hβ μ t.toNNReal ω)|) ≤ uniformSpatialConstant β j := by
      apply max_le
      · rw [← Real.norm_eq_abs]
        exact (norm_parisiSpatialJet_succ_le β ν j t _).trans
          (norm_spatialDerivativeBCF_le_uniform β ν j)
      · rw [← Real.norm_eq_abs]
        exact (norm_parisiSpatialJet_succ_le β ρ j t _).trans
          (norm_spatialDerivativeBCF_le_uniform β ρ j)
    gcongr

  simpa using norm_integral_le_of_norm_le_const (μ:=canonicalBrownianMeasure) (.of_forall hb)

 theorem tendsto_fixedStateJetPower_of_weak {ι : Type*} {L : Filter ι}
    (β : ℝ) (hβ : β≠0) (μ ρ : ParisiMeasure) (ν : ι→ParisiMeasure)
    (hν:Tendsto ν L (nhds ρ)) (j p : ℕ) (t : ℝ) :
    Tendsto (fun i=>fixedStateJetPower β hβ μ (ν i) j p t) L
      (nhds (fixedStateJetPower β hβ μ ρ j p t)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun i=>norm_nonneg _)
    (fun i=>fixedStateJetPower_sub_norm_le β hβ μ (ν i) ρ j p t)
  simpa only [sub_self,norm_zero,zero_mul] using
    (((tendsto_spatialDerivativeBCF_of_weak β j ρ ν hν).sub_const
      (bcfSpatialDerivative (parisiGradientBCF β ρ) j)).norm.mul_const (p:ℝ)).mul_const
        (uniformSpatialConstant β j^(p-1))

end FRSB
