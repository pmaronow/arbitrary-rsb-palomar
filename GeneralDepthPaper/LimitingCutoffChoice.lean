module

public import GeneralDepthPaper.LimitingVariationFamily

@[expose] public section


/-! The cutoff and its strict uniform negative margin are derived from
the actual first variation of the nondegenerate limiting branch. -/
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 64

namespace LimitingStandingData
variable {Ξ:AdmissibleCovariance} {r:ℕ} {seed:AtomicPoint r}

def limitingVariation (d:LimitingStandingData Ξ seed) (m:d.MassInterval) (q:ℝ) : ℝ :=
  (m:ℝ)⁻¹^2*(d.limitingVariationData m).firstVariation q

theorem limitingVariation_eq_jet (d:LimitingStandingData Ξ seed) (m:d.MassInterval)
    (q:TruncatedClockDomain 1) : d.limitingVariation m q=d.limitingVariationJets m 0 q := rfl

theorem limitingVariation_eq_actual (d:LimitingStandingData Ξ seed) (m:d.MassInterval)
    (q:ℝ) (hq:q∈Icc (0:ℝ) 1) :
    d.limitingVariation m q=(m:ℝ)⁻¹^2*firstVariation ((temperatureCovarianceFamily Ξ).covariance m)
      (atomicMeasure (d.branch m) (d.branch_nondegenerate m m.property).choose) q := by
  unfold limitingVariation limitingVariationData
  rw [←firstVariation_atomicMeasure_eq_truncated _ _ _ q hq]

theorem limitingVariation_lipschitz_bound (d:LimitingStandingData Ξ seed)
    {B:ℝ} (hb:∀m:d.MassInterval,∀j:Fin 3,∀q:TruncatedClockDomain 1,
      |d.limitingVariationJets m j q| ≤ B) (m:d.MassInterval)
    {q:ℝ} (hq:q∈Icc (0:ℝ) 1) :
    |d.limitingVariation m q-d.limitingVariation m 1| ≤ B*(1-q) := by
  have hd (q:ℝ):HasDerivAt (d.limitingVariation m)
      ((m:ℝ)⁻¹^2*(d.limitingVariationData m).firstVariationPrime q) q :=
    ((d.limitingVariationData m).hasDerivAt_firstVariation q).const_mul _
  have hbd:∀x∈Icc (0:ℝ) 1,‖deriv (d.limitingVariation m) x‖ ≤ B := by
    intro x hx
    rw [(hd x).deriv,Real.norm_eq_abs]
    have hh:=hb m 1 ⟨x,hx⟩
    change |(m:ℝ)⁻¹^2*(d.limitingVariationData m).firstVariationPrimeMap ⟨x,hx⟩| ≤ B at hh
    rw [TruncatedParisiData.firstVariationPrimeMap_apply] at hh
    exact hh
  have hh:=(convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun x (_:x∈Icc (0:ℝ) 1)=>(hd x).differentiableAt) hbd
    (show (1:ℝ)∈Icc (0:ℝ) 1 by norm_num) hq
  simpa only [Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hq.2),neg_sub] using hh

theorem limiting_cutoff_choice (d:LimitingStandingData Ξ seed) :
    ∃gamma:ℝ,0 < gamma ∧ ∃qc:ℝ,qc∈Ioo d.cutoff 1 ∧
      (∀m:d.MassInterval,d.limitingVariation m 1 ≤ -5*gamma) ∧
      (∀m:d.MassInterval,∀q∈Icc qc 1,d.limitingVariation m q ≤ -4*gamma) ∧
      (1/2:ℝ)*(∫q in qc..1,(1-q)*Ξ.second q) ≤ gamma := by
  have hend:Continuous (fun m:d.MassInterval=>d.limitingVariation m 1) := by
    have h0:Continuous (fun m:d.MassInterval=>d.limitingVariationJets m 0) :=
      (continuous_apply 0).comp d.continuous_limitingVariationJets
    exact (ContinuousMap.evalCLM (R:=ℝ) (M:=ℝ) (⟨1,by norm_num⟩:TruncatedClockDomain 1)).continuous.comp h0
  obtain ⟨mm,_,hmax⟩:=isCompact_univ.exists_isMaxOn
    (show (univ:Set d.MassInterval).Nonempty from ⟨⟨1,⟨d.massLower_mem.2.le,le_rfl⟩⟩,mem_univ _⟩)
    hend.continuousOn
  have hneg:d.limitingVariation mm 1 < 0 := d.limitingVariation_endpoint_neg mm
  let gamma:ℝ := -d.limitingVariation mm 1/5
  have hgamma:0 < gamma := by dsimp only [gamma];linarith
  have hgmax:∀m:d.MassInterval,d.limitingVariation m 1 ≤ -5*gamma := by
    intro m
    have hh:=hmax (mem_univ m)
    change d.limitingVariation m 1 ≤ d.limitingVariation mm 1 at hh
    dsimp only [gamma]
    linarith
  obtain ⟨B,hB,hbound⟩:=d.limitingVariationJets_uniform_bound
  have hbase:∀ᶠq in 𝓝 (1:ℝ),endpointBaseIntegral Ξ q < 2*gamma := by
    have hz:endpointBaseIntegral Ξ 1=0 := by simp [endpointBaseIntegral]
    have hlt:endpointBaseIntegral Ξ 1 < 2*gamma := by rw [hz];positivity
    exact (show ContinuousAt (endpointBaseIntegral Ξ) 1 from
      (contDiff_endpointBaseIntegral Ξ).continuous.continuousAt).eventually
        (eventually_lt_nhds hlt)
  obtain ⟨δ0,hδ0,hδball⟩:=Metric.mem_nhds_iff.mp hbase
  have hpositive:0 < min (gamma/(B+1)) (min (1-d.cutoff) δ0) :=
    lt_min (by positivity) (lt_min (by linarith [d.cutoff_mem.2]) hδ0)
  obtain ⟨δ,hδ,hδsmall⟩:=exists_between hpositive
  have hδg:δ < gamma/(B+1) := hδsmall.trans_le (min_le_left _ _)
  have hδcut:δ < 1-d.cutoff := hδsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδd:δ < δ0 := hδsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let qc:ℝ:=1-δ/2
  have hqc:qc∈Ioo d.cutoff 1 := by constructor <;> dsimp only [qc] <;> linarith
  refine ⟨gamma,hgamma,qc,hqc,hgmax,?_,?_⟩
  · intro m q hq
    have hqunit:q∈Icc (0:ℝ) 1 := ⟨d.cutoff_mem.1.le.trans (hqc.1.le.trans hq.1),hq.2⟩
    have hLip:=d.limitingVariation_lipschitz_bound hbound m hqunit
    have hg:=hgmax m
    have hbg:δ*(B+1) < gamma := (lt_div_iff₀ (by linarith)).mp hδg
    have hqgap:1-q ≤ δ/2 := by dsimp only [qc] at hq;linarith [hq.1]
    have hBq:=mul_le_mul_of_nonneg_left hqgap hB
    nlinarith [(abs_le.mp hLip).2]
  · have hqball:qc∈ball (1:ℝ) δ0 := by
      rw [mem_ball,Real.dist_eq,abs_lt]
      dsimp only [qc]
      constructor <;> linarith
    have hh:=hδball hqball
    change endpointBaseIntegral Ξ qc < 2*gamma at hh
    rw [endpointBaseIntegral_eq_integral] at hh
    linarith

end LimitingStandingData
end GeneralDepthPaper
