module

public import GeneralDepthPaper.AtomMoveOperations
public import GeneralDepthPaper.SupportingPlane
public import GeneralDepthPaper.SmallRemainderDirect

@[expose] public section


/-! Moving an arbitrary interior atom of an arbitrary genuine order
parameter. This proves the location formula without fixing the lowest atom
at zero and without assuming differentiability of the measure curve. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace GeneralDepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem atomMove_functional_remainder (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (a : Overlap) (t : ℝ) :
    ‖parisiFunctional Ξ (moveAtom μ a t)-parisiFunctional Ξ μ+
      atomWeight μ a*(firstVariation Ξ μ (movedOverlap a t)-firstVariation Ξ μ a)‖ ≤
      (atomWeight μ a*‖firstVariationPrimeMap Ξ (moveAtom μ a t)-firstVariationPrimeMap Ξ μ‖)*
        |(movedOverlap a t:ℝ)-(a:ℝ)| := by
  let ν:=moveAtom μ a t
  let w:=atomWeight μ a
  let A:=firstVariation Ξ μ (movedOverlap a t)-firstVariation Ξ μ a
  let B:=firstVariation Ξ ν (movedOverlap a t)-firstVariation Ξ ν a
  let Δ:=parisiFunctional Ξ ν-parisiFunctional Ξ μ
  have hmove (ρ : ParisiMeasure) :
      (∫q : Overlap,firstVariation Ξ ρ q ∂(ν : Measure Overlap))-
        (∫q : Overlap,firstVariation Ξ ρ q ∂(μ : Measure Overlap))=
        w*(firstVariation Ξ ρ (movedOverlap a t)-firstVariation Ξ ρ a) := by
    simpa only [BoundedContinuousFunction.mkOfCompact_apply,firstVariationValueMap_apply] using
      integral_moveAtom_sub μ a t (BoundedContinuousFunction.mkOfCompact (firstVariationValueMap Ξ ρ))
  have hp:=firstVariation_supporting_planes Ξ μ ν
  rw [hmove μ,hmove ν] at hp
  change -(w*A)≤Δ ∧ Δ≤-(w*B) at hp
  have hw:=atomWeight_nonneg μ a
  have hnonneg : 0≤Δ+w*A := by linarith [hp.1]
  have hupper : Δ+w*A≤w*(A-B) := by linarith [hp.2]
  have hi:=firstVariation_increment_sub_norm_le Ξ μ ν a.property (movedOverlap a t).property
  change ‖B-A‖≤‖firstVariationPrimeMap Ξ ν-firstVariationPrimeMap Ξ μ‖*
    |(movedOverlap a t:ℝ)-(a:ℝ)| at hi
  change ‖Δ+w*A‖≤(w*‖firstVariationPrimeMap Ξ ν-firstVariationPrimeMap Ξ μ‖)*_
  rw [Real.norm_of_nonneg hnonneg]
  calc
    Δ+w*A≤w*(A-B) := hupper
    _≤w*‖A-B‖ := mul_le_mul_of_nonneg_left (le_abs_self _) hw
    _≤w*(‖firstVariationPrimeMap Ξ ν-firstVariationPrimeMap Ξ μ‖*
        |(movedOverlap a t:ℝ)-(a:ℝ)|) := by
      apply mul_le_mul_of_nonneg_left _ hw
      simpa only [norm_sub_rev] using hi
    _=(w*‖firstVariationPrimeMap Ξ ν-firstVariationPrimeMap Ξ μ‖)*
        |(movedOverlap a t:ℝ)-(a:ℝ)| := by ring

/-- Literal location derivative, valid even for a nonatomic remainder. -/
theorem hasDerivAt_parisiFunctional_moveAtom (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (a : Overlap) (ha : (a:ℝ)∈Ioo (0:ℝ) 1) :
    HasDerivAt (fun t=>parisiFunctional Ξ (moveAtom μ a t))
      (-atomWeight μ a*firstVariationDerivative Ξ μ a) 0 := by
  let φ:ℝ→ℝ:=fun t=>parisiFunctional Ξ (moveAtom μ a t)
  let w:=atomWeight μ a
  have harg : HasDerivAt (fun t:ℝ=>(a:ℝ)+t) 1 0 := by
    simpa only [id_eq] using (hasDerivAt_id (0:ℝ)).const_add (a:ℝ)
  have hbase : HasDerivAt (firstVariation Ξ μ) (firstVariationDerivative Ξ μ a) ((a:ℝ)+0) := by
    simpa only [add_zero,firstVariationDerivative] using hasDerivAt_firstVariation Ξ μ ha
  have hd : HasDerivAt (fun t=>firstVariation Ξ μ ((a:ℝ)+t)) (firstVariationDerivative Ξ μ a) 0 := by
    simpa only [mul_one,Function.comp_def] using hbase.comp 0 harg
  have hpart := (hd.sub_const (firstVariation Ξ μ a)).const_mul w
  let ψ:ℝ→ℝ:=fun t=>φ t+w*(firstVariation Ξ μ ((a:ℝ)+t)-firstVariation Ξ μ a)
  let E:ℝ→ℝ:=fun t=>w*‖firstVariationPrimeMap Ξ (moveAtom μ a t)-firstVariationPrimeMap Ξ μ‖
  have hE : Tendsto E (𝓝 (0:ℝ)) (𝓝 0) := by
    have hp:=tendsto_firstVariationPrimeMap_of_weak Ξ (moveAtom μ a) μ (tendsto_moveAtom_zero μ a)
    simpa only [E,sub_self,norm_zero,mul_zero] using
      (hp.sub_const (firstVariationPrimeMap Ξ μ)).norm.const_mul w
  have hin : ∀ᶠt in 𝓝 (0:ℝ),(a:ℝ)+t∈Icc (0:ℝ) 1 := by
    apply (continuous_const.add continuous_id).continuousAt
    simpa only [Pi.add_apply,id_eq,add_zero] using Icc_mem_nhds ha.1 ha.2
  have hψ : HasDerivAt ψ 0 0 := by
    apply hasDerivAt_of_small_remainder ψ 0 E hE
    filter_upwards [hin] with t ht
    have he : (movedOverlap a t:ℝ)=(a:ℝ)+t := by
      simp only [movedOverlap,projIcc_of_mem (by norm_num : (0:ℝ)≤1) ht]
    have hh:=atomMove_functional_remainder Ξ μ a t
    rw [he] at hh
    simp only [add_sub_cancel_left] at hh
    simpa only [ψ,φ,E,w,moveAtom_zero,add_zero,sub_self,mul_zero,zero_mul,sub_zero,
      add_sub_right_comm] using hh
  have hout:=hψ.sub hpart
  convert hout using 1
  · funext t
    dsimp only [ψ,φ,w,Pi.sub_apply]
    ring
  · dsimp only [w]
    ring

end GeneralDepthPaper
