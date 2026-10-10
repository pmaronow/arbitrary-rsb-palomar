module

public import DepthPaper.PartialAtomicMeasure
public import DepthPaper.AtomMassTransfer

@[expose] public section


/-! The literal location and mass-coordinate derivatives in Corollary 2.3.
Every assertion includes `m=1`; no positive mass at the upper atom is needed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem partialAtomicLocation_functional_remainder {r : ℕ} (Ξ : AdmissibleCovariance)
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (Q : Overlap) (i : Fin r) (t : ℝ) (ht : IsAtomicPoint (atomicLocationPath z i t)) :
    ‖partialAtomicFunctionalExtension Ξ r m Q (atomicLocationPath z i t)-
      partialAtomicFunctionalExtension Ξ r m Q z+
      (m*atomicWeight z i.succ)*(firstVariation Ξ (partialAtomicMeasure z hz m Q) (z.1 i+t)-
        firstVariation Ξ (partialAtomicMeasure z hz m Q) (z.1 i))‖ ≤
      ((m*atomicWeight z i.succ)*‖firstVariationPrimeMap Ξ
        (partialAtomicMeasure (atomicLocationPath z i t) ht m Q)-
        firstVariationPrimeMap Ξ (partialAtomicMeasure z hz m Q)‖)*|t| := by
  let μ:=partialAtomicMeasure z hz m Q
  let ν:=partialAtomicMeasure (atomicLocationPath z i t) ht m Q
  let w:=m*atomicWeight z i.succ
  let A:=firstVariation Ξ μ (z.1 i+t)-firstVariation Ξ μ (z.1 i)
  let B:=firstVariation Ξ ν (z.1 i+t)-firstVariation Ξ ν (z.1 i)
  let Δ:=parisiFunctional Ξ ν-parisiFunctional Ξ μ
  have hp:=firstVariation_supporting_planes Ξ μ ν
  rw [integral_partialAtomicLocationPath_sub z hz m hm Q i t ht _
    (continuous_firstVariation_overlap Ξ μ),
    integral_partialAtomicLocationPath_sub z hz m hm Q i t ht _
      (continuous_firstVariation_overlap Ξ ν)] at hp
  change -(w*A)≤Δ ∧ Δ≤-(w*B) at hp
  have hw : 0≤w := mul_nonneg hm.1 (hz.2.2 i.succ).le
  have hnonneg : 0≤Δ+w*A := by linarith [hp.1]
  have hupper : Δ+w*A≤w*(A-B) := by linarith [hp.2]
  have ha : z.1 i∈Icc (0:ℝ) 1 := by
    simpa only [atomicLocation_succ] using atomicLocation_mem_unit hz i.succ
  have hb : z.1 i+t∈Icc (0:ℝ) 1 := by
    simpa only [atomicLocation_locationPath_same] using atomicLocation_mem_unit ht i.succ
  have hi:=firstVariation_increment_sub_norm_le Ξ μ ν ha hb
  change ‖B-A‖≤‖firstVariationPrimeMap Ξ ν-firstVariationPrimeMap Ξ μ‖*|z.1 i+t-z.1 i| at hi
  simp only [add_sub_cancel_left] at hi
  simp only [partialAtomicFunctionalExtension,partialAtomicMeasureExtension_eq _ ht,
    partialAtomicMeasureExtension_eq z hz]
  change ‖Δ+w*A‖≤(w*‖firstVariationPrimeMap Ξ ν-firstVariationPrimeMap Ξ μ‖)*|t|
  rw [Real.norm_of_nonneg hnonneg]
  calc
    Δ+w*A≤w*(A-B) := hupper
    _≤w*‖A-B‖ := mul_le_mul_of_nonneg_left (le_abs_self _) hw
    _≤w*(‖firstVariationPrimeMap Ξ ν-firstVariationPrimeMap Ξ μ‖*|t|) := by
      apply mul_le_mul_of_nonneg_left _ hw
      simpa only [norm_sub_rev] using hi
    _=(w*‖firstVariationPrimeMap Ξ ν-firstVariationPrimeMap Ξ μ‖)*|t| := by ring

theorem hasDerivAt_partialAtomicLocationFunctional {r : ℕ} (Ξ : AdmissibleCovariance)
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (Q : Overlap) (i : Fin r) :
    HasDerivAt (fun t=>partialAtomicFunctionalExtension Ξ r m Q (atomicLocationPath z i t))
      (-(m*atomicWeight z i.succ)*firstVariationDerivative Ξ
        (partialAtomicMeasure z hz m Q) (z.1 i)) 0 := by
  let μ:=partialAtomicMeasure z hz m Q
  let φ:ℝ→ℝ:=fun t=>partialAtomicFunctionalExtension Ξ r m Q (atomicLocationPath z i t)
  let q:=z.1 i
  let w:=m*atomicWeight z i.succ
  have hq : q∈Ioo (0:ℝ) 1 := by
    constructor
    · simpa only [q,atomicLocation_zero,atomicLocation_succ] using hz.1 (Fin.succ_pos i)
    · exact (show q≤atomicLocation z (Fin.last r) from
        (hz.1.monotone (Fin.le_last i.succ))).trans_lt hz.2.1
  have harg : HasDerivAt (fun t:ℝ=>q+t) 1 0 := by
    simpa only [id_eq] using (hasDerivAt_id (0:ℝ)).const_add q
  have hd : HasDerivAt (fun t=>firstVariation Ξ μ (q+t)) (firstVariationDerivative Ξ μ q) 0 := by
    have hb : HasDerivAt (firstVariation Ξ μ) (firstVariationDerivative Ξ μ q) (q+0) := by
      simpa only [add_zero,firstVariationDerivative] using hasDerivAt_firstVariation Ξ μ hq
    simpa only [Function.comp_def,mul_one] using hb.comp 0 harg
  have hpart:=(hd.sub_const (firstVariation Ξ μ q)).const_mul w
  let ψ:ℝ→ℝ:=fun t=>φ t+w*(firstVariation Ξ μ (q+t)-firstVariation Ξ μ q)
  let E:ℝ→ℝ:=fun t=>w*‖firstVariationPrimeMap Ξ
    (partialAtomicMeasureExtension r m Q (atomicLocationPath z i t))-firstVariationPrimeMap Ξ μ‖
  have hE : Tendsto E (𝓝 (0:ℝ)) (𝓝 0) := by
    have hv:=tendsto_firstVariationPrimeMap_of_weak Ξ _ μ
      (partialAtomicLocationPath_measure_tendsto z hz m hm Q i)
    simpa only [E,sub_self,norm_zero,mul_zero] using
      (hv.sub_const (firstVariationPrimeMap Ξ μ)).norm.const_mul w
  have hψ : HasDerivAt ψ 0 0 := by
    apply hasDerivAt_of_small_remainder ψ 0 E hE
    filter_upwards [atomicLocationPath_mem z hz i] with t ht
    have hh:=partialAtomicLocation_functional_remainder Ξ z hz m hm Q i t ht
    simpa only [ψ,φ,E,μ,q,w,atomicLocationPath_zero,add_zero,sub_self,mul_zero,zero_mul,
      sub_zero,add_sub_right_comm,partialAtomicMeasureExtension_eq _ ht] using hh
  have hout:=hψ.sub hpart
  convert hout using 1
  · funext t
    dsimp only [ψ,φ,w,q,μ,Pi.sub_apply]
    ring
  · dsimp only [w,q,μ]
    ring

theorem partialAtomicMass_functional_remainder {r : ℕ} (Ξ : AdmissibleCovariance)
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (Q : Overlap) (i : Fin r) (t : ℝ) (ht : IsAtomicPoint (atomicMassPath z i t)) :
    ‖partialAtomicFunctionalExtension Ξ r m Q (atomicMassPath z i t)-
      partialAtomicFunctionalExtension Ξ r m Q z+
      (m*t)*(firstVariation Ξ (partialAtomicMeasure z hz m Q) (atomicLocation z i.castSucc)-
        firstVariation Ξ (partialAtomicMeasure z hz m Q) (atomicLocation z (Fin.last r)))‖ ≤
      (2*m*‖firstVariationValueMap Ξ (partialAtomicMeasure (atomicMassPath z i t) ht m Q)-
        firstVariationValueMap Ξ (partialAtomicMeasure z hz m Q)‖)*|t| := by
  let μ:=partialAtomicMeasure z hz m Q
  let ν:=partialAtomicMeasure (atomicMassPath z i t) ht m Q
  let A:=firstVariation Ξ μ (atomicLocation z i.castSucc)-firstVariation Ξ μ (atomicLocation z (Fin.last r))
  let B:=firstVariation Ξ ν (atomicLocation z i.castSucc)-firstVariation Ξ ν (atomicLocation z (Fin.last r))
  let Δ:=parisiFunctional Ξ ν-parisiFunctional Ξ μ
  have hp:=firstVariation_supporting_planes Ξ μ ν
  rw [integral_partialAtomicMassPath_sub z hz m hm Q i t ht _ (continuous_firstVariation_overlap Ξ μ),
    integral_partialAtomicMassPath_sub z hz m hm Q i t ht _ (continuous_firstVariation_overlap Ξ ν)] at hp
  change -((m*t)*A)≤Δ ∧ Δ≤-((m*t)*B) at hp
  have hnonneg : 0≤Δ+(m*t)*A := by linarith [hp.1]
  have hupper : Δ+(m*t)*A≤(m*t)*(A-B) := by linarith [hp.2]
  have hi:=firstVariation_two_values_sub_norm_le Ξ μ ν
    (atomicOverlap z hz i.castSucc) (atomicOverlap z hz (Fin.last r))
  change ‖B-A‖≤2*‖firstVariationValueMap Ξ ν-firstVariationValueMap Ξ μ‖ at hi
  simp only [partialAtomicFunctionalExtension,partialAtomicMeasureExtension_eq _ ht,
    partialAtomicMeasureExtension_eq z hz]
  change ‖Δ+(m*t)*A‖≤(2*m*‖firstVariationValueMap Ξ ν-firstVariationValueMap Ξ μ‖)*|t|
  rw [Real.norm_of_nonneg hnonneg]
  calc
    Δ+(m*t)*A≤(m*t)*(A-B) := hupper
    _≤‖(m*t)*(A-B)‖ := le_abs_self _
    _=(m*|t|)*‖A-B‖ := by rw [norm_mul,norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hm.1]
    _≤(m*|t|)*(2*‖firstVariationValueMap Ξ ν-firstVariationValueMap Ξ μ‖) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hm.1 (abs_nonneg t))
      simpa only [norm_sub_rev] using hi
    _=(2*m*‖firstVariationValueMap Ξ ν-firstVariationValueMap Ξ μ‖)*|t| := by ring

theorem hasDerivAt_partialAtomicMassFunctional {r : ℕ} (Ξ : AdmissibleCovariance)
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (Q : Overlap) (i : Fin r) :
    HasDerivAt (fun t=>partialAtomicFunctionalExtension Ξ r m Q (atomicMassPath z i t))
      (m*(firstVariation Ξ (partialAtomicMeasure z hz m Q) (atomicLocation z (Fin.last r))-
        firstVariation Ξ (partialAtomicMeasure z hz m Q) (atomicLocation z i.castSucc))) 0 := by
  let μ:=partialAtomicMeasure z hz m Q
  let φ:ℝ→ℝ:=fun t=>partialAtomicFunctionalExtension Ξ r m Q (atomicMassPath z i t)
  let A:=m*(firstVariation Ξ μ (atomicLocation z i.castSucc)-firstVariation Ξ μ (atomicLocation z (Fin.last r)))
  have hpart : HasDerivAt (fun t:ℝ=>t*A) A 0 := by
    simpa only [one_mul,id_eq] using (hasDerivAt_id (0:ℝ)).mul_const A
  let ψ:ℝ→ℝ:=fun t=>φ t+t*A
  let E:ℝ→ℝ:=fun t=>2*m*‖firstVariationValueMap Ξ
    (partialAtomicMeasureExtension r m Q (atomicMassPath z i t))-firstVariationValueMap Ξ μ‖
  have hE : Tendsto E (𝓝 (0:ℝ)) (𝓝 0) := by
    have hv:=tendsto_firstVariationValueMap_of_weak Ξ _ μ
      (partialAtomicMassPath_measure_tendsto z hz m hm Q i)
    simpa only [E,sub_self,norm_zero,mul_zero] using
      (hv.sub_const (firstVariationValueMap Ξ μ)).norm.const_mul (2*m)
  have hψ : HasDerivAt ψ 0 0 := by
    apply hasDerivAt_of_small_remainder ψ 0 E hE
    filter_upwards [atomicMassPath_mem z hz i] with t ht
    have hh:=partialAtomicMass_functional_remainder Ξ z hz m hm Q i t ht
    have he : t*A=(m*t)*(firstVariation Ξ μ (atomicLocation z i.castSucc)-
        firstVariation Ξ μ (atomicLocation z (Fin.last r))) := by dsimp only [A]; ring
    simpa only [ψ,φ,E,μ,atomicMassPath_zero,zero_mul,add_zero,sub_zero,
      add_sub_right_comm,partialAtomicMeasureExtension_eq _ ht,he] using hh
  have hout:=hψ.sub hpart
  convert hout using 1
  · funext t
    dsimp only [ψ,φ,A,μ,Pi.sub_apply]
    ring
  · dsimp only [A,μ]
    ring

end DepthPaper
