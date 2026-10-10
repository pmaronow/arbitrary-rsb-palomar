module

public import DepthPaper.AtomicLocationPath
public import DepthPaper.SupportingPlane
public import DepthPaper.SmallRemainderDerivative

@[expose] public section


/-! The literal location derivative of the actual finite atomic Parisi
functional. Convex supporting planes and genuine uniform weak-measure
observable continuity identify the derivative of the smooth chart. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

 theorem atomicLocation_functional_remainder {r : ℕ} (Ξ : AdmissibleCovariance)
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (i : Fin r) (t : ℝ)
    (ht : IsAtomicPoint (atomicLocationPath z i t)) :
    ‖atomicFunctionalExtension Ξ r (atomicLocationPath z i t)-atomicFunctionalExtension Ξ r z+
      atomicWeight z i.succ*(firstVariation Ξ (atomicMeasure z hz) (z.1 i+t)-
        firstVariation Ξ (atomicMeasure z hz) (z.1 i))‖ ≤
      (atomicWeight z i.succ*‖firstVariationPrimeMap Ξ (atomicMeasure (atomicLocationPath z i t) ht)-
        firstVariationPrimeMap Ξ (atomicMeasure z hz)‖)*|t| := by
  let μ:=atomicMeasure z hz
  let ν:=atomicMeasure (atomicLocationPath z i t) ht
  let w:=atomicWeight z i.succ
  let a:=firstVariation Ξ μ (z.1 i+t)-firstVariation Ξ μ (z.1 i)
  let b:=firstVariation Ξ ν (z.1 i+t)-firstVariation Ξ ν (z.1 i)
  let Δ:=parisiFunctional Ξ ν-parisiFunctional Ξ μ
  have hp := firstVariation_supporting_planes Ξ μ ν
  rw [integral_locationPath_sub z hz i t ht,integral_locationPath_sub z hz i t ht] at hp
  change -(w*a)≤Δ ∧ Δ≤-(w*b) at hp
  have hw : 0≤w := (hz.2.2 i.succ).le
  have hnonneg : 0≤Δ+w*a := by linarith [hp.1]
  have hupper : Δ+w*a≤w*(a-b) := by linarith [hp.2]
  have ha : z.1 i∈Icc (0:ℝ) 1 := by
    simpa only [atomicLocation_succ] using atomicLocation_mem_unit hz i.succ
  have hb : z.1 i+t∈Icc (0:ℝ) 1 := by
    simpa only [atomicLocation_locationPath_same] using atomicLocation_mem_unit ht i.succ
  have hi := firstVariation_increment_sub_norm_le Ξ μ ν ha hb
  change ‖b-a‖≤‖firstVariationPrimeMap Ξ ν-firstVariationPrimeMap Ξ μ‖*|z.1 i+t-z.1 i| at hi
  simp only [add_sub_cancel_left] at hi
  rw [atomicFunctionalExtension_eq Ξ _ ht,atomicFunctionalExtension_eq Ξ z hz]
  change ‖Δ+w*a‖≤(w*‖firstVariationPrimeMap Ξ ν-firstVariationPrimeMap Ξ μ‖)*|t|
  rw [Real.norm_of_nonneg hnonneg]
  calc
    Δ+w*a≤w*(a-b) := hupper
    _≤w*‖a-b‖ := mul_le_mul_of_nonneg_left (le_abs_self _) hw
    _≤w*(‖firstVariationPrimeMap Ξ ν-firstVariationPrimeMap Ξ μ‖*|t|) := by
      apply mul_le_mul_of_nonneg_left _ hw
      simpa only [norm_sub_rev] using hi
    _=(w*‖firstVariationPrimeMap Ξ ν-firstVariationPrimeMap Ξ μ‖)*|t| := by ring

/-- Equation (2.3): moving an interior atom while fixing every mass and every
other location gives the actual derivative `-w_i f'(q_i)`. -/
theorem hasDerivAt_atomicLocationFunctional {r : ℕ} (Ξ : AdmissibleCovariance)
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (i : Fin r) :
    HasDerivAt (fun t=>atomicFunctionalExtension Ξ r (atomicLocationPath z i t))
      (-atomicWeight z i.succ*firstVariationDerivative Ξ (atomicMeasure z hz) (z.1 i)) 0 := by
  let μ:=atomicMeasure z hz
  let φ:ℝ→ℝ:=fun t=>atomicFunctionalExtension Ξ r (atomicLocationPath z i t)
  let q:=z.1 i
  let w:=atomicWeight z i.succ
  have hq : q∈Ioo (0:ℝ) 1 := by
    constructor
    · simpa only [q,atomicLocation_zero,atomicLocation_succ] using hz.1 (Fin.succ_pos i)
    · exact (show q≤atomicLocation z (Fin.last r) from
        (hz.1.monotone (Fin.le_last i.succ))).trans_lt hz.2.1
  have harg : HasDerivAt (fun t:ℝ=>q+t) 1 0 := by
    simpa only [id_eq] using (hasDerivAt_id (0:ℝ)).const_add q
  have hd : HasDerivAt (fun t=>firstVariation Ξ μ (q+t)) (firstVariationDerivative Ξ μ q) 0 := by
    have hbase : HasDerivAt (firstVariation Ξ μ) (firstVariationDerivative Ξ μ q) (q+0) := by
      simpa only [add_zero,firstVariationDerivative] using hasDerivAt_firstVariation Ξ μ hq
    simpa only [mul_one,Function.comp_def] using hbase.comp 0 harg
  have hpart : HasDerivAt (fun t=>w*(firstVariation Ξ μ (q+t)-firstVariation Ξ μ q))
      (w*firstVariationDerivative Ξ μ q) 0 := (hd.sub_const _).const_mul w
  have hφ : DifferentiableAt ℝ φ 0 := by
    have houter : ContDiffAt ℝ ∞ (atomicFunctionalExtension Ξ r) (atomicLocationPath z i 0) := by
      simpa only [atomicLocationPath_zero] using contDiffAt_atomicFunctionalExtension Ξ z hz
    have hc := houter.comp 0 (contDiff_atomicLocationPath z i).contDiffAt
    simpa only [φ,atomicLocationPath_zero,Function.comp_def] using hc.differentiableAt (by norm_num)
  let ψ:ℝ→ℝ:=fun t=>φ t+w*(firstVariation Ξ μ (q+t)-firstVariation Ξ μ q)
  let E:ℝ→ℝ:=fun t=>w*‖firstVariationPrimeMap Ξ (atomicMeasureExtension r (atomicLocationPath z i t))-
    firstVariationPrimeMap Ξ μ‖
  have hE : Tendsto E (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hprime := tendsto_firstVariationPrimeMap_of_weak Ξ _ μ
      (atomicLocationPath_measure_tendsto z hz i)
    have hh := (hprime.sub_const (firstVariationPrimeMap Ξ μ)).norm.const_mul w
    simpa only [E,sub_self,norm_zero,mul_zero] using hh.mono_left nhdsWithin_le_nhds
  have hψ : HasDerivAt ψ 0 0 := by
    apply hasDerivAt_of_right_small_remainder ψ 0 (hφ.add hpart.differentiableAt) E hE
    filter_upwards [(atomicLocationPath_mem z hz i).filter_mono nhdsWithin_le_nhds] with t ht
    have hh := atomicLocation_functional_remainder Ξ z hz i t ht
    simpa only [ψ,φ,E,μ,q,w,atomicLocationPath_zero,add_zero,sub_self,mul_zero,sub_zero,
      zero_mul,add_sub_right_comm,atomicMeasureExtension_eq _ ht] using hh
  have hout := hψ.sub hpart
  convert hout using 1
  · funext t
    dsimp only [ψ,φ,μ,w,q,Pi.sub_apply]
    ring
  · dsimp only [μ,w]
    ring

end DepthPaper
