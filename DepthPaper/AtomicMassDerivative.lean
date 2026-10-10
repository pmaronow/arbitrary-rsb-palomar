module

public import DepthPaper.AtomicMassPath
public import DepthPaper.SupportingPlane
public import DepthPaper.SmallRemainderDerivative

@[expose] public section


/-! Actual mass-coordinate derivatives, moving mass from the last atom to
a prescribed earlier atom while keeping all locations fixed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem atomicMass_functional_remainder {r : ℕ} (Ξ : AdmissibleCovariance)
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (i : Fin r) (t : ℝ)
    (ht : IsAtomicPoint (atomicMassPath z i t)) :
    ‖atomicFunctionalExtension Ξ r (atomicMassPath z i t)-atomicFunctionalExtension Ξ r z+
      t*(firstVariation Ξ (atomicMeasure z hz) (atomicLocation z i.castSucc)-
        firstVariation Ξ (atomicMeasure z hz) (atomicLocation z (Fin.last r)))‖ ≤
      (2*‖firstVariationValueMap Ξ (atomicMeasure (atomicMassPath z i t) ht)-
        firstVariationValueMap Ξ (atomicMeasure z hz)‖)*|t| := by
  let μ:=atomicMeasure z hz
  let ν:=atomicMeasure (atomicMassPath z i t) ht
  let a:=firstVariation Ξ μ (atomicLocation z i.castSucc)-firstVariation Ξ μ (atomicLocation z (Fin.last r))
  let b:=firstVariation Ξ ν (atomicLocation z i.castSucc)-firstVariation Ξ ν (atomicLocation z (Fin.last r))
  let Δ:=parisiFunctional Ξ ν-parisiFunctional Ξ μ
  have hp := firstVariation_supporting_planes Ξ μ ν
  rw [integral_massPath_sub z hz i t ht,integral_massPath_sub z hz i t ht] at hp
  change -(t*a)≤Δ ∧ Δ≤-(t*b) at hp
  have hnonneg : 0≤Δ+t*a := by linarith [hp.1]
  have hupper : Δ+t*a≤t*(a-b) := by linarith [hp.2]
  have hi := firstVariation_two_values_sub_norm_le Ξ μ ν
    (atomicOverlap z hz i.castSucc) (atomicOverlap z hz (Fin.last r))
  change ‖b-a‖≤2*‖firstVariationValueMap Ξ ν-firstVariationValueMap Ξ μ‖ at hi
  rw [atomicFunctionalExtension_eq Ξ _ ht,atomicFunctionalExtension_eq Ξ z hz]
  change ‖Δ+t*a‖≤(2*‖firstVariationValueMap Ξ ν-firstVariationValueMap Ξ μ‖)*|t|
  rw [Real.norm_of_nonneg hnonneg]
  calc
    Δ+t*a≤t*(a-b) := hupper
    _≤‖t*(a-b)‖ := le_abs_self _
    _=|t| * ‖a-b‖ := by rw [norm_mul,Real.norm_eq_abs]
    _≤|t| * (2*‖firstVariationValueMap Ξ ν-firstVariationValueMap Ξ μ‖) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg t)
      simpa only [norm_sub_rev] using hi
    _=(2*‖firstVariationValueMap Ξ ν-firstVariationValueMap Ξ μ‖)*|t| := by ring

/-- The actual mass-transfer derivative `f(q_r)-f(q_i)`. -/
theorem hasDerivAt_atomicMassFunctional {r : ℕ} (Ξ : AdmissibleCovariance)
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (i : Fin r) :
    HasDerivAt (fun t=>atomicFunctionalExtension Ξ r (atomicMassPath z i t))
      (firstVariation Ξ (atomicMeasure z hz) (atomicLocation z (Fin.last r))-
        firstVariation Ξ (atomicMeasure z hz) (atomicLocation z i.castSucc)) 0 := by
  let μ:=atomicMeasure z hz
  let φ:ℝ→ℝ:=fun t=>atomicFunctionalExtension Ξ r (atomicMassPath z i t)
  let a:=firstVariation Ξ μ (atomicLocation z i.castSucc)-firstVariation Ξ μ (atomicLocation z (Fin.last r))
  have hpart : HasDerivAt (fun t:ℝ=>t*a) a 0 := by
    simpa only [one_mul,id_eq] using (hasDerivAt_id (0:ℝ)).mul_const a
  have hφ : DifferentiableAt ℝ φ 0 := by
    have houter : ContDiffAt ℝ ∞ (atomicFunctionalExtension Ξ r) (atomicMassPath z i 0) := by
      simpa only [atomicMassPath_zero] using contDiffAt_atomicFunctionalExtension Ξ z hz
    have hc := houter.comp 0 (contDiff_atomicMassPath z i).contDiffAt
    simpa only [φ,Function.comp_def] using hc.differentiableAt (by norm_num)
  let ψ:ℝ→ℝ:=fun t=>φ t+t*a
  let E:ℝ→ℝ:=fun t=>2*‖firstVariationValueMap Ξ (atomicMeasureExtension r (atomicMassPath z i t))-
    firstVariationValueMap Ξ μ‖
  have hE : Tendsto E (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hv := tendsto_firstVariationValueMap_of_weak Ξ _ μ
      (atomicMassPath_measure_tendsto z hz i)
    have hh := (hv.sub_const (firstVariationValueMap Ξ μ)).norm.const_mul 2
    simpa only [E,sub_self,norm_zero,mul_zero] using hh.mono_left nhdsWithin_le_nhds
  have hψ : HasDerivAt ψ 0 0 := by
    apply hasDerivAt_of_right_small_remainder ψ 0 (hφ.add hpart.differentiableAt) E hE
    filter_upwards [(atomicMassPath_mem z hz i).filter_mono nhdsWithin_le_nhds] with t ht
    have hh := atomicMass_functional_remainder Ξ z hz i t ht
    simpa only [ψ,φ,E,μ,a,atomicMassPath_zero,zero_mul,add_zero,sub_zero,
      add_sub_right_comm,atomicMeasureExtension_eq _ ht] using hh
  have hout := hψ.sub hpart
  convert hout using 1
  · funext t
    dsimp only [ψ,φ,μ,a,Pi.sub_apply]
    ring
  · dsimp only [μ,a]
    ring

end DepthPaper
