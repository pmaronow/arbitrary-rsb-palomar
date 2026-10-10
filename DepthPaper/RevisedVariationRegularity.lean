module

public import DepthPaper.RevisedModel
public import DepthPaper.ContactPerturbation
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

/-! Actual first-variation C² regularity on the full closed overlap interval
and convex supporting planes for every finite positive even covariance. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace DepthPaper.RevisedCovariance
set_option maxHeartbeats 500000

def firstVariationDerivative (Ξ : RevisedCovariance) (μ : ParisiMeasure) (q : ℝ) : ℝ :=
  (1/2:ℝ)*Ξ.second q*(Gamma Ξ μ q-q)

theorem contDiff_covariance_second (Ξ : RevisedCovariance) :
    ContDiff ℝ ∞ Ξ.second := by
  unfold RevisedCovariance.second
  fun_prop

theorem contDiffOn_firstVariationDerivative (Ξ : RevisedCovariance) (μ : ParisiMeasure) :
    ContDiffOn ℝ 1 (firstVariationDerivative Ξ μ) (Icc (0:ℝ) 1) :=
  ((contDiffOn_const.mul ((contDiff_covariance_second Ξ).of_le (by norm_num)).contDiffOn).mul
    ((contDiffOn_Gamma_one Ξ μ).sub contDiffOn_id))

theorem hasDerivWithinAt_firstVariation (Ξ : RevisedCovariance) (μ : ParisiMeasure)
    {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (firstVariation Ξ μ) (firstVariationDerivative Ξ μ q)
      (Icc (0:ℝ) 1) q := by
  let d := firstVariationDerivative Ξ μ
  let ext : ℝ→ℝ := fun x=>d (Set.projIcc (0:ℝ) 1 (by norm_num) x)
  have hext : Continuous ext :=
    (((contDiffOn_firstVariationDerivative Ξ μ).continuousOn.comp_continuous
      continuous_subtype_val (fun x : Icc (0:ℝ) 1=>x.property)).comp continuous_projIcc)
  have heq : EqOn (fun x=>∫s in (0:ℝ)..x,ext s) (firstVariation Ξ μ) (Icc (0:ℝ) 1) := by
    intro x hx
    rw [firstVariation_eq,←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hx.1]
    intro s hs
    have hsm : s∈Icc (0:ℝ) 1 := ⟨hs.1,hs.2.trans hx.2⟩
    dsimp only [ext,d,firstVariationDerivative]
    rw [Set.projIcc_of_mem _ hsm]
    dsimp only
    ring
  have hd : HasDerivWithinAt (fun x=>∫s in (0:ℝ)..x,ext s) (ext q)
      (Icc (0:ℝ) 1) q := (intervalIntegral.integral_hasDerivAt_right (hext.intervalIntegrable (0:ℝ) q)
    (hext.stronglyMeasurableAtFilter volume (nhds q)) hext.continuousAt).hasDerivWithinAt
  have hval : ext q=firstVariationDerivative Ξ μ q := by
    dsimp only [ext,d]
    rw [Set.projIcc_of_mem _ hq]
  rw [hval] at hd
  exact hd.congr_of_mem (fun x hx=>(heq hx).symm) hq

theorem derivWithin_firstVariation (Ξ : RevisedCovariance) (μ : ParisiMeasure)
    {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    derivWithin (firstVariation Ξ μ) (Icc (0:ℝ) 1) q=firstVariationDerivative Ξ μ q :=
  (hasDerivWithinAt_firstVariation Ξ μ hq).derivWithin
    (uniqueDiffOn_Icc (by norm_num) q hq)

/-- The first variation really is C² on the manuscript's entire overlap
interval, including the terminal endpoint and every cumulative-mass atom. -/
theorem contDiffOn_firstVariation_two (Ξ : RevisedCovariance) (μ : ParisiMeasure) :
    ContDiffOn ℝ 2 (firstVariation Ξ μ) (Icc (0:ℝ) 1) := by
  rw [show (2:ℕ∞ω)=1+1 by norm_num,contDiffOn_succ_iff_derivWithin
    (uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1))]
  refine ⟨fun q hq=>(hasDerivWithinAt_firstVariation Ξ μ hq).differentiableWithinAt,
    by simp,?_⟩
  exact (contDiffOn_firstVariationDerivative Ξ μ).congr
    (fun q hq=>derivWithin_firstVariation Ξ μ hq)

theorem continuousOn_closed_firstVariation_second (Ξ : RevisedCovariance)
    (μ : ParisiMeasure) :
    ContinuousOn (closedJet 1 2 (firstVariation Ξ μ)) (Icc (0:ℝ) 1) := by
  change ContinuousOn (derivWithin (derivWithin (firstVariation Ξ μ) (Icc (0:ℝ) 1))
    (Icc (0:ℝ) 1)) (Icc (0:ℝ) 1)
  exact ((contDiffOn_firstVariation_two Ξ μ).derivWithin
    (uniqueDiffOn_Icc (by norm_num)) (m:=1) (by norm_num)).continuousOn_derivWithin
      (uniqueDiffOn_Icc (by norm_num)) (by norm_num)

theorem closedJet_two_eq_deriv_of_mem_Ioo {bar q : ℝ} (f : ℝ→ℝ)
    (hq : q∈Ioo (0:ℝ) bar) : closedJet bar 2 f q=deriv (deriv f) q := by
  change derivWithin (derivWithin f (Icc (0:ℝ) bar)) (Icc (0:ℝ) bar) q=deriv (deriv f) q
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds hq.1 hq.2)]
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [isOpen_Ioo.mem_nhds hq] with y hy
  exact derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)

theorem contDiffAt_firstVariation_two (Ξ : RevisedCovariance) (μ : ParisiMeasure)
    {q : ℝ} (hq : q∈Ioo (0:ℝ) 1) :
    ContDiffAt ℝ 2 (firstVariation Ξ μ) q :=
  (contDiffOn_firstVariation_two Ξ μ).contDiffAt (Icc_mem_nhds hq.1 hq.2)

theorem firstVariation_supporting_plane (Ξ : RevisedCovariance) (μ ν : ParisiMeasure) :
    -((∫q : Overlap,firstVariation Ξ μ q ∂(ν : Measure Overlap))-
      (∫q : Overlap,firstVariation Ξ μ q ∂(μ : Measure Overlap))) ≤
      parisiFunctional Ξ ν-parisiFunctional Ξ μ := by
  have hc := FourPapersCommon.convexOn_mixedFunctional_mix Ξ.toEvenMixture 0 μ ν
  have hd := hasDerivWithinAt_parisiFunctional_mix Ξ μ ν
  have hb := hc.le_slope_of_hasDerivWithinAt_Ioi
    (by norm_num : (0:ℝ)∈Icc (0:ℝ) 1) (by norm_num : (1:ℝ)∈Icc (0:ℝ) 1)
    (by norm_num : (0:ℝ)<1) hd
  simpa only [slope_def_field,Paper.parisiMix_zero,Paper.parisiMix_one,
    sub_zero,div_one,parisiFunctional] using hb

theorem firstVariation_supporting_planes (Ξ : RevisedCovariance) (μ ν : ParisiMeasure) :
    -((∫q : Overlap,firstVariation Ξ μ q ∂(ν : Measure Overlap))-
      (∫q : Overlap,firstVariation Ξ μ q ∂(μ : Measure Overlap))) ≤
        parisiFunctional Ξ ν-parisiFunctional Ξ μ ∧
    parisiFunctional Ξ ν-parisiFunctional Ξ μ ≤
      -((∫q : Overlap,firstVariation Ξ ν q ∂(ν : Measure Overlap))-
        (∫q : Overlap,firstVariation Ξ ν q ∂(μ : Measure Overlap))) := by
  refine ⟨firstVariation_supporting_plane Ξ μ ν,?_⟩
  have hh := firstVariation_supporting_plane Ξ ν μ
  linarith

end DepthPaper.RevisedCovariance
