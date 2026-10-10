module

public import GeneralDepthPaper.Curvature
public import GeneralDepthPaper.ContactPerturbation

@[expose] public section


/-! Closed-interval C² regularity of the genuine first variation. Endpoint
derivatives are intrinsic to [0,1], without choosing a differentiable state
extension past the terminal overlap. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 400000

def firstVariationDerivative (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) (q : ℝ) : ℝ :=
  (1/2:ℝ)*Ξ.second q*(Gamma Ξ μ q-q)

theorem contDiff_covariance_second (Ξ : AdmissibleCovariance) :
    ContDiff ℝ ∞ Ξ.second := by
  unfold AdmissibleCovariance.second
  fun_prop

theorem contDiffOn_firstVariationDerivative (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) :
    ContDiffOn ℝ 1 (firstVariationDerivative Ξ μ) (Icc (0:ℝ) 1) :=
  ((contDiffOn_const.mul ((contDiff_covariance_second Ξ).of_le (by norm_num)).contDiffOn).mul
    ((contDiffOn_Gamma_one Ξ μ).sub contDiffOn_id))

theorem hasDerivWithinAt_firstVariation (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
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

theorem derivWithin_firstVariation (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    derivWithin (firstVariation Ξ μ) (Icc (0:ℝ) 1) q=firstVariationDerivative Ξ μ q :=
  (hasDerivWithinAt_firstVariation Ξ μ hq).derivWithin
    (uniqueDiffOn_Icc (by norm_num) q hq)

/-- The first variation really is C² on the manuscript's entire overlap
interval, including the terminal endpoint and every cumulative-mass atom. -/
theorem contDiffOn_firstVariation_two (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) :
    ContDiffOn ℝ 2 (firstVariation Ξ μ) (Icc (0:ℝ) 1) := by
  rw [show (2:ℕ∞ω)=1+1 by norm_num,contDiffOn_succ_iff_derivWithin
    (uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1))]
  refine ⟨fun q hq=>(hasDerivWithinAt_firstVariation Ξ μ hq).differentiableWithinAt,
    by simp,?_⟩
  exact (contDiffOn_firstVariationDerivative Ξ μ).congr
    (fun q hq=>derivWithin_firstVariation Ξ μ hq)

theorem continuousOn_closed_firstVariation_second (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) :
    ContinuousOn (closedJet 1 2 (firstVariation Ξ μ)) (Icc (0:ℝ) 1) := by
  change ContinuousOn (derivWithin (derivWithin (firstVariation Ξ μ) (Icc (0:ℝ) 1))
    (Icc (0:ℝ) 1)) (Icc (0:ℝ) 1)
  exact ((contDiffOn_firstVariation_two Ξ μ).derivWithin
    (uniqueDiffOn_Icc (by norm_num)) (m:=1) (by norm_num)).continuousOn_derivWithin
      (uniqueDiffOn_Icc (by norm_num)) (by norm_num)

end GeneralDepthPaper
