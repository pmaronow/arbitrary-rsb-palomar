module

public import DepthPaper.MassInterpolation
public import DepthPaper.OpenSmoothIntegral
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section


/-! Smooth parameter averaging over the affine mass segment. The local
dominating constants are derived from compactness in the actual finite
parameter space, rather than imposed as new analytic assumptions. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 64

def unitMassClamp (t : ℝ) : ℝ := projIcc 0 1 zero_le_one t

theorem continuous_unitMassClamp : Continuous unitMassClamp :=
  continuous_subtype_val.comp continuous_projIcc

theorem unitMassClamp_mem (t : ℝ) : unitMassClamp t∈Icc (0:ℝ) 1 :=
  (projIcc 0 1 zero_le_one t).property

theorem unitMassClamp_eq {t : ℝ} (ht : t∈Icc (0:ℝ) 1) : unitMassClamp t=t := by
  simp [unitMassClamp,projIcc_of_mem zero_le_one ht]

theorem continuousOn_massClampedJet {r : ℕ} {f : CutoffInputParameter r→ℝ}
    {U : Set (CutoffInputParameter r)} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hp : ∀t∈Icc (0:ℝ) 1,MapsTo (massInterpolation t) U U) (j : ℕ) :
    ContinuousOn (fun p : ℝ×CutoffInputParameter r=> iteratedFDeriv ℝ j (fun y=> f (massInterpolation (unitMassClamp p.1) y)) p.2)
      {p | p.2∈U} := by
  have hj : ContinuousOn (iteratedFDeriv ℝ j f) U := by
    intro x hx
    exact (((hf x hx).contDiffAt (hU.mem_nhds hx)).iteratedFDeriv_right
      (m:=0) (by simp)).continuousAt.continuousWithinAt
  have hi : Continuous (fun p : ℝ×CutoffInputParameter r=> massInterpolation (unitMassClamp p.1) p.2) :=
    contDiff_massInterpolation.continuous.comp
      ((continuous_unitMassClamp.comp continuous_fst).prodMk continuous_snd)
  have hraw := hj.comp hi.continuousOn
    (fun p hx=> hp _ (unitMassClamp_mem _) hx)
  let C := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
    (fun _ : Fin j=> CutoffInputParameter r) (fun _ : Fin j=> CutoffInputParameter r) ℝ
  have hL : Continuous (fun p : ℝ×CutoffInputParameter r=> C (fun _=> massInterpolationLinear (unitMassClamp p.1))) :=
    C.cont.comp (continuous_pi fun _=> continuous_massInterpolationLinear.comp (continuous_unitMassClamp.comp continuous_fst))
  apply (hL.continuousOn.clm_apply hraw).congr
  intro p hx
  dsimp only [Function.comp_apply]
  rw [iteratedFDeriv_comp_massInterpolation (unitMassClamp p.1)
    ((hf _ (hp _ (unitMassClamp_mem _) hx)).contDiffAt
      (hU.mem_nhds (hp _ (unitMassClamp_mem _) hx))) j]
  simp only [C,ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear_apply_apply]

theorem massAverage_integral_conditions {r : ℕ} {f : CutoffInputParameter r→ℝ}
    {U : Set (CutoffInputParameter r)} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hp : ∀t∈Icc (0:ℝ) 1,MapsTo (massInterpolation t) U U) :
    (∀t,ContDiffOn ℝ ∞ (fun x=> f (massInterpolation (unitMassClamp t) x)) U) ∧
    (∀j,∀x∈U,AEStronglyMeasurable
      (fun t=> iteratedFDeriv ℝ j (fun y=> f (massInterpolation (unitMassClamp t) y)) x)
      (volume.restrict (Ioc (0:ℝ) 1))) ∧
    (∀x∈U,∃s∈𝓝 x,s⊆U ∧ ∃B:ℕ→ℝ→ℝ,
      (∀j,Integrable (B j) (volume.restrict (Ioc (0:ℝ) 1))) ∧
      ∀j,∀y∈s,∀t,‖iteratedFDeriv ℝ j
        (fun u=> f (massInterpolation (unitMassClamp t) u)) y‖ ≤ B j t) := by
  refine ⟨fun t=> hf.comp
    ((contDiff_massInterpolation.comp (contDiff_const.prodMk contDiff_id)).contDiffOn)
      (hp _ (unitMassClamp_mem _)),?_,?_⟩
  · intro j x hx
    have hc : Continuous (fun t=> iteratedFDeriv ℝ j
        (fun y=> f (massInterpolation (unitMassClamp t) y)) x) := by
      apply continuousOn_univ.mp
      exact (continuousOn_massClampedJet hU hf hp j).comp
        (continuous_id.prodMk continuous_const).continuousOn (fun _ _=> hx)
    exact hc.aestronglyMeasurable
  · intro x hx
    obtain ⟨e,he,hes⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
    have hsub : Metric.closedBall x (e/2)⊆U := by
      intro y hy
      apply hes
      exact (Metric.mem_closedBall.mp hy).trans_lt (by linarith)
    let K := Icc (0:ℝ) 1 ×ˢ Metric.closedBall x (e/2)
    have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
    have hmap : MapsTo (fun p : ℝ×CutoffInputParameter r=> massInterpolation p.1 p.2) K U :=
      fun p h=> hp _ h.1 (hsub h.2)
    have hj : ∀j,ContinuousOn (fun p : ℝ×CutoffInputParameter r=> iteratedFDeriv ℝ j f (massInterpolation p.1 p.2)) K := by
      intro j
      have hc : ContinuousOn (iteratedFDeriv ℝ j f) U := by
        intro y hy
        exact (((hf y hy).contDiffAt (hU.mem_nhds hy)).iteratedFDeriv_right
          (m:=0) (by simp)).continuousAt.continuousWithinAt
      exact hc.comp contDiff_massInterpolation.continuous.continuousOn hmap
    choose C hC using fun j=> hK.exists_bound_of_continuousOn (hj j)
    refine ⟨Metric.closedBall x (e/2),Metric.closedBall_mem_nhds _ (by linarith),hsub,
      fun j _=> C j,fun _=> integrable_const _,?_⟩
    intro j y hy t
    exact (norm_iteratedFDeriv_comp_massInterpolation_le (unitMassClamp_mem t)
      ((hf _ (hp _ (unitMassClamp_mem t) (hsub hy))).contDiffAt
        (hU.mem_nhds (hp _ (unitMassClamp_mem t) (hsub hy)))) j).trans
      (hC j (unitMassClamp t,y) ⟨unitMassClamp_mem t,hy⟩)

def massAverage {r : ℕ} (f : CutoffInputParameter r→ℝ) (x : CutoffInputParameter r) : ℝ :=
  ∫t in Ioc (0:ℝ) 1,f (massInterpolation (unitMassClamp t) x)

theorem contDiffOn_massAverage {r : ℕ} {f : CutoffInputParameter r→ℝ}
    {U : Set (CutoffInputParameter r)} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hp : ∀t∈Icc (0:ℝ) 1,MapsTo (massInterpolation t) U U) :
    ContDiffOn ℝ ∞ (massAverage f) U := by
  obtain ⟨hd,hm,hb⟩ := massAverage_integral_conditions hU hf hp
  rw [contDiffOn_infty]
  intro N
  apply contDiffOn_integral_of_dominated_derivatives N _ hU _ (fun t=> (hd t).of_le (by simp))
    (fun j _ x hx=> hm j x hx)
  intro x hx
  obtain ⟨s,hs,hsub,B,hBi,hB⟩ := hb x hx
  exact ⟨s,hs,hsub,B,fun j _=> hBi j,fun j _=> hB j⟩

theorem iteratedFDeriv_massAverage {r : ℕ} {f : CutoffInputParameter r→ℝ}
    {U : Set (CutoffInputParameter r)} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hp : ∀t∈Icc (0:ℝ) 1,MapsTo (massInterpolation t) U U)
    (j : ℕ) {x : CutoffInputParameter r} (hx : x∈U) :
    iteratedFDeriv ℝ j (massAverage f) x=
      ∫t in Ioc (0:ℝ) 1,
        iteratedFDeriv ℝ j (fun y=> f (massInterpolation (unitMassClamp t) y)) x := by
  obtain ⟨hd,hm,hb⟩ := massAverage_integral_conditions hU hf hp
  apply iteratedFDeriv_integral_on_open_domain j _ hU _ (fun t=> (hd t).of_le (by simp))
    (fun i _ y hy=> hm i y hy) _ j le_rfl hx
  intro y hy
  obtain ⟨s,hs,hsub,B,hBi,hB⟩ := hb y hy
  exact ⟨s,hs,hsub,B,fun i _=> hBi i,fun i _=> hB i⟩

theorem massAverage_eq_intervalIntegral {r : ℕ} (f : CutoffInputParameter r→ℝ)
    (x : CutoffInputParameter r) :
    massAverage f x=∫t in (0:ℝ)..1,f (massInterpolation t x) := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [unitMassClamp_eq ⟨ht.1.le,ht.2⟩]

theorem norm_iteratedFDeriv_massAverage_le {r : ℕ} {f : CutoffInputParameter r→ℝ}
    {U : Set (CutoffInputParameter r)} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hp : ∀t∈Icc (0:ℝ) 1,MapsTo (massInterpolation t) U U)
    (j : ℕ) {x : CutoffInputParameter r} (hx : x∈U) {B : ℝ}
    (hb : ∀t∈Icc (0:ℝ) 1,‖iteratedFDeriv ℝ j f (massInterpolation t x)‖ ≤ B) :
    ‖iteratedFDeriv ℝ j (massAverage f) x‖ ≤ B := by
  rw [iteratedFDeriv_massAverage hU hf hp j hx]
  have h := norm_integral_le_of_norm_le_const (μ:=volume.restrict (Ioc (0:ℝ) 1))
    (Eventually.of_forall fun t=> (norm_iteratedFDeriv_comp_massInterpolation_le (unitMassClamp_mem t)
        ((hf _ (hp _ (unitMassClamp_mem t) hx)).contDiffAt
          (hU.mem_nhds (hp _ (unitMassClamp_mem t) hx))) j).trans
        (hb _ (unitMassClamp_mem t)))
  simpa using h

end DepthPaper
