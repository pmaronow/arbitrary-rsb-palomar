module

public import DepthPaper.TruncatedCoefficient
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

@[expose] public section


/-! Finite-grid coefficients converge in time L¹ and L² even though their
values at moving atoms need not converge pointwise. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace DepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem norm_truncatedCoefficient_le_one {L : ℕ} {qc : ℝ}
    (p : TruncatedRecursionParameter L qc) (hn : Monotone p.2.1)
    (ha : ∀i,p.2.2.1 i ∈ Icc (0:ℝ) 1) (t : ℝ) : ‖truncatedCoefficient p t‖ ≤ 1 := by
  have h := truncatedCoefficient_mem_Icc p hn ha t
  rw [Real.norm_of_nonneg h.1]
  exact h.2

theorem tendsto_truncatedCoefficient_L1 {L : ℕ} {qc : ℝ}
    (p : ℕ → TruncatedRecursionParameter L qc) (p0 : TruncatedRecursionParameter L qc)
    (hp : Tendsto p atTop (𝓝 p0)) (hn : ∀n,Monotone (p n).2.1) (hn0 : Monotone p0.2.1)
    (ha : ∀n i,(p n).2.2.1 i ∈ Icc (0:ℝ) 1) (ha0 : ∀i,p0.2.2.1 i ∈ Icc (0:ℝ) 1) :
    Tendsto (fun n => ∫t in Icc (0:ℝ) qc,‖truncatedCoefficient (p n) t-truncatedCoefficient p0 t‖)
      atTop (𝓝 0) := by
  have hpoint : ∀ᵐ t ∂volume.restrict (Icc (0:ℝ) qc),∀j : Fin (L+1),t ≠ (p0.2.1 j : ℝ) :=
    ae_all_iff.mpr fun j => (volume.restrict (Icc (0:ℝ) qc)).ae_ne (p0.2.1 j : ℝ)
  have h := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Icc (0:ℝ) qc)) (F := fun n t =>
      ‖truncatedCoefficient (p n) t-truncatedCoefficient p0 t‖) (f := fun _ => (0:ℝ))
    (fun _ => (2:ℝ))
    (fun n => ((measurable_truncatedCoefficient (p n)).sub (measurable_truncatedCoefficient p0)).norm.aestronglyMeasurable)
    (integrableOn_const isCompact_Icc.measure_ne_top)
    (fun n => .of_forall fun t => by
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact (norm_sub_le _ _).trans (by
        have h1 := norm_truncatedCoefficient_le_one (p n) (hn n) (ha n) t
        have h2 := norm_truncatedCoefficient_le_one p0 hn0 ha0 t
        linarith)) ?_
  · simpa only [integral_zero] using h
  · filter_upwards [hpoint] with t ht
    simpa only [sub_self,norm_zero] using
      ((tendsto_truncatedCoefficient_at_nonnode p p0 hp t ht).sub
        (tendsto_const_nhds (x := truncatedCoefficient p0 t))).norm

theorem tendsto_truncatedCoefficient_L2 {L : ℕ} {qc : ℝ}
    (p : ℕ → TruncatedRecursionParameter L qc) (p0 : TruncatedRecursionParameter L qc)
    (hp : Tendsto p atTop (𝓝 p0)) (hn : ∀n,Monotone (p n).2.1) (hn0 : Monotone p0.2.1)
    (ha : ∀n i,(p n).2.2.1 i ∈ Icc (0:ℝ) 1) (ha0 : ∀i,p0.2.2.1 i ∈ Icc (0:ℝ) 1) :
    Tendsto (fun n => ∫t in Icc (0:ℝ) qc,‖truncatedCoefficient (p n) t-truncatedCoefficient p0 t‖^2)
      atTop (𝓝 0) := by
  have hpoint : ∀ᵐ t ∂volume.restrict (Icc (0:ℝ) qc),∀j : Fin (L+1),t ≠ (p0.2.1 j : ℝ) :=
    ae_all_iff.mpr fun j => (volume.restrict (Icc (0:ℝ) qc)).ae_ne (p0.2.1 j : ℝ)
  have h := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Icc (0:ℝ) qc)) (F := fun n t =>
      ‖truncatedCoefficient (p n) t-truncatedCoefficient p0 t‖^2) (f := fun _ => (0:ℝ))
    (fun _ => (4:ℝ))
    (fun n => (((measurable_truncatedCoefficient (p n)).sub
      (measurable_truncatedCoefficient p0)).norm.pow_const 2).aestronglyMeasurable)
    (integrableOn_const isCompact_Icc.measure_ne_top)
    (fun n => .of_forall fun t => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have h1 := norm_truncatedCoefficient_le_one (p n) (hn n) (ha n) t
      have h2 := norm_truncatedCoefficient_le_one p0 hn0 ha0 t
      have hd := norm_sub_le (truncatedCoefficient (p n) t) (truncatedCoefficient p0 t)
      have hnon := norm_nonneg (truncatedCoefficient (p n) t-truncatedCoefficient p0 t)
      nlinarith) ?_
  · simpa only [integral_zero] using h
  · filter_upwards [hpoint] with t ht
    simpa only [sub_self,norm_zero,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true] using
      (((tendsto_truncatedCoefficient_at_nonnode p p0 hp t ht).sub
        (tendsto_const_nhds (x := truncatedCoefficient p0 t))).norm.pow 2)

end DepthPaper
