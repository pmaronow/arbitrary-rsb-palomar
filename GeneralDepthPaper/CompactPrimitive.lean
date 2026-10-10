module

public import GeneralDepthPaper.TruncatedRecursionContinuity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section


/-! The actual indefinite integral is a bounded linear operator on continuous
functions on a compact time interval. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace GeneralDepthPaper
set_option maxHeartbeats 800000

def compactPrimitive {T : ℝ} (hT : 0 ≤ T) (f : C(TruncatedClockDomain T,ℝ)) :
    C(TruncatedClockDomain T,ℝ) where
  toFun q := ∫s in (0:ℝ)..(q:ℝ),f (projIcc 0 T hT s)
  continuous_toFun := by
    have hc : Continuous (fun s => f (projIcc 0 T hT s)) := f.continuous.comp continuous_projIcc
    have hp : Continuous (fun q => ∫s in (0:ℝ)..q,f (projIcc 0 T hT s)) :=
      continuous_iff_continuousAt.mpr fun q =>
        (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 q)
          hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).continuousAt
    exact hp.comp continuous_subtype_val

def compactPrimitiveCLM {T : ℝ} (hT : 0 ≤ T) :
    C(TruncatedClockDomain T,ℝ) →L[ℝ] C(TruncatedClockDomain T,ℝ) :=
  LinearMap.mkContinuous
    { toFun := compactPrimitive hT
      map_add' := fun f g => by
        ext q
        change (∫s in 0..(q:ℝ),(f+g) (projIcc 0 T hT s)) =
          (∫s in 0..(q:ℝ),f (projIcc 0 T hT s))+(∫s in 0..(q:ℝ),g (projIcc 0 T hT s))
        simp only [ContinuousMap.add_apply]
        exact intervalIntegral.integral_add
          ((f.continuous.comp continuous_projIcc).intervalIntegrable 0 q)
          ((g.continuous.comp continuous_projIcc).intervalIntegrable 0 q)
      map_smul' := fun c f => by
        ext q
        exact intervalIntegral.integral_smul c _ }
    T (fun f => by
      apply (ContinuousMap.norm_le _ (mul_nonneg hT (norm_nonneg _))).mpr
      intro q
      have he := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := 0) (b := (q:ℝ)) (fun s _ => f.norm_coe_le_norm (projIcc 0 T hT s))
      simp only [sub_zero,abs_of_nonneg q.property.1] at he
      exact he.trans (by nlinarith only [q.property.2,norm_nonneg f]))

@[simp] theorem compactPrimitiveCLM_apply {T : ℝ} (hT : 0 ≤ T)
    (f : C(TruncatedClockDomain T,ℝ)) (q : TruncatedClockDomain T) :
    compactPrimitiveCLM hT f q = ∫s in 0..(q:ℝ),f (projIcc 0 T hT s) := rfl

end GeneralDepthPaper
