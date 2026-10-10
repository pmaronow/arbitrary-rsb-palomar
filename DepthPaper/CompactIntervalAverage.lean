module

public import DepthPaper.UnitTiltAverage
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section


/-! Compact-interval averaging is continuous for Banach parameters. The
parameter space need not be locally compact, which is essential for terminal
functions in the manuscript's infinite-dimensional Banach space. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace DepthPaper
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
set_option maxSynthPendingDepth 64

theorem integrable_unitInterval_extension (F : C(UnitTilt,E)) :
    Integrable (fun t : ℝ => F (projIcc 0 1 zero_le_one t)) unitTiltMeasure := by
  apply (integrable_const ‖F‖).mono'
  · exact (F.continuous.comp continuous_projIcc).aestronglyMeasurable
  · exact .of_forall fun t => F.norm_coe_le_norm _

def unitIntervalIntegralCLM : C(UnitTilt,E) →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := fun F => ∫t,F (projIcc 0 1 zero_le_one t) ∂unitTiltMeasure
      map_add' := fun F G => integral_add (integrable_unitInterval_extension F)
        (integrable_unitInterval_extension G)
      map_smul' := fun c F => integral_smul c (fun t => F (projIcc 0 1 zero_le_one t)) }
    1 (fun F => by
      simpa using norm_integral_le_of_norm_le_const
        (μ := unitTiltMeasure) (.of_forall fun t => F.norm_coe_le_norm (projIcc 0 1 zero_le_one t)))

theorem unitIntervalIntegralCLM_apply (F : C(UnitTilt,E)) :
    unitIntervalIntegralCLM F = ∫t in (0:ℝ)..1,F (projIcc 0 1 zero_le_one t) := by
  change (∫t,F (projIcc 0 1 zero_le_one t) ∂volume.restrict (Icc 0 1)) = _
  rw [intervalIntegral.integral_of_le zero_le_one]
  exact setIntegral_congr_set Ioc_ae_eq_Icc.symm

theorem continuous_unitIntervalIntegral {P : Type*} [TopologicalSpace P]
    (F : P × UnitTilt → E) (hF : Continuous F) :
    Continuous (fun p : P => ∫t in (0:ℝ)..1,F (p,projIcc 0 1 zero_le_one t)) := by
  let H : P → C(UnitTilt,E) := fun p =>
    ⟨fun t => F (p,t),hF.comp (continuous_const.prodMk continuous_id)⟩
  have hH : Continuous H := ContinuousMap.continuous_of_continuous_uncurry H hF
  have he : (fun p => unitIntervalIntegralCLM (H p)) =
      fun p : P => ∫t in (0:ℝ)..1,F (p,projIcc 0 1 zero_le_one t) := by
    funext p
    exact unitIntervalIntegralCLM_apply (H p)
  rw [←he]
  exact unitIntervalIntegralCLM.continuous.comp hH

end DepthPaper
