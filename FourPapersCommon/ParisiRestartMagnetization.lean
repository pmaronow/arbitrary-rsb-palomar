module

public import Paper.ParisiHJBValueFunction
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section


/-! The actual restarted magnetization equals the expected terminal tanh.
Differentiation holds the genuine control fixed; its touching HJB objective
then has the same field derivative as the PDE value. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace FourPapersCommon
open Paper
set_option maxHeartbeats 800000

theorem measurable_parisiTimeControlEndpoint (β x : ℝ) (μ : ParisiMeasure)
    (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (A : ℝ → BrownianSample → ℝ) (hA : IsParisiAdmissibleControl A) :
    Measurable (parisiTimeControlEndpoint β x μ a A) := by
  have hs := (measurable_canonicalParisiControlledState β x (parisiRestartMeasure μ a ha.1) A hA).comp
    (f:=fun sample : BrownianSample => ((1-a).toNNReal,sample))
    (measurable_const.prodMk (measurable_id : Measurable (fun sample : BrownianSample => sample)))
  have he : parisiTimeControlEndpoint β x μ a A =
      fun sample => canonicalParisiRestartControlledState β x μ a ha.1 A (1-a).toNNReal sample :=
    funext (parisiTimeControlEndpoint_eq_state β x μ a ha A)
  rw [he]
  exact hs

theorem hasDerivAt_parisiTimeControlObjective_field (β : ℝ) (μ : ParisiMeasure)
    (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (A : ℝ → BrownianSample → ℝ) (hA : IsParisiAdmissibleControl A) (x : ℝ) :
    HasDerivAt (fun y => parisiTimeControlObjective β y μ a A)
      (∫ sample, Real.tanh (parisiTimeControlEndpoint β x μ a A sample)
        ∂canonicalBrownianMeasure) x := by
  let F := fun y sample => Real.log (Real.cosh (parisiTimeControlEndpoint β y μ a A sample))-
    parisiTimeControlCost β μ a A sample
  let D := fun y sample => Real.tanh (parisiTimeControlEndpoint β y μ a A sample)
  have hm (y : ℝ) : Measurable (parisiTimeControlEndpoint β y μ a A) :=
    measurable_parisiTimeControlEndpoint β y μ a ha A hA
  have hi : Integrable (F x) canonicalBrownianMeasure :=
    (integrable_parisiTimeControl_terminal β x μ a ha A hA).sub
      (integrable_parisiTimeControlCost β μ a ha A hA)
  have hFm : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (F y) canonicalBrownianMeasure :=
    .of_forall fun y => ((Real.continuous_cosh.log (fun z => (Real.cosh_pos z).ne')).measurable.comp
      (hm y)).aestronglyMeasurable.sub
        (integrable_parisiTimeControlCost β μ a ha A hA).aestronglyMeasurable
  have hc : Continuous Real.tanh := continuous_iff_continuousAt.mpr
    (fun y => (hasDerivAt_tanh y).continuousAt)
  have hDm : AEStronglyMeasurable (D x) canonicalBrownianMeasure :=
    (hc.measurable.comp (hm x)).aestronglyMeasurable
  have hbound : ∀ᵐ sample ∂canonicalBrownianMeasure, ∀ y ∈ (univ : Set ℝ), ‖D y sample‖ ≤ (1 : ℝ) :=
    .of_forall fun sample y _ => by simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one _).le
  have hdiff : ∀ᵐ sample ∂canonicalBrownianMeasure, ∀ y ∈ (univ : Set ℝ),
      HasDerivAt (fun z => F z sample) (D y sample) y := by
    apply Filter.Eventually.of_forall
    intro sample y _
    have hd : HasDerivAt (fun z => parisiTimeControlEndpoint β z μ a A sample) 1 y :=
      ((hasDerivAt_id y).add_const (β*canonicalBrownian (1-a).toNNReal sample)).add_const _
    simpa only [F,D,mul_one,Function.comp_def] using
      ((hasDerivAt_log_cosh (parisiTimeControlEndpoint β y μ a A sample)).comp y hd).sub_const
        (parisiTimeControlCost β μ a A sample)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F:=F) (F':=D) (bound:=fun _ => (1 : ℝ)) (s:=univ) (by simp)
    hFm hi hDm hbound (integrable_const 1) hdiff).2

theorem parisiGradient_eq_restart_terminal_tanh (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (x : ℝ) :
    parisiGradient β μ (a,x)=
      ∫ sample, Real.tanh (canonicalParisiRestartState β x μ a ha.1 (1-a).toNNReal sample)
        ∂canonicalBrownianMeasure := by
  let A := canonicalParisiRestartControl β x μ a ha.1
  have hA := isParisiAdmissibleControl_canonicalParisiRestartControl β x μ a ha.1
  have hm : IsLocalMin (fun y => parisiPotential β μ (a,y)-parisiTimeControlObjective β y μ a A) x := by
    apply Filter.Eventually.of_forall
    intro y
    have hx := parisiTimeControlObjective_feedback_eq_potential β x hβ μ a ha
    have hy := parisiTimeControlObjective_le_potential β y hβ μ a ha A hA
    change parisiPotential β μ (a,x)-parisiTimeControlObjective β x μ a A ≤ _
    change parisiTimeControlObjective β x μ a A=parisiPotential β μ (a,x) at hx
    linarith
  have hz := hm.hasDerivAt_eq_zero
    ((hasDerivAt_parisiPotential_spatial β hβ μ a x ha).sub
      (hasDerivAt_parisiTimeControlObjective_field β μ a ha A hA x))
  have he := sub_eq_zero.mp hz
  rw [he]
  apply integral_congr_ae
  exact .of_forall fun sample => congrArg Real.tanh
    (parisiTimeControlEndpoint_feedback_eq_restartState β x μ a ha sample)

end FourPapersCommon
