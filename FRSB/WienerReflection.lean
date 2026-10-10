module

public import Paper.CanonicalBrownian
public import Paper.RSFunctional

@[expose] public section


/-! Reflection symmetry of the constructed continuous Wiener path law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
open scoped NNReal
namespace FRSB

theorem measurable_continuousPath_coe :
    Measurable (fun path : C(Overlap, ℝ) => fun t : Overlap => path t) := by
  exact measurable_pi_lambda fun t =>
    (ProbabilityTheory.ContinuousMap.measurable_iff_eval
      (fun path : C(Overlap, ℝ) => path)).mp measurable_id t

theorem continuousPathMeasure_ext (P Q : Measure C(Overlap, ℝ))
    (h : P.map (fun path => fun t : Overlap => path t) =
      Q.map (fun path => fun t : Overlap => path t)) : P = Q := by
  have hm : (inferInstance : MeasurableSpace C(Overlap, ℝ)) =
      MeasurableSpace.pi.comap (fun path : C(Overlap, ℝ) => fun t : Overlap => path t) := by
    calc
      _ = ⨆ t : Overlap, (inferInstance : MeasurableSpace ℝ).comap
        (fun path : C(Overlap, ℝ) => path t) :=
          ProbabilityTheory.ContinuousMap.measurableSpace_eq_iSup_comap_eval
      _ = _ := by simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
        MeasurableSpace.comap_comp, Function.comp_def]
  apply Measure.ext
  intro S hS
  change @MeasurableSet C(Overlap, ℝ) (inferInstance : MeasurableSpace C(Overlap, ℝ)) S at hS
  rw [hm] at hS
  rcases hS with ⟨T, hT, rfl⟩
  rw [← Measure.map_apply measurable_continuousPath_coe hT, h,
    Measure.map_apply measurable_continuousPath_coe hT]

theorem canonicalWienerMeasure_reflection :
    canonicalWienerMeasure.map (fun path : C(Overlap, ℝ) => -path) =
      canonicalWienerMeasure := by
  have hB := isBrownianReal_canonicalBrownian.toIsPreBrownianReal.hasLaw_gaussianLimit
    (measurable_pi_lambda measurable_canonicalBrownian).aemeasurable
  have hneg := isBrownianReal_canonicalBrownian.toIsPreBrownianReal.neg.hasLaw_gaussianLimit
    (measurable_pi_lambda fun t => (measurable_canonicalBrownian t).neg).aemeasurable
  have hfull : canonicalBrownianMeasure.map (fun sample => fun t : ℝ≥0 =>
      -canonicalBrownian t sample) =
      canonicalBrownianMeasure.map (fun sample => fun t : ℝ≥0 => canonicalBrownian t sample) :=
    hneg.map_eq.trans hB.map_eq.symm
  let restrict : (ℝ≥0 → ℝ) → (Overlap → ℝ) := fun f t => f t.1.toNNReal
  have hrestrict : Measurable restrict := measurable_pi_lambda fun t => measurable_pi_apply _
  have hres := congrArg (fun P => P.map restrict) hfull
  have hnm : Measurable (fun sample : BrownianSample => fun t : ℝ≥0 =>
      -canonicalBrownian t sample) := by
    exact measurable_pi_iff.mpr fun t => (measurable_canonicalBrownian t).neg
  have hpm : Measurable (fun sample : BrownianSample => fun t : ℝ≥0 =>
      canonicalBrownian t sample) := measurable_pi_iff.mpr measurable_canonicalBrownian
  rw [Measure.map_map hrestrict hnm, Measure.map_map hrestrict hpm] at hres
  apply continuousPathMeasure_ext
  rw [Measure.map_map measurable_continuousPath_coe continuous_neg.measurable,
    canonicalWienerMeasure,
    Measure.map_map (measurable_continuousPath_coe.comp continuous_neg.measurable)
      measurable_canonicalBrownianPath,
    Measure.map_map measurable_continuousPath_coe measurable_canonicalBrownianPath]
  exact hres

end FRSB
