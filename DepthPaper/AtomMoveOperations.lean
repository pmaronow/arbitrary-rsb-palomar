module

public import DepthPaper.WeakVariationValueMap

@[expose] public section


/-! Genuine atom-moving probability measures, for arbitrary order parameters.
Only the chosen atom moves; the rest of the measure is preserved exactly. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BoundedContinuousFunction
namespace DepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

def movedOverlap (a : Overlap) (t : ℝ) : Overlap := projIcc 0 1 (by norm_num) ((a:ℝ)+t)

def moveAtomMap (a : Overlap) (t : ℝ) (q : Overlap) : Overlap :=
  @ite Overlap (q=a) (Classical.propDecidable _) (movedOverlap a t) q

def moveAtom (μ : ParisiMeasure) (a : Overlap) (t : ℝ) : ParisiMeasure := μ.map (moveAtomMap a t)

def atomWeight (μ : ParisiMeasure) (a : Overlap) : ℝ := (μ : Measure Overlap).real {a}

theorem atomWeight_nonneg (μ : ParisiMeasure) (a : Overlap) : 0≤atomWeight μ a :=
  measureReal_nonneg

@[simp] theorem movedOverlap_zero (a : Overlap) : movedOverlap a 0=a := by
  simp only [movedOverlap,add_zero,projIcc_of_mem (by norm_num : (0:ℝ)≤1) a.property]

@[simp] theorem moveAtomMap_zero (a q : Overlap) : moveAtomMap a 0 q=q := by
  unfold moveAtomMap
  rw [movedOverlap_zero]
  by_cases hqa : q=a
  · exact @ite_eq_left (q=a) (Classical.propDecidable _) hqa Overlap a q |>.trans hqa.symm
  · exact @ite_eq_right (q=a) (Classical.propDecidable _) hqa Overlap a q

@[simp] theorem moveAtom_zero (μ : ParisiMeasure) (a : Overlap) : moveAtom μ a 0=μ := by
  have he : moveAtomMap a 0=id := by funext q; exact moveAtomMap_zero a q
  unfold moveAtom
  rw [he]
  apply ProbabilityMeasure.toMeasure_injective
  exact Measure.map_id

theorem measurable_moveAtomMap (a : Overlap) (t : ℝ) : Measurable (moveAtomMap a t) := by
  classical
  exact measurable_const.ite (measurableSet_singleton a) measurable_id

theorem continuous_movedOverlap (a : Overlap) : Continuous (movedOverlap a) :=
  continuous_projIcc.comp (continuous_const.add continuous_id)

theorem integral_moveAtom_sub (μ : ParisiMeasure) (a : Overlap) (t : ℝ)
    (f : Overlap→ᵇℝ) :
    (∫q,f q ∂(moveAtom μ a t : Measure Overlap))-(∫q,f q ∂(μ : Measure Overlap))=
      atomWeight μ a*(f (movedOverlap a t)-f a) := by
  classical
  have hm := measurable_moveAtomMap a t
  have hi : Integrable (fun q=>f (moveAtomMap a t q)) (μ : Measure Overlap) :=
    (integrable_const ‖f‖).mono' (f.continuous.measurable.comp hm).aestronglyMeasurable
      (.of_forall fun q=>f.norm_coe_le_norm _)
  rw [moveAtom,ProbabilityMeasure.toMeasure_map,integral_map hm.aemeasurable f.continuous.aestronglyMeasurable,
    ←integral_sub hi (f.integrable (μ : Measure Overlap))]
  have he : (fun q=>f (moveAtomMap a t q)-f q)=
      ({a} : Set Overlap).indicator (fun _=>f (movedOverlap a t)-f a) := by
    funext q
    by_cases hqa : q=a
    · subst q
      have hmap : moveAtomMap a t a=movedOverlap a t :=
        @ite_eq_left (a=a) (Classical.propDecidable _) rfl Overlap _ _
      rw [hmap,indicator_of_mem (mem_singleton a)]
    · have hmap : moveAtomMap a t q=q :=
        @ite_eq_right (q=a) (Classical.propDecidable _) hqa Overlap _ _
      rw [hmap,indicator_of_notMem (show q∉({a}:Set Overlap) by simpa using hqa),sub_self]
  rw [he,integral_indicator (measurableSet_singleton a),integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,atomWeight]

theorem tendsto_moveAtom_zero (μ : ParisiMeasure) (a : Overlap) :
    Tendsto (moveAtom μ a) (𝓝 (0:ℝ)) (𝓝 μ) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have hp := (f.continuous.comp (continuous_movedOverlap a)).continuousAt.tendsto (x:=0)
  have hh := ((hp.sub_const (f a)).const_mul (atomWeight μ a)).add_const
    (∫q,f q ∂(μ : Measure Overlap))
  have he : ∀t,(∫q,f q ∂(moveAtom μ a t : Measure Overlap))=
      atomWeight μ a*(f (movedOverlap a t)-f a)+(∫q,f q ∂(μ : Measure Overlap)) := by
    intro t
    linarith [integral_moveAtom_sub μ a t f]
  simpa only [Function.comp_def,movedOverlap_zero,sub_self,mul_zero,zero_add,←he] using hh

end DepthPaper
