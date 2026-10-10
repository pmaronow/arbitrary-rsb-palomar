module

public import Paper.CanonicalBrownian
public import Mathlib.Probability.Process.Adapted

@[expose] public section


/-! Genuine Brownian clock rescaling as equality of probability laws of
continuous paths. The sign of a nonzero scale is included. The deterministic
clock needs only continuity; monotonicity is unnecessary for this law identity. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace FourPapersCommon

def rescaledCanonicalBrownian (β : ℝ) (t : ℝ≥0) (sample : Paper.BrownianSample) : ℝ :=
  β*Paper.canonicalBrownian (t/(β^2).toNNReal) sample

theorem measurable_rescaledCanonicalBrownian (β : ℝ) (t : ℝ≥0) :
    Measurable (rescaledCanonicalBrownian β t) :=
  (Paper.measurable_canonicalBrownian _).const_mul β

theorem continuous_rescaledCanonicalBrownian (β : ℝ) (sample : Paper.BrownianSample) :
    Continuous (fun t => rescaledCanonicalBrownian β t sample) :=
  ((Paper.continuous_canonicalBrownian sample).comp
    (continuous_id.div_const _)).const_mul β

theorem isBrownianReal_rescaledCanonicalBrownian (β : ℝ) (hβ : β ≠ 0) :
    IsBrownianReal (rescaledCanonicalBrownian β) Paper.canonicalBrownianMeasure := by
  let c : ℝ≥0 := ((β^2).toNNReal)⁻¹
  have hb2 : 0 < β^2 := sq_pos_of_ne_zero hβ
  have hc : c ≠ 0 := inv_ne_zero (by
    exact (Real.toNNReal_pos.mpr hb2).ne')
  have hs : (Real.sqrt (c : ℝ))⁻¹ = |β| := by
    simp only [c,NNReal.coe_inv,Real.coe_toNNReal _ hb2.le,Real.sqrt_inv,
      Real.sqrt_sq_eq_abs,inv_inv]
  have h := Paper.isBrownianReal_canonicalBrownian.smul hc
  have hAbs : IsBrownianReal (fun t sample =>
      |β| * Paper.canonicalBrownian (t/(β^2).toNNReal) sample)
      Paper.canonicalBrownianMeasure := by
    convert h using 1
    funext t sample
    rw [hs]
    congr 1
    simp only [c,div_eq_mul_inv,mul_comm]
  by_cases hb : 0 ≤ β
  · change IsBrownianReal (fun t sample => β*Paper.canonicalBrownian (t/(β^2).toNNReal) sample) _
    simpa only [abs_of_nonneg hb] using hAbs
  · convert hAbs.neg using 1
    funext t sample
    simp only [rescaledCanonicalBrownian,Pi.neg_apply,abs_of_neg (lt_of_not_ge hb),
      neg_mul,neg_neg]

theorem rescaledCanonicalBrownian_fullLaw (β : ℝ) (hβ : β ≠ 0) :
    Paper.canonicalBrownianMeasure.map (fun sample => fun t => rescaledCanonicalBrownian β t sample) =
      Paper.canonicalBrownianMeasure.map (fun sample => fun t => Paper.canonicalBrownian t sample) := by
  have hs := (isBrownianReal_rescaledCanonicalBrownian β hβ).toIsPreBrownianReal.hasLaw_gaussianLimit
    (Measurable.of_eval (measurable_rescaledCanonicalBrownian β)).aemeasurable
  have hb := Paper.isBrownianReal_canonicalBrownian.toIsPreBrownianReal.hasLaw_gaussianLimit
    (Measurable.of_eval Paper.measurable_canonicalBrownian).aemeasurable
  exact hs.map_eq.trans hb.map_eq.symm

variable {K : Type*} [TopologicalSpace K] [SecondCountableTopology K] [LocallyCompactSpace K]

def clockBrownianPath (A : C(K,ℝ≥0)) (sample : Paper.BrownianSample) : C(K,ℝ) where
  toFun q := Paper.canonicalBrownian (A q) sample
  continuous_toFun := (Paper.continuous_canonicalBrownian sample).comp A.continuous

def rescaledClockBrownianPath (β : ℝ) (A : C(K,ℝ≥0))
    (sample : Paper.BrownianSample) : C(K,ℝ) where
  toFun q := β*Paper.canonicalBrownian (A q/(β^2).toNNReal) sample
  continuous_toFun := (continuous_rescaledCanonicalBrownian β sample).comp A.continuous

theorem measurable_clockBrownianPath (A : C(K,ℝ≥0)) : Measurable (clockBrownianPath A) := by
  rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
  intro q
  exact Paper.measurable_canonicalBrownian _

theorem measurable_rescaledClockBrownianPath (β : ℝ) (A : C(K,ℝ≥0)) :
    Measurable (rescaledClockBrownianPath β A) := by
  rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
  intro q
  exact measurable_rescaledCanonicalBrownian β _

theorem measurable_continuousRealPath_coe :
    Measurable (fun path : C(K,ℝ) => fun q : K => path q) := by
  exact Measurable.of_eval fun q =>
    (ProbabilityTheory.ContinuousMap.measurable_iff_eval
      (fun path : C(K,ℝ) => path)).mp measurable_id q

theorem continuousRealPathMeasure_ext (P Q : Measure C(K,ℝ))
    (h : P.map (fun path => fun q : K => path q) = Q.map (fun path => fun q : K => path q)) :
    P = Q := by
  have hm : (inferInstance : MeasurableSpace C(K,ℝ)) =
      MeasurableSpace.pi.comap (fun path : C(K,ℝ) => fun q : K => path q) := by
    calc
      _ = ⨆ q : K, (inferInstance : MeasurableSpace ℝ).comap
        (fun path : C(K,ℝ) => path q) :=
          ProbabilityTheory.ContinuousMap.measurableSpace_eq_iSup_comap_eval
      _ = _ := by simp only [MeasurableSpace.pi,MeasurableSpace.comap_iSup,
        MeasurableSpace.comap_comp,Function.comp_def]
  apply Measure.ext
  intro S hS
  change @MeasurableSet C(K,ℝ) (inferInstance : MeasurableSpace C(K,ℝ)) S at hS
  rw [hm] at hS
  rcases hS with ⟨T,hT,rfl⟩
  rw [← Measure.map_apply measurable_continuousRealPath_coe hT,h,
    Measure.map_apply measurable_continuousRealPath_coe hT]

theorem clockBrownianPath_rescaling_law (β : ℝ) (hβ : β ≠ 0) (A : C(K,ℝ≥0)) :
    Paper.canonicalBrownianMeasure.map (clockBrownianPath A) =
      Paper.canonicalBrownianMeasure.map (rescaledClockBrownianPath β A) := by
  let restrict : (ℝ≥0 → ℝ) → (K → ℝ) := fun f q => f (A q)
  have hr : Measurable restrict := Measurable.of_eval fun q => measurable_pi_apply _
  have h := congrArg (fun P => P.map restrict) (rescaledCanonicalBrownian_fullLaw β hβ)
  rw [Measure.map_map hr (Measurable.of_eval (measurable_rescaledCanonicalBrownian β)),
    Measure.map_map hr (Measurable.of_eval Paper.measurable_canonicalBrownian)] at h
  apply continuousRealPathMeasure_ext
  rw [Measure.map_map measurable_continuousRealPath_coe (measurable_clockBrownianPath A),
    Measure.map_map measurable_continuousRealPath_coe (measurable_rescaledClockBrownianPath β A)]
  exact h.symm

end FourPapersCommon
