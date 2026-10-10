module

public import Paper.RSFunctional
public import FRSB.MomentBootstrap

@[expose] public section


/-! Right continuity removes the almost-everywhere ambiguity in the
 density quotient, while the left limit at the terminal support point is
 the mass below that point, rather than the CDF value including its atom. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace FRSB

/-- The actual overlap CDF is the usual CDF of the pushforward real law. -/
theorem parisiCDF_eq_real_cdf (μ : Paper.ParisiMeasure) :
    Paper.parisiCDF μ = cdf (μ.map (fun x : Paper.Overlap => (x : ℝ)) :
      ProbabilityMeasure ℝ) := by
  funext s
  rw [cdf_eq_real, measureReal_def, ProbabilityMeasure.map_apply' μ
    continuous_subtype_val.measurable.aemeasurable measurableSet_Iic]
  rfl

theorem parisiCDF_continuousWithinAt_right (μ : Paper.ParisiMeasure) (s : ℝ) :
    ContinuousWithinAt (Paper.parisiCDF μ) (Ici s) s := by
  rw [parisiCDF_eq_real_cdf]
  exact (cdf _).right_continuous s

/-- The actual left endpoint mass is the limit of the CDF from below. -/
theorem tendsto_parisiCDF_left (μ : Paper.ParisiMeasure) (q : ℝ) :
    Tendsto (Paper.parisiCDF μ) (𝓝[<] q)
      (𝓝 (((μ : Measure Paper.Overlap) {x | (x : ℝ) < q}).toReal)) := by
  let ν : ProbabilityMeasure ℝ := μ.map (fun x : Paper.Overlap => (x : ℝ))
  have hl := (cdf (ν : Measure ℝ)).mono.tendsto_leftLim q
  have hn : 0 ≤ Function.leftLim (cdf (ν : Measure ℝ)) q :=
    ge_of_tendsto hl (Filter.Eventually.of_forall (cdf_nonneg (ν : Measure ℝ)))
  have hm : ((ν : Measure ℝ) (Iio q)).toReal = Function.leftLim (cdf (ν : Measure ℝ)) q := by
    calc
      _ = (((cdf (ν : Measure ℝ)).measure) (Iio q)).toReal := by
        rw [measure_cdf]
      _ = _ := by
        rw [StieltjesFunction.measure_Iio _ (tendsto_cdf_atBot (ν : Measure ℝ)),
          sub_zero, ENNReal.toReal_ofReal hn]
  rw [ProbabilityMeasure.map_apply' μ continuous_subtype_val.measurable.aemeasurable
    measurableSet_Iio] at hm
  rw [parisiCDF_eq_real_cdf]
  exact hm ▸ hl

/-- A right-continuous integrand whose every subinterval integral vanishes
 must vanish at every point except possibly the terminal endpoint. -/
theorem eq_zero_of_right_continuous_and_interval_integrals_zero
    (f : ℝ → ℝ) (q : ℝ) (hfm : StronglyMeasurable f)
    (hc : ∀ s ∈ Ico (0 : ℝ) q, ContinuousWithinAt f (Ici s) s)
    (hi : ∀ s t, s ∈ Icc (0 : ℝ) q → t ∈ Icc (0 : ℝ) q → s ≤ t →
      ∫ r in s..t, f r = 0) : ∀ s ∈ Ico (0 : ℝ) q, f s = 0 := by
  intro s hs
  have hmem : s ∈ Icc s q := ⟨le_rfl, hs.2.le⟩
  have : Fact (s ∈ Icc s q) := ⟨hmem⟩
  have hd : HasDerivWithinAt (fun t => ∫ r in s..t, f r) (f s) (Icc s q) s :=
    intervalIntegral.integral_hasDerivWithinAt_right (by simp)
      hfm.stronglyMeasurableAtFilter ((hc s hs).mono Icc_subset_Ici_self)
  have hz : HasDerivWithinAt (fun t => ∫ r in s..t, f r) 0 (Icc s q) s := by
    apply (hasDerivWithinAt_const s (Icc s q) (0 : ℝ)).congr
    · intro t ht
      exact hi s t ⟨hs.1, hs.2.le⟩ ⟨hs.1.trans ht.1, ht.2⟩ ht.1
    · simp
  calc
    f s = derivWithin (fun t => ∫ r in s..t, f r) (Icc s q) s :=
      (hd.derivWithin (uniqueDiffOn_Icc hs.2 s hmem)).symm
    _ = 0 := hz.derivWithin (uniqueDiffOn_Icc hs.2 s hmem)

/-- Exact pointwise quotient extraction, including time zero. Its interval
 identity is the genuine conclusion of the Gamma moment equation. -/
theorem quotient_of_interval_identity (α A B : ℝ → ℝ) (q : ℝ)
    (hAm : StronglyMeasurable A) (hBm : StronglyMeasurable B)
    (hαm : StronglyMeasurable α)
    (hA : ContinuousOn A (Icc 0 q)) (hB : ContinuousOn B (Icc 0 q))
    (hBpos : ∀ s ∈ Icc (0 : ℝ) q, 0 < B s)
    (hα : ∀ s ∈ Ico (0 : ℝ) q, ContinuousWithinAt α (Ici s) s)
    (hi : ∀ s t, s ∈ Icc (0 : ℝ) q → t ∈ Icc (0 : ℝ) q → s ≤ t →
      ∫ r in s..t, A r - 2 * α r * B r = 0) :
    ∀ s ∈ Ico (0 : ℝ) q, α s = A s / (2 * B s) := by
  have hr : ∀ s ∈ Ico (0 : ℝ) q,
      ContinuousWithinAt (fun r => A r - 2 * α r * B r) (Ici s) s := by
    intro s hs
    have hloc : Icc (0 : ℝ) q ∈ 𝓝[Ici s] s := by
      apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      refine ⟨Iio q, Iio_mem_nhds hs.2, ?_⟩
      intro x hx
      exact ⟨hs.1.trans hx.2, hx.1.le⟩
    have ha := (hA s ⟨hs.1, hs.2.le⟩).mono_of_mem_nhdsWithin hloc
    have hb := (hB s ⟨hs.1, hs.2.le⟩).mono_of_mem_nhdsWithin hloc
    exact ha.sub ((continuousWithinAt_const.mul (hα s hs)).mul hb)
  have hz := eq_zero_of_right_continuous_and_interval_integrals_zero _ q
    (hAm.sub ((stronglyMeasurable_const.mul hαm).mul hBm)) hr hi
  intro s hs
  have hsB := hBpos s ⟨hs.1, hs.2.le⟩
  apply (eq_div_iff (by positivity : 2 * B s ≠ 0)).mpr
  have hh := hz s hs
  change A s - 2 * α s * B s = 0 at hh
  nlinarith

/-- A continuous quotient agreeing with the CDF before q has terminal value
 equal to the actual mass strictly below q. -/
theorem parisiCDF_quotient_terminal_mass (μ : Paper.ParisiMeasure) (A B : ℝ → ℝ)
    (q : ℝ) (hq : 0 < q) (hA : ContinuousOn A (Icc 0 q))
    (hB : ContinuousOn B (Icc 0 q)) (hBpos : ∀ s ∈ Icc (0 : ℝ) q, 0 < B s)
    (he : ∀ s ∈ Ico (0 : ℝ) q, Paper.parisiCDF μ s = A s / (2 * B s)) :
    (((μ : Measure Paper.Overlap) {x | (x : ℝ) < q}).toReal) = A q / (2 * B q) := by
  have hquot : ContinuousOn (fun s => A s / (2 * B s)) (Icc 0 q) :=
    hA.div (continuousOn_const.mul hB) (fun s hs => by have := hBpos s hs; positivity)
  have hlim : Tendsto (fun s => A s / (2 * B s)) (𝓝[<] q) (𝓝 (A q / (2 * B q))) := by
    have hh := (hquot q ⟨hq.le, le_rfl⟩).mono Ioo_subset_Icc_self
    simpa only [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsLT hq] using hh
  have hevent : Paper.parisiCDF μ =ᶠ[𝓝[<] q] (fun s => A s / (2 * B s)) := by
    rw [← nhdsWithin_Ioo_eq_nhdsLT hq]
    exact eventually_nhdsWithin_of_forall (fun s hs => he s ⟨hs.1.le, hs.2⟩)
  exact tendsto_nhds_unique (tendsto_parisiCDF_left μ q) (hlim.congr' hevent.symm)

/-- The zero-time odd third jet forces the actual measure to have no atom
 at zero once the quotient formula is known. -/
theorem parisiMeasure_no_atom_zero_of_quotient (μ : Paper.ParisiMeasure)
    (A B : ℝ → ℝ) (q : ℝ) (hq : 0 < q) (hA0 : A 0 = 0)
    (he : ∀ s ∈ Ico (0 : ℝ) q, Paper.parisiCDF μ s = A s / (2 * B s)) :
    (μ : Measure Paper.Overlap) {⟨0, by simp⟩} = 0 := by
  have hzero : Paper.parisiCDF μ 0 = 0 := by
    rw [he 0 ⟨le_rfl, hq⟩, hA0, zero_div]
  have heq : {x : Paper.Overlap | (x : ℝ) ≤ 0} = {⟨0, by simp⟩} := by
    ext x
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor
    · intro hx
      apply Subtype.ext
      exact le_antisymm hx x.property.1
    · intro hx
      rw [hx]
  rw [Paper.parisiCDF, heq] at hzero
  exact ((ENNReal.toReal_eq_zero_iff _).mp hzero).resolve_right (measure_ne_top _ _)

end FRSB
