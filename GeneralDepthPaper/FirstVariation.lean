module

public import GeneralDepthPaper.Curvature
public import FourPapersCommon.MixedFirstVariation

@[expose] public section


/-! The genuine mixed first-variation criterion in the manuscript's lower
primitive convention f(0)=0, including strict uniqueness of its optimizer. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace GeneralDepthPaper
open FourPapersCommon
set_option maxHeartbeats 300000

theorem continuous_firstVariation_overlap (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) :
    Continuous (fun q : Overlap=>firstVariation Ξ μ q) :=
  (continuousOn_firstVariation Ξ μ).comp_continuous continuous_subtype_val
    (fun q=>q.property)

theorem hasDerivWithinAt_parisiFunctional_mix (Ξ : AdmissibleCovariance)
    (μ ν : ParisiMeasure) :
    HasDerivWithinAt (fun ε=>parisiFunctional Ξ (Paper.parisiMix μ ν ε))
      (-((∫q : Overlap,firstVariation Ξ μ q ∂(ν : Measure Overlap))-
        (∫q : Overlap,firstVariation Ξ μ q ∂(μ : Measure Overlap)))) (Ioi (0:ℝ)) 0 := by
  have hd := hasDerivWithinAt_mixedFunctional_mix_tail Ξ.toEvenMixture 0 μ ν
  have hf : Continuous (fun q : Overlap=>mixedFirstVariation Ξ.toEvenMixture 0 μ q) :=
    continuous_firstVariation_overlap Ξ μ
  have he : ∀ ρ : ParisiMeasure,
      (∫q,mixedTailVariation Ξ.toEvenMixture 0 μ q ∂(ρ : Measure Overlap)) =
        mixedFirstVariation Ξ.toEvenMixture 0 μ 1-
        ∫q,mixedFirstVariation Ξ.toEvenMixture 0 μ q ∂(ρ : Measure Overlap) := by
    intro ρ
    simp_rw [mixedTailVariation_eq_total_sub]
    rw [integral_sub (integrable_const _) (Paper.integrable_overlap_continuous hf ρ)]
    simp only [integral_const,probReal_univ,one_smul]
  rw [he ν,he μ] at hd
  convert hd using 1 <;> dsimp only [parisiFunctional,firstVariation] <;> ring

theorem isParisiMinimizer_iff_support_firstVariation_max
    (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) :
    IsParisiMinimizer Ξ μ ↔ ∀q∈(μ : Measure Overlap).support,
      ∀r : Overlap,firstVariation Ξ μ r≤firstVariation Ξ μ q :=
  isMixedMinimizer_iff_support_firstVariation_max Ξ.toEvenMixture 0 μ

theorem isParisiMinimizer_of_nonpos_zero_support
    (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (hle : ∀q∈Icc (0:ℝ) 1,firstVariation Ξ μ q≤0)
    (hzero : ∀q∈(μ : Measure Overlap).support,firstVariation Ξ μ q=0) :
    IsParisiMinimizer Ξ μ := by
  apply (isParisiMinimizer_iff_support_firstVariation_max Ξ μ).mpr
  intro q hq r
  rw [hzero q hq]
  exact hle r r.property

/-- Proposition 2.1's literal full-mass criterion. Continuity transfers its
almost-everywhere contact statement to the entire topological support. -/
theorem isParisiMinimizer_of_nonpos_full_zero_mass
    (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (hle : ∀q∈Icc (0:ℝ) 1,firstVariation Ξ μ q≤0)
    (hmass : (μ : Measure Overlap) {q|firstVariation Ξ μ q=0}=1) :
    IsParisiMinimizer Ξ μ := by
  have hclosed : IsClosed {q : Overlap|firstVariation Ξ μ q=0} :=
    isClosed_eq (continuous_firstVariation_overlap Ξ μ) continuous_const
  have hnull : (μ : Measure Overlap) {q|firstVariation Ξ μ q=0}ᶜ=0 := by
    rw [measure_compl hclosed.measurableSet (measure_ne_top _ _),hmass,measure_univ]
    simp
  exact isParisiMinimizer_of_nonpos_zero_support Ξ μ hle
    (fun q hq=>Measure.support_subset_of_isClosed hclosed (mem_ae_iff.mpr hnull) hq)

def parisiMinimizer (Ξ : AdmissibleCovariance) : ParisiMeasure :=
  mixedMinimizer Ξ.toEvenMixture 0

theorem isParisiMinimizer_selected (Ξ : AdmissibleCovariance) :
    IsParisiMinimizer Ξ (parisiMinimizer Ξ) :=
  isMixedMinimizer_selected Ξ.toEvenMixture 0

theorem parisiMinimizer_unique (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (hμ : IsParisiMinimizer Ξ μ) : μ=parisiMinimizer Ξ :=
  mixedMinimizer_unique Ξ.toEvenMixture 0 μ hμ

theorem existsUnique_parisiMinimizer (Ξ : AdmissibleCovariance) :
    ∃!μ,IsParisiMinimizer Ξ μ :=
  existsUnique_mixed_minimizer Ξ.toEvenMixture 0

theorem parisiMinimizer_value (Ξ : AdmissibleCovariance) :
    parisiFunctional Ξ (parisiMinimizer Ξ)=parisiPressure Ξ :=
  mixedMinimizer_value Ξ.toEvenMixture 0

theorem unique_minimizer_of_firstVariation_criterion
    (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (hle : ∀q∈Icc (0:ℝ) 1,firstVariation Ξ μ q≤0)
    (hmass : (μ : Measure Overlap) {q|firstVariation Ξ μ q=0}=1) :
    μ=parisiMinimizer Ξ :=
  parisiMinimizer_unique Ξ μ (isParisiMinimizer_of_nonpos_full_zero_mass Ξ μ hle hmass)

end GeneralDepthPaper
