module

public import FRSB.FiniteSchemeRepresentation
public import GeneralDepthPaper.AtomicCoordinates
public import Paper.JTVariational

@[expose] public section

/-!
# Exact finite-scheme representation of probability mixing directions

Every finitely supported probability measure on the closed overlap interval
has a finite Gaussian scheme, including endpoint atoms. Convex mixing preserves
finite support. These bridges justify evaluating concrete scheme infima along
the right-hand directions used in the independent transition interface.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace DepthPaper.RevisedFiniteScheme

/-- Exact scheme representation, with no assumptions about ordered coordinates. -/
theorem finite_support_scheme_representation (μ : Paper.ParisiMeasure)
    (hfin : (μ : Measure Paper.Overlap).support.Finite) :
    ∃ n, ∃ s : SpinGlass.Targets.RSBScheme n, Paper.parisiSchemeMeasure s = μ :=
  FRSB.exists_RSBScheme_of_finite_support μ hfin

/-- Scaling a measure cannot enlarge its topological support. -/
theorem support_smul_subset (μ : Measure Paper.Overlap) (c : ℝ≥0∞) :
    (c • μ).support ⊆ μ.support :=
  Measure.smul_absolutelyContinuous.support_mono

/-- Finite support is preserved by the actual probability mixing variation.
The extension outside the unit parameter interval is the initial measure. -/
theorem finite_support_parisiMix (μ ν : Paper.ParisiMeasure)
    (hμ : (μ : Measure Paper.Overlap).support.Finite)
    (hν : (ν : Measure Paper.Overlap).support.Finite) (t : ℝ) :
    (Paper.parisiMix μ ν t : Measure Paper.Overlap).support.Finite := by
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · apply (hμ.union hν).subset
    rw [Paper.parisiMix_measure μ ν t ht, Measure.support_add]
    exact union_subset_union (support_smul_subset _ _) (support_smul_subset _ _)
  · have he : Paper.parisiMix μ ν t = μ := by simp [Paper.parisiMix, ht]
    rw [he]
    exact hμ

/-- Every finite mixing direction is represented exactly by a scheme. -/
theorem exists_scheme_parisiMix (μ ν : Paper.ParisiMeasure)
    (hμ : (μ : Measure Paper.Overlap).support.Finite)
    (hν : (ν : Measure Paper.Overlap).support.Finite) (t : ℝ) :
    ∃ n, ∃ s : SpinGlass.Targets.RSBScheme n,
      Paper.parisiSchemeMeasure s = Paper.parisiMix μ ν t :=
  finite_support_scheme_representation _ (finite_support_parisiMix μ ν hμ hν t)

/-- An arbitrary atom insertion, including zero and one, is a genuine finite
scheme direction from every valid atomic chart point. -/
theorem exists_scheme_atomic_dirac_mix {r : ℕ}
    (z : GeneralDepthPaper.AtomicPoint r) (hz : GeneralDepthPaper.IsAtomicPoint z)
    (q : Paper.Overlap) (t : ℝ) :
    ∃ n, ∃ s : SpinGlass.Targets.RSBScheme n,
      Paper.parisiSchemeMeasure s = Paper.parisiMix
        (GeneralDepthPaper.atomicMeasure z hz) (Paper.diracOverlap q q.property) t := by
  apply exists_scheme_parisiMix
  · rw [GeneralDepthPaper.support_atomicMeasure]
    exact finite_range _
  · rw [Paper.support_diracOverlap]
    exact finite_singleton _

end DepthPaper.RevisedFiniteScheme
