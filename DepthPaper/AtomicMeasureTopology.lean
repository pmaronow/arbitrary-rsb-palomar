module

public import DepthPaper.AtomicCoordinates
public import FourPapersCommon.AllFieldMomentStability

@[expose] public section


/-! Genuine weak continuity of the positive finite atomic chart. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace DepthPaper
set_option maxHeartbeats 500000

abbrev AtomicDomain (r : ℕ) := {z : AtomicPoint r // IsAtomicPoint z}

def atomicChartMeasure {r : ℕ} (z : AtomicDomain r) : ParisiMeasure :=
  atomicMeasure z.1 z.2

theorem integral_atomicMeasure {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (f : Overlap→ℝ) :
    (∫q,f q ∂(atomicMeasure z hz : Measure Overlap))=
      ∑i,atomicWeight z i*f (atomicOverlap z hz i) := by
  rw [atomicMeasure_measure,integral_finsetSum_measure]
  · simp only [integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal (hz.2.2 _).le,
      smul_eq_mul]
  · intro i _
    exact (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top

theorem continuous_atomicChartOverlap {r : ℕ} (i : Fin (r+1)) :
    Continuous (fun z : AtomicDomain r=>atomicOverlap z.1 z.2 i) :=
  ((continuous_atomicLocation i).comp continuous_subtype_val).subtype_mk
    (fun z=>atomicLocation_mem_unit z.2 i)

theorem continuous_atomicChartMeasure (r : ℕ) :
    Continuous (atomicChartMeasure (r:=r)) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr
  intro f
  simp_rw [atomicChartMeasure,integral_atomicMeasure]
  exact continuous_finsetSum _ (fun i _=>
    ((continuous_atomicWeight i).comp continuous_subtype_val).mul
      (f.continuous.comp (continuous_atomicChartOverlap i)))


def atomicMeasureExtension (r : ℕ) (z : AtomicPoint r) : ParisiMeasure :=
  @dite ParisiMeasure (IsAtomicPoint z) (Classical.propDecidable _)
    (fun hz=>atomicMeasure z hz)
    (fun _=>⟨Measure.dirac ⟨0,by norm_num⟩,Measure.dirac.isProbabilityMeasure⟩)

@[simp] theorem atomicMeasureExtension_eq {r : ℕ} (z : AtomicPoint r)
    (hz : IsAtomicPoint z) : atomicMeasureExtension r z=atomicMeasure z hz := by
  unfold atomicMeasureExtension
  exact @dite_eq_left (IsAtomicPoint z) (Classical.propDecidable _) hz ParisiMeasure _ _

theorem continuousAt_atomicMeasureExtension {r : ℕ} (z : AtomicPoint r)
    (hz : IsAtomicPoint z) : ContinuousAt (atomicMeasureExtension r) z := by
  have hc : ContinuousOn (atomicMeasureExtension r) {z | IsAtomicPoint z} := by
    apply continuousOn_iff_continuous_restrict.mpr
    have he : (fun z : AtomicDomain r=>atomicMeasureExtension r z.1)=atomicChartMeasure := by
      funext y
      exact atomicMeasureExtension_eq y.1 y.2
    change Continuous (fun z : AtomicDomain r=>atomicMeasureExtension r z.1)
    rw [he]
    exact continuous_atomicChartMeasure r
  exact hc.continuousAt ((isOpen_atomic_domain r).mem_nhds hz)

end DepthPaper
