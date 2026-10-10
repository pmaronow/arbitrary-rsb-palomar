module

public import GeneralDepthPaper.AtomicMassPath

@[expose] public section


/-! The literal partial-mass atomic family of Corollary 2.3. The upper atom
may have zero mass when `m=1`; no positive-mass chart for that atom is imposed. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators BoundedContinuousFunction
namespace GeneralDepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

def partialAtomicMeasure {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (m : ℝ) (Q : Overlap) : ParisiMeasure :=
  Paper.parisiMix (Measure.dirac Q).toProbabilityMeasure (atomicMeasure z hz) m

def partialAtomicMeasureExtension (r : ℕ) (m : ℝ) (Q : Overlap) (z : AtomicPoint r) :
    ParisiMeasure :=
  Paper.parisiMix (Measure.dirac Q).toProbabilityMeasure (atomicMeasureExtension r z) m

@[simp] theorem partialAtomicMeasureExtension_eq {r : ℕ} (z : AtomicPoint r)
    (hz : IsAtomicPoint z) (m : ℝ) (Q : Overlap) :
    partialAtomicMeasureExtension r m Q z=partialAtomicMeasure z hz m Q := by
  rw [partialAtomicMeasureExtension,atomicMeasureExtension_eq]
  rfl

def partialAtomicFunctionalExtension (Ξ : AdmissibleCovariance) (r : ℕ)
    (m : ℝ) (Q : Overlap) (z : AtomicPoint r) : ℝ :=
  parisiFunctional Ξ (partialAtomicMeasureExtension r m Q z)

theorem integral_partialAtomicMeasure {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (m : ℝ) (hm : m∈Icc (0:ℝ) 1) (Q : Overlap) (f : Overlap→ℝ) (hf : Continuous f) :
    (∫q,f q ∂(partialAtomicMeasure z hz m Q : Measure Overlap))=
      (1-m)*f Q+m*(∑i,atomicWeight z i*f (atomicOverlap z hz i)) := by
  rw [partialAtomicMeasure,Paper.integral_parisiMix hf _ _ _ hm,integral_atomicMeasure]
  simp only [Measure.toProbabilityMeasure,ProbabilityMeasure.toMeasure,integral_dirac]

theorem continuousAt_partialAtomicMeasureExtension {r : ℕ} (z : AtomicPoint r)
    (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1) (Q : Overlap) :
    ContinuousAt (partialAtomicMeasureExtension r m Q) z := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have hμ:=(continuousAt_atomicMeasureExtension z hz).tendsto
  have hi:=ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ f
  have hh:= (hi.const_mul m).const_add ((1-m)*f Q)
  have he (y : AtomicPoint r) :
      (∫q,f q ∂(partialAtomicMeasureExtension r m Q y : Measure Overlap))=
        (1-m)*f Q+m*(∫q,f q ∂(atomicMeasureExtension r y : Measure Overlap)) := by
    rw [partialAtomicMeasureExtension,Paper.integral_parisiMix f.continuous _ _ _ hm]
    simp only [Measure.toProbabilityMeasure,ProbabilityMeasure.toMeasure,integral_dirac]
  simp_rw [he]
  exact hh

theorem partialAtomicLocationPath_measure_tendsto {r : ℕ} (z : AtomicPoint r)
    (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1) (Q : Overlap) (i : Fin r) :
    Tendsto (fun t=>partialAtomicMeasureExtension r m Q (atomicLocationPath z i t))
      (𝓝 (0:ℝ)) (𝓝 (partialAtomicMeasure z hz m Q)) := by
  have hp : Tendsto (atomicLocationPath z i) (𝓝 (0:ℝ)) (𝓝 z) := by
    simpa only [atomicLocationPath_zero] using
      (continuous_atomicLocationPath z i).continuousAt.tendsto (x:=0)
  have hh := (continuousAt_partialAtomicMeasureExtension z hz m hm Q).tendsto.comp hp
  rw [partialAtomicMeasureExtension_eq z hz m Q] at hh
  simpa only [Function.comp_def] using hh

theorem partialAtomicMassPath_measure_tendsto {r : ℕ} (z : AtomicPoint r)
    (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1) (Q : Overlap) (i : Fin r) :
    Tendsto (fun t=>partialAtomicMeasureExtension r m Q (atomicMassPath z i t))
      (𝓝 (0:ℝ)) (𝓝 (partialAtomicMeasure z hz m Q)) := by
  have hp : Tendsto (atomicMassPath z i) (𝓝 (0:ℝ)) (𝓝 z) := by
    simpa only [atomicMassPath_zero] using
      (continuous_atomicMassPath z i).continuousAt.tendsto (x:=0)
  have hh := (continuousAt_partialAtomicMeasureExtension z hz m hm Q).tendsto.comp hp
  rw [partialAtomicMeasureExtension_eq z hz m Q] at hh
  simpa only [Function.comp_def] using hh

theorem integral_partialAtomicLocationPath_sub {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (m : ℝ) (hm : m∈Icc (0:ℝ) 1) (Q : Overlap) (i : Fin r) (t : ℝ)
    (ht : IsAtomicPoint (atomicLocationPath z i t)) (f : ℝ→ℝ)
    (hf : Continuous (fun q : Overlap=>f q)) :
    (∫q : Overlap,f q ∂(partialAtomicMeasure (atomicLocationPath z i t) ht m Q : Measure Overlap))-
      (∫q : Overlap,f q ∂(partialAtomicMeasure z hz m Q : Measure Overlap))=
      (m*atomicWeight z i.succ)*(f (z.1 i+t)-f (z.1 i)) := by
  simp only [partialAtomicMeasure,Paper.integral_parisiMix hf _ _ _ hm]
  have hi:=integral_locationPath_sub z hz i t ht f
  calc
    _=m*((∫q : Overlap,f q ∂(atomicMeasure (atomicLocationPath z i t) ht : Measure Overlap))-
      (∫q : Overlap,f q ∂(atomicMeasure z hz : Measure Overlap))) := by ring
    _=_ := by rw [hi]; ring

theorem integral_partialAtomicMassPath_sub {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (m : ℝ) (hm : m∈Icc (0:ℝ) 1) (Q : Overlap) (i : Fin r) (t : ℝ)
    (ht : IsAtomicPoint (atomicMassPath z i t)) (f : ℝ→ℝ)
    (hf : Continuous (fun q : Overlap=>f q)) :
    (∫q : Overlap,f q ∂(partialAtomicMeasure (atomicMassPath z i t) ht m Q : Measure Overlap))-
      (∫q : Overlap,f q ∂(partialAtomicMeasure z hz m Q : Measure Overlap))=
      (m*t)*(f (atomicLocation z i.castSucc)-f (atomicLocation z (Fin.last r))) := by
  simp only [partialAtomicMeasure,Paper.integral_parisiMix hf _ _ _ hm]
  have hi:=integral_massPath_sub z hz i t ht f
  calc
    _=m*((∫q : Overlap,f q ∂(atomicMeasure (atomicMassPath z i t) ht : Measure Overlap))-
      (∫q : Overlap,f q ∂(atomicMeasure z hz : Measure Overlap))) := by ring
    _=_ := by rw [hi]; ring

end GeneralDepthPaper
