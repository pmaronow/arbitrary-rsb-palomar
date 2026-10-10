module

public import GeneralDepthPaper.WeakVariationContinuity
public import GeneralDepthPaper.AtomicPotentialRegularity

@[expose] public section


/-! Actual one-location coordinate paths and their finite atomic integrals. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ContDiff
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 600000

def atomicLocationDirection {r : ℕ} (i : Fin r) : AtomicPoint r := (Pi.single i 1,0)
def atomicLocationPath {r : ℕ} (z : AtomicPoint r) (i : Fin r) (t : ℝ) : AtomicPoint r :=
  z+t • atomicLocationDirection i

@[simp] theorem atomicLocationPath_zero {r : ℕ} (z : AtomicPoint r) (i : Fin r) :
    atomicLocationPath z i 0=z := by simp [atomicLocationPath]

theorem continuous_atomicLocationPath {r : ℕ} (z : AtomicPoint r) (i : Fin r) :
    Continuous (atomicLocationPath z i) := continuous_const.add (continuous_id.smul continuous_const)

theorem contDiff_atomicLocationPath {r : ℕ} (z : AtomicPoint r) (i : Fin r) :
    ContDiff ℝ ∞ (atomicLocationPath z i) := contDiff_const.add (contDiff_id.smul contDiff_const)

@[simp] theorem atomicWeight_locationPath {r : ℕ} (z : AtomicPoint r) (i : Fin r)
    (t : ℝ) (k : Fin (r+1)) : atomicWeight (atomicLocationPath z i t) k=atomicWeight z k := by
  have hp : (atomicLocationPath z i t).2=z.2 := by
    change z.2+t • (0:Fin r→ℝ)=z.2
    simp
  simp only [atomicWeight,hp]

@[simp] theorem atomicLocation_locationPath_same {r : ℕ} (z : AtomicPoint r) (i : Fin r) (t : ℝ) :
    atomicLocation (atomicLocationPath z i t) i.succ=z.1 i+t := by
  simp [atomicLocation_succ,atomicLocationPath,atomicLocationDirection,Pi.single_apply]

theorem atomicLocation_locationPath_ne {r : ℕ} (z : AtomicPoint r) (i : Fin r)
    (t : ℝ) (k : Fin (r+1)) (hk : k≠i.succ) :
    atomicLocation (atomicLocationPath z i t) k=atomicLocation z k := by
  cases k using Fin.cases with
  | zero => simp
  | succ j =>
    have hji : j≠i := by intro he; subst j; exact hk rfl
    simp [atomicLocation_succ,atomicLocationPath,atomicLocationDirection,Pi.single_apply,hji]

theorem atomicLocationPath_mem {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z) (i : Fin r) :
    ∀ᶠt in 𝓝 (0:ℝ),IsAtomicPoint (atomicLocationPath z i t) := by
  exact (continuous_atomicLocationPath z i).continuousAt
    ((isOpen_atomic_domain r).mem_nhds (by simpa using hz))

theorem atomicLocationPath_measure_tendsto {r : ℕ} (z : AtomicPoint r)
    (hz : IsAtomicPoint z) (i : Fin r) :
    Tendsto (fun t=>atomicMeasureExtension r (atomicLocationPath z i t)) (𝓝 (0:ℝ))
      (𝓝 (atomicMeasure z hz)) := by
  have hp : Tendsto (atomicLocationPath z i) (𝓝 (0:ℝ)) (𝓝 z) := by
    simpa only [atomicLocationPath_zero] using
      (continuous_atomicLocationPath z i).continuousAt.tendsto (x:=0)
  have ht := (continuousAt_atomicMeasureExtension z hz).tendsto.comp hp
  simpa only [atomicLocationPath_zero,atomicMeasureExtension_eq z hz,Function.comp_def] using ht

theorem integral_locationPath_sub {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (i : Fin r) (t : ℝ) (ht : IsAtomicPoint (atomicLocationPath z i t)) (f : ℝ→ℝ) :
    (∫q : Overlap,f q ∂(atomicMeasure (atomicLocationPath z i t) ht : Measure Overlap))-
      (∫q : Overlap,f q ∂(atomicMeasure z hz : Measure Overlap)) =
      atomicWeight z i.succ*(f (z.1 i+t)-f (z.1 i)) := by
  classical
  rw [integral_atomicMeasure,integral_atomicMeasure,←Finset.sum_sub_distrib]
  have he : ∀k : Fin (r+1),atomicWeight (atomicLocationPath z i t) k*
      f (atomicOverlap (atomicLocationPath z i t) ht k)-atomicWeight z k*f (atomicOverlap z hz k)=
      if k=i.succ then atomicWeight z i.succ*(f (z.1 i+t)-f (z.1 i)) else 0 := by
    intro k
    rw [atomicWeight_locationPath]
    by_cases hk : k=i.succ
    · subst k
      simp [atomicOverlap,atomicLocation_succ,atomicLocationPath,atomicLocationDirection]
      ring
    · simp only [if_neg hk,atomicOverlap,atomicLocation_locationPath_ne z i t k hk,sub_self]
  simp_rw [he]
  simp

end GeneralDepthPaper
