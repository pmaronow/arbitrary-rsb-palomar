module

public import DepthPaper.AtomicLocationPath
public import DepthPaper.WeakVariationValueMap

@[expose] public section


/-! Actual mass-transfer paths in the positive atomic coordinate chart. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ContDiff
namespace DepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 600000

def atomicMassDirection {r : ℕ} (i : Fin r) : AtomicPoint r := (0,Pi.single i 1)
def atomicMassPath {r : ℕ} (z : AtomicPoint r) (i : Fin r) (t : ℝ) : AtomicPoint r :=
  z+t • atomicMassDirection i

@[simp] theorem atomicMassPath_zero {r : ℕ} (z : AtomicPoint r) (i : Fin r) :
    atomicMassPath z i 0=z := by simp [atomicMassPath]

theorem continuous_atomicMassPath {r : ℕ} (z : AtomicPoint r) (i : Fin r) :
    Continuous (atomicMassPath z i) := continuous_const.add (continuous_id.smul continuous_const)

theorem contDiff_atomicMassPath {r : ℕ} (z : AtomicPoint r) (i : Fin r) :
    ContDiff ℝ ∞ (atomicMassPath z i) := contDiff_const.add (contDiff_id.smul contDiff_const)

@[simp] theorem atomicLocation_massPath {r : ℕ} (z : AtomicPoint r) (i : Fin r)
    (t : ℝ) (k : Fin (r+1)) : atomicLocation (atomicMassPath z i t) k=atomicLocation z k := by
  have hp : (atomicMassPath z i t).1=z.1 := by
    change z.1+t • (0:Fin r→ℝ)=z.1
    simp
  simp only [atomicLocation,hp]

@[simp] theorem atomicWeight_massPath_castSucc {r : ℕ} (z : AtomicPoint r) (i j : Fin r) (t : ℝ) :
    atomicWeight (atomicMassPath z i t) j.castSucc=atomicWeight z j.castSucc+(if j=i then t else 0) := by
  classical
  by_cases hji : j=i
  · subst j
    simp [atomicWeight_castSucc,atomicMassPath,atomicMassDirection]
  · simp [atomicWeight_castSucc,atomicMassPath,atomicMassDirection,Pi.single_apply,hji]

@[simp] theorem atomicWeight_massPath_last {r : ℕ} (z : AtomicPoint r) (i : Fin r) (t : ℝ) :
    atomicWeight (atomicMassPath z i t) (Fin.last r)=atomicWeight z (Fin.last r)-t := by
  simp only [atomicWeight_last]
  change 1-(∑ j : Fin r, (z.2 j+t*(Pi.single i 1 : Fin r→ℝ) j))=1-(∑ j : Fin r,z.2 j)-t
  rw [Finset.sum_add_distrib,←Finset.mul_sum]
  simp
  ring

theorem atomicMassPath_mem {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z) (i : Fin r) :
    ∀ᶠt in 𝓝 (0:ℝ),IsAtomicPoint (atomicMassPath z i t) :=
  (continuous_atomicMassPath z i).continuousAt
    ((isOpen_atomic_domain r).mem_nhds (by simpa using hz))

theorem atomicMassPath_measure_tendsto {r : ℕ} (z : AtomicPoint r)
    (hz : IsAtomicPoint z) (i : Fin r) :
    Tendsto (fun t=>atomicMeasureExtension r (atomicMassPath z i t)) (𝓝 (0:ℝ))
      (𝓝 (atomicMeasure z hz)) := by
  have hp : Tendsto (atomicMassPath z i) (𝓝 (0:ℝ)) (𝓝 z) := by
    simpa only [atomicMassPath_zero] using
      (continuous_atomicMassPath z i).continuousAt.tendsto (x:=0)
  have ht := (continuousAt_atomicMeasureExtension z hz).tendsto.comp hp
  simpa only [atomicMeasureExtension_eq z hz,Function.comp_def] using ht

theorem integral_massPath_sub {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (i : Fin r) (t : ℝ) (ht : IsAtomicPoint (atomicMassPath z i t)) (f : ℝ→ℝ) :
    (∫q : Overlap,f q ∂(atomicMeasure (atomicMassPath z i t) ht : Measure Overlap))-
      (∫q : Overlap,f q ∂(atomicMeasure z hz : Measure Overlap)) =
      t*(f (atomicLocation z i.castSucc)-f (atomicLocation z (Fin.last r))) := by
  classical
  rw [integral_atomicMeasure,integral_atomicMeasure,←Finset.sum_sub_distrib,Fin.sum_univ_castSucc]
  have he : ∀j : Fin r,atomicWeight (atomicMassPath z i t) j.castSucc*
      f (atomicOverlap (atomicMassPath z i t) ht j.castSucc)-
      atomicWeight z j.castSucc*f (atomicOverlap z hz j.castSucc)=
      if j=i then t*f (atomicLocation z i.castSucc) else 0 := by
    intro j
    simp only [atomicOverlap,atomicLocation_massPath,atomicWeight_massPath_castSucc]
    by_cases hji : j=i
    · subst j; simp; ring
    · simp [hji]
  simp_rw [he]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,atomicOverlap,
    atomicLocation_massPath,atomicWeight_massPath_last]
  ring

end DepthPaper
