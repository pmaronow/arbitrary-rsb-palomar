module

public import DepthPaper.RevisedAtomicInjectivity
public import FourPapersCommon.MixedMeasure

@[expose] public section

/-! Two-sided affine mass lines in the genuine atomic probability chart.
Only validity of the measures at the evaluated parameters is required. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace DepthPaper

def atomicMassDirectionWeight {r : ℕ} (v : AtomicPoint r) : Fin (r + 1) → ℝ :=
  Fin.lastCases (-∑ i, v.2 i) v.2

theorem atomicLocation_mass_line {r : ℕ} (z v : AtomicPoint r) (hv : v.1 = 0)
    (t : ℝ) (i : Fin (r + 1)) : atomicLocation (z + t • v) i = atomicLocation z i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp [atomicLocation_succ, hv]

theorem atomicWeight_mass_line {r : ℕ} (z v : AtomicPoint r)
    (t : ℝ) (i : Fin (r + 1)) :
    atomicWeight (z + t • v) i = atomicWeight z i + t * atomicMassDirectionWeight v i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hs : (z + t • v).2 = fun j => z.2 j + t * v.2 j := rfl
    simp only [atomicWeight_last, atomicMassDirectionWeight, Fin.lastCases_last, hs,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  · simp [atomicWeight_castSucc, atomicMassDirectionWeight]

def atomicMassCDFDirection {r : ℕ} (z v : AtomicPoint r) (q : ℝ) : ℝ :=
  ∑ i : Fin (r + 1), if atomicLocation z i ≤ q then atomicMassDirectionWeight v i else 0

theorem parisiCDF_atomic_mass_line {r : ℕ} (z v : AtomicPoint r)
    (hz : IsAtomicPoint z) (hv : v.1 = 0) (t : ℝ)
    (ht : IsAtomicPoint (z + t • v)) (q : ℝ) :
    Paper.parisiCDF (atomicMeasure (z + t • v) ht) q =
      Paper.parisiCDF (atomicMeasure z hz) q + t * atomicMassCDFDirection z v q := by
  rw [parisiCDF_atomicMeasure, parisiCDF_atomicMeasure]
  simp_rw [atomicLocation_mass_line z v hv t, atomicWeight_mass_line z v t]
  unfold atomicMassCDFDirection
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

/-- The line is affine through any nonzero valid parameter, including for
negative nearby parameters. This is stronger than a one-sided measure mix. -/
theorem parisiCDF_atomic_mass_line_affine {r : ℕ} (z v : AtomicPoint r)
    (hz : IsAtomicPoint z) (hv : v.1 = 0) (ε : ℝ) (hε : ε ≠ 0)
    (hεz : IsAtomicPoint (z + ε • v)) (t : ℝ)
    (ht : IsAtomicPoint (z + t • v)) (q : ℝ) :
    Paper.parisiCDF (atomicMeasure (z + t • v) ht) q =
      Paper.parisiCDF (atomicMeasure z hz) q + (t / ε) *
        (Paper.parisiCDF (atomicMeasure (z + ε • v) hεz) q -
          Paper.parisiCDF (atomicMeasure z hz) q) := by
  rw [parisiCDF_atomic_mass_line z v hz hv t ht,
    parisiCDF_atomic_mass_line z v hz hv ε hεz]
  field_simp
  ring

theorem parisiCDF_mixed_atomic_mass_line_affine
    (ξ : FourPapersCommon.AdmissibleEvenMixture) {r : ℕ} (z v : AtomicPoint r)
    (hz : IsAtomicPoint z) (hv : v.1 = 0) (ε : ℝ) (hε : ε ≠ 0)
    (hεz : IsAtomicPoint (z + ε • v)) (t : ℝ)
    (ht : IsAtomicPoint (z + t • v)) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    Paper.parisiCDF (FourPapersCommon.mixedMeasure ξ (atomicMeasure (z + t • v) ht)) s =
      Paper.parisiCDF (FourPapersCommon.mixedMeasure ξ (atomicMeasure z hz)) s +
        (t / ε) *
          (Paper.parisiCDF (FourPapersCommon.mixedMeasure ξ
            (atomicMeasure (z + ε • v) hεz)) s -
            Paper.parisiCDF (FourPapersCommon.mixedMeasure ξ (atomicMeasure z hz)) s) := by
  obtain ⟨q, hq⟩ := ξ.surjective_unitClock ⟨s, hs⟩
  have he : ξ.clock q = s := congrArg Subtype.val hq
  rw [← he]
  simp only [FourPapersCommon.parisiCDF_mixedMeasure ξ _ q q.property]
  exact parisiCDF_atomic_mass_line_affine z v hz hv ε hε hεz t ht q

theorem atomicMassLine_eventually_valid {r : ℕ} (z v : AtomicPoint r)
    (hz : IsAtomicPoint z) : ∀ᶠ t : ℝ in 𝓝 0, IsAtomicPoint (z + t • v) := by
  have hc : Continuous (fun t : ℝ => z + t • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hc0 : ContinuousAt (fun t : ℝ => z + t • v) 0 := hc.continuousAt
  have hn := hc0.eventually ((isOpen_atomic_domain r).mem_nhds (by simpa using hz))
  simpa using hn

theorem atomicMassLine_measure_ne {r : ℕ} (z v : AtomicPoint r)
    (hz : IsAtomicPoint z) (hv : v.1 = 0) (hv0 : v ≠ 0)
    (ε : ℝ) (hε : ε ≠ 0) (hεz : IsAtomicPoint (z + ε • v)) :
    atomicMeasure (z + ε • v) hεz ≠ atomicMeasure z hz := by
  intro he
  have hloc : (z + ε • v).1 = z.1 := by simp [hv]
  have hzEq := atomicMeasure_injective_fixed_locations _ _ hεz hz hloc he
  have hs : ε • v = 0 := by
    apply add_left_cancel (a := z)
    simpa using hzEq
  exact hv0 ((smul_eq_zero.mp hs).resolve_left hε)

end DepthPaper
