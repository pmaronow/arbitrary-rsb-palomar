module

public import GeneralDepthPaper.HighDegreeModel
public import GeneralDepthPaper.AtomicPotentialRegularity

@[expose] public section


/-! Literal change of coordinates from a lower atomic probability, its
total mass, and its appended upper location to the full atomic chart. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128

abbrev TwoLevelAtomicPoint (r : ℕ):=AtomicPoint r×(ℝ×ℝ)

def twoLevelAtomicCoordinates {r : ℕ} (v : TwoLevelAtomicPoint r) : AtomicPoint (r+1) :=
  (Fin.lastCases v.2.2 v.1.1,fun i=>v.2.1*atomicWeight v.1 i)

def twoLevelAtomicInverse {r : ℕ} (y : AtomicPoint (r+1)) : TwoLevelAtomicPoint r :=
  (((fun i=>y.1 i.castSucc),(fun i=>y.2 i.castSucc/(∑j,y.2 j))),
    ((∑j,y.2 j),y.1 (Fin.last r)))

@[simp] theorem twoLevelAtomicCoordinates_location_castSucc {r : ℕ}
    (v : TwoLevelAtomicPoint r) (i : Fin r) :
    (twoLevelAtomicCoordinates v).1 i.castSucc=v.1.1 i := by
  simp [twoLevelAtomicCoordinates]

@[simp] theorem twoLevelAtomicCoordinates_location_last {r : ℕ}
    (v : TwoLevelAtomicPoint r) :
    (twoLevelAtomicCoordinates v).1 (Fin.last r)=v.2.2 := by
  simp [twoLevelAtomicCoordinates]

@[simp] theorem twoLevelAtomicCoordinates_mass {r : ℕ}
    (v : TwoLevelAtomicPoint r) (i : Fin (r+1)) :
    (twoLevelAtomicCoordinates v).2 i=v.2.1*atomicWeight v.1 i := rfl

theorem twoLevelAtomicCoordinates_mass_sum {r : ℕ} (v : TwoLevelAtomicPoint r) :
    (∑i,(twoLevelAtomicCoordinates v).2 i)=v.2.1 := by
  simp only [twoLevelAtomicCoordinates_mass,←Finset.mul_sum,sum_atomicWeight,mul_one]

theorem twoLevelAtomicInverse_coordinates {r : ℕ} (v : TwoLevelAtomicPoint r)
    (hm : v.2.1≠0) : twoLevelAtomicInverse (twoLevelAtomicCoordinates v)=v := by
  unfold twoLevelAtomicInverse
  simp only [twoLevelAtomicCoordinates_mass_sum,twoLevelAtomicCoordinates_location_castSucc,
    twoLevelAtomicCoordinates_mass,atomicWeight_castSucc,twoLevelAtomicCoordinates_location_last,
    ←Finset.mul_sum,sum_atomicWeight,mul_one]
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · funext i
      exact mul_div_cancel_left₀ (v.1.2 i) hm
  · rfl

theorem twoLevelAtomicCoordinates_inverse {r : ℕ} (y : AtomicPoint (r+1))
    (hm : (∑j,y.2 j)≠0) : twoLevelAtomicCoordinates (twoLevelAtomicInverse y)=y := by
  apply Prod.ext
  · funext i
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simp [twoLevelAtomicCoordinates,twoLevelAtomicInverse]
    · simp [twoLevelAtomicCoordinates,twoLevelAtomicInverse]
  · funext i
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simp only [twoLevelAtomicCoordinates_mass,atomicWeight_last,twoLevelAtomicInverse]
      rw [←Finset.sum_div,div_eq_mul_inv]
      have hs:=Fin.sum_univ_castSucc (fun i : Fin (r+1)=>y.2 i)
      field_simp
      linarith
    · simp only [twoLevelAtomicCoordinates_mass,atomicWeight_castSucc,twoLevelAtomicInverse]
      exact mul_div_cancel₀ _ hm

theorem contDiff_twoLevelAtomicCoordinates (r : ℕ) :
    ContDiff ℝ ∞ (twoLevelAtomicCoordinates (r:=r)) := by
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro i
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simpa only [twoLevelAtomicCoordinates,Fin.lastCases_last] using contDiff_snd.snd
    · simpa only [twoLevelAtomicCoordinates,Fin.lastCases_castSucc,Function.comp_def] using
        (contDiff_apply ℝ ℝ j).comp contDiff_fst.fst
  · apply contDiff_pi.mpr
    intro i
    exact contDiff_snd.fst.mul ((contDiff_atomicWeight i).comp contDiff_fst)

theorem contDiffAt_twoLevelAtomicInverse {r : ℕ} (y : AtomicPoint (r+1))
    (hm : (∑j,y.2 j)≠0) : ContDiffAt ℝ ∞ (twoLevelAtomicInverse (r:=r)) y := by
  have hsum : ContDiff ℝ ∞ (fun y : AtomicPoint (r+1)=>∑j,y.2 j):=
    ContDiff.sum fun j _=>(contDiff_apply ℝ ℝ j).comp contDiff_snd
  apply ContDiffAt.prodMk
  · apply ContDiffAt.prodMk
    · apply contDiffAt_pi.mpr
      intro i
      exact ((contDiff_apply ℝ ℝ i.castSucc).comp contDiff_fst).contDiffAt
    · apply contDiffAt_pi.mpr
      intro i
      exact (((contDiff_apply ℝ ℝ i.castSucc).comp contDiff_snd).contDiffAt).div hsum.contDiffAt hm
  · exact hsum.contDiffAt.prodMk (((contDiff_apply ℝ ℝ (Fin.last r)).comp contDiff_fst).contDiffAt)

end GeneralDepthPaper
