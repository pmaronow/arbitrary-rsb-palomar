module

public import GeneralDepthPaper.AtomicCoordinates
public import GeneralDepthPaper.QuarticSeed

@[expose] public section


/-! Definition 2.5 and the zero-depth nondegenerate seed. The Hessian is
the actual second Fréchet derivative of the actual atomic Parisi functional
on the open coordinate chart. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace GeneralDepthPaper

def atomicFunctionalExtension (Ξ : AdmissibleCovariance) (r : ℕ) (z : AtomicPoint r) : ℝ :=
  @dite ℝ (IsAtomicPoint z) (Classical.propDecidable _)
    (fun hz=>atomicFunctional Ξ z hz) (fun _=>0)

theorem atomicFunctionalExtension_eq (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) :
    atomicFunctionalExtension Ξ r z=parisiFunctional Ξ (atomicMeasure z hz) := by
  simp only [atomicFunctionalExtension,dif_pos hz,atomicFunctional]

def positiveAtomicHessian (Ξ : AdmissibleCovariance) {r : ℕ} (z : AtomicPoint r) : Prop :=
  ∀v : AtomicPoint r,v≠0 →
    0<(fderiv ℝ (fun y=>fderiv ℝ (atomicFunctionalExtension Ξ r) y) z v) v

def Nondegenerate (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) : Prop :=
  IsParisiMinimizer Ξ (atomicMeasure z hz) ∧
    (∀q∈Icc (0:ℝ) 1,firstVariation Ξ (atomicMeasure z hz) q≤0 ∧
      (firstVariation Ξ (atomicMeasure z hz) q=0 ↔ ∃i,q=atomicLocation z i)) ∧
    (∀i : Fin r,closedJet 1 2 (firstVariation Ξ (atomicMeasure z hz)) (z.1 i)<0) ∧
    positiveAtomicHessian Ξ z ∧ Ξ.IsSubcritical

theorem isAtomicPoint_zero_depth : IsAtomicPoint (0 : AtomicPoint 0) := by
  letI : Subsingleton (Fin (0+1)) := inferInstanceAs (Subsingleton (Fin 1))
  refine ⟨?_,?_,?_⟩
  · intro i j hij
    exact False.elim (hij.ne (Subsingleton.elim i j))
  · change (0:ℝ)<1
    norm_num
  · intro i
    have hi : i=Fin.last 0 := Subsingleton.elim _ _
    rw [hi,atomicWeight_last]
    simp

theorem atomicMeasure_zero_depth :
    atomicMeasure (0 : AtomicPoint 0) isAtomicPoint_zero_depth=
      Paper.diracOverlap 0 (by norm_num) := by
  apply MeasureTheory.ProbabilityMeasure.toMeasure_injective
  change (∑i : Fin 1,ENNReal.ofReal (atomicWeight (0 : AtomicPoint 0) i) •
    Measure.dirac (atomicOverlap (0 : AtomicPoint 0) isAtomicPoint_zero_depth i)) = _
  rw [Fin.sum_univ_one]
  have hw : atomicWeight (0 : AtomicPoint 0) (0 : Fin 1)=1 := by
    change atomicWeight (0 : AtomicPoint 0) (Fin.last 0)=1
    rw [atomicWeight_last]
    simp only [Finset.univ_eq_empty,Finset.sum_empty,sub_zero]
  rw [hw,ENNReal.ofReal_one,one_smul]
  rfl

theorem positiveAtomicHessian_zero_depth (Ξ : AdmissibleCovariance) :
    positiveAtomicHessian Ξ (0 : AtomicPoint 0) := by
  intro v hv
  exact False.elim (hv (Subsingleton.elim _ _))

/-- The genuine nondegenerate zero-step base used by the depth induction. -/
theorem quarticSeed_nondegenerate :
    Nondegenerate quarticSeed (0 : AtomicPoint 0) isAtomicPoint_zero_depth := by
  unfold Nondegenerate
  rw [atomicMeasure_zero_depth]
  refine ⟨quarticSeed_dirac_minimizes,?_,?_,⟨positiveAtomicHessian_zero_depth _, by norm_num [AdmissibleCovariance.IsSubcritical, AdmissibleCovariance.second, quarticSeed]⟩⟩
  · intro q hq
    have hzero := quarticSeed_firstVariation_zero_iff (Paper.diracOverlap 0 (by norm_num)) hq
    refine ⟨?_,?_⟩
    · rcases hq.1.eq_or_lt with rfl|hp
      · simp only [firstVariation_zero,le_refl]
      · exact (quarticSeed_firstVariation_neg _ ⟨hp,hq.2⟩).le
    · letI : Subsingleton (Fin (0+1)) := inferInstanceAs (Subsingleton (Fin 1))
      rw [hzero]
      constructor
      · intro hq0
        exact ⟨0,by simpa only [atomicLocation_zero] using hq0⟩
      · rintro ⟨i,hi⟩
        have hi0 : i=(0 : Fin 1) := Subsingleton.elim _ _
        simpa only [hi0,atomicLocation_zero] using hi
  · exact fun i=>Fin.elim0 i

theorem quarticSeed_zero_RSB : IsFiniteRSB 0 (parisiMinimizer quarticSeed) := by
  rw [quarticSeed_parisiMinimizer,←atomicMeasure_zero_depth]
  exact atomicMeasure_isFiniteRSB _ _

end GeneralDepthPaper
