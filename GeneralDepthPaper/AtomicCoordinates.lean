module

public import GeneralDepthPaper.FirstVariation
public import GeneralDepthPaper.VariationRegularity

set_option backward.privateInPublic true

@[expose] public section


/-! The actual open 2r-dimensional coordinate chart of positive finite-step
Parisi measures. Locations and masses are independent coordinates, with the
origin fixed and the last mass determined by total mass one. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology BigOperators
namespace GeneralDepthPaper
set_option maxHeartbeats 400000

abbrev AtomicPoint (r : ℕ) := (Fin r→ℝ)×(Fin r→ℝ)

def atomicLocation {r : ℕ} (z : AtomicPoint r) : Fin (r+1)→ℝ := Fin.cases 0 z.1

def atomicWeight {r : ℕ} (z : AtomicPoint r) : Fin (r+1)→ℝ :=
  Fin.lastCases (1-∑i,z.2 i) z.2

@[simp] theorem atomicLocation_zero {r : ℕ} (z : AtomicPoint r) : atomicLocation z 0=0 := rfl

@[simp] theorem atomicLocation_succ {r : ℕ} (z : AtomicPoint r) (i : Fin r) :
    atomicLocation z i.succ=z.1 i := rfl

@[simp] theorem atomicWeight_last {r : ℕ} (z : AtomicPoint r) :
    atomicWeight z (Fin.last r)=1-∑i,z.2 i := by simp [atomicWeight]

@[simp] theorem atomicWeight_castSucc {r : ℕ} (z : AtomicPoint r) (i : Fin r) :
    atomicWeight z i.castSucc=z.2 i := by simp [atomicWeight]

theorem sum_atomicWeight {r : ℕ} (z : AtomicPoint r) : ∑i,atomicWeight z i=1 := by
  rw [Fin.sum_univ_castSucc]
  simp only [atomicWeight_last,atomicWeight_castSucc]
  ring

def IsAtomicPoint {r : ℕ} (z : AtomicPoint r) : Prop :=
  StrictMono (atomicLocation z) ∧ atomicLocation z (Fin.last r)<1 ∧
    ∀i,0<atomicWeight z i

theorem continuous_atomicLocation {r : ℕ} (i : Fin (r+1)) :
    Continuous (fun z : AtomicPoint r=>atomicLocation z i) := by
  refine Fin.cases ?_ (fun j=>?_) i
  · simp only [atomicLocation_zero]
    exact continuous_const
  · simp only [atomicLocation_succ]
    exact (continuous_apply j).comp continuous_fst

theorem continuous_atomicWeight {r : ℕ} (i : Fin (r+1)) :
    Continuous (fun z : AtomicPoint r=>atomicWeight z i) := by
  refine Fin.lastCases ?_ (fun j=>?_) i
  · simp only [atomicWeight_last]
    exact continuous_const.sub (continuous_finsetSum _ (fun j _=>
      (continuous_apply j).comp continuous_snd))
  · simp only [atomicWeight_castSucc]
    exact (continuous_apply j).comp continuous_snd

/-- The literal open atomic coordinate domain Z_r. -/
theorem isOpen_atomic_domain (r : ℕ) : IsOpen {z : AtomicPoint r|IsAtomicPoint z} := by
  have hmono : IsOpen {z : AtomicPoint r|StrictMono (atomicLocation z)} := by
    change IsOpen {z : AtomicPoint r|∀i j,i<j→atomicLocation z i<atomicLocation z j}
    simp_rw [ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro _hij
    exact isOpen_lt (continuous_atomicLocation i) (continuous_atomicLocation j)
  have hweight : IsOpen {z : AtomicPoint r|∀i,0<atomicWeight z i} := by
    simp_rw [ofPred_forall]
    exact isOpen_iInter_of_finite (fun i=>isOpen_lt continuous_const (continuous_atomicWeight i))
  exact hmono.inter ((isOpen_lt (continuous_atomicLocation (Fin.last r)) continuous_const).inter hweight)

theorem atomicLocation_mem_unit {r : ℕ} {z : AtomicPoint r} (hz : IsAtomicPoint z)
    (i : Fin (r+1)) : atomicLocation z i∈Icc (0:ℝ) 1 := by
  constructor
  · simpa only [atomicLocation_zero] using hz.1.monotone (Fin.zero_le i)
  · exact (hz.1.monotone (Fin.le_last i)).trans hz.2.1.le

def atomicOverlap {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (i : Fin (r+1)) : Overlap := ⟨atomicLocation z i,atomicLocation_mem_unit hz i⟩

private theorem atomic_probability {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z) :
    IsProbabilityMeasure (∑i : Fin (r+1),ENNReal.ofReal (atomicWeight z i) •
      Measure.dirac (atomicOverlap z hz i)) := by
  apply isProbabilityMeasure_iff.mpr
  simp only [Measure.finsetSum_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
  rw [←ENNReal.ofReal_sum_of_nonneg (fun i _=>(hz.2.2 i).le),sum_atomicWeight]
  norm_num

def atomicMeasure {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z) : ParisiMeasure :=
  ⟨∑i : Fin (r+1),ENNReal.ofReal (atomicWeight z i) •
      Measure.dirac (atomicOverlap z hz i),atomic_probability z hz⟩

theorem atomicMeasure_measure {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z) :
    (atomicMeasure z hz : Measure Overlap)=∑i : Fin (r+1),ENNReal.ofReal (atomicWeight z i) •
      Measure.dirac (atomicOverlap z hz i) := rfl

theorem atomicOverlap_injective {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z) :
    Function.Injective (atomicOverlap z hz) := by
  intro i j hij
  exact hz.1.injective (congrArg (fun x : Overlap=>(x:ℝ)) hij)

def atomicFunctional (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) : ℝ := parisiFunctional Ξ (atomicMeasure z hz)

/-- Literal cumulative mass of the finite atomic measure, including atoms
at the threshold q. -/
theorem parisiCDF_atomicMeasure {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z) (q : ℝ) :
    Paper.parisiCDF (atomicMeasure z hz) q=
      ∑i : Fin (r+1),if atomicLocation z i≤q then atomicWeight z i else 0 := by
  let S : Set Overlap := {x|(x:ℝ)≤q}
  have hS : MeasurableSet S := (isClosed_le continuous_subtype_val continuous_const).measurableSet
  unfold Paper.parisiCDF
  change ((atomicMeasure z hz : Measure Overlap) S).toReal = _
  rw [atomicMeasure_measure,Measure.finsetSum_apply]
  simp only [Measure.smul_apply,Measure.dirac_apply' _ hS,Set.indicator,Pi.one_apply]
  change (∑i : Fin (r+1),ENNReal.ofReal (atomicWeight z i)*
    (if atomicLocation z i≤q then 1 else 0)).toReal = _
  have hn (i : Fin (r+1)) : 0≤(if atomicLocation z i≤q then atomicWeight z i else 0) := by
    split_ifs
    · exact (hz.2.2 i).le
    · exact le_rfl
  have he : (∑i : Fin (r+1),ENNReal.ofReal (atomicWeight z i)*
      (if atomicLocation z i≤q then 1 else 0)) =
      ENNReal.ofReal (∑i : Fin (r+1),if atomicLocation z i≤q then atomicWeight z i else 0) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _=>hn i)]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [he,ENNReal.toReal_ofReal (Finset.sum_nonneg (fun i _=>hn i))]

theorem support_atomicMeasure {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z) :
    (atomicMeasure z hz : Measure Overlap).support=range (atomicOverlap z hz) := by
  apply Set.Subset.antisymm
  · have hclosed : IsClosed (range (atomicOverlap z hz)) := (finite_range _).isClosed
    apply Measure.support_subset_of_isClosed hclosed
    apply mem_ae_iff.mpr
    rw [atomicMeasure_measure,Measure.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro i _
    rw [Measure.smul_apply,Measure.dirac_apply' _ hclosed.measurableSet.compl]
    simp [Set.indicator]
  · rintro _ ⟨j,rfl⟩
    rw [Measure.mem_support_iff_forall]
    intro U hU
    rw [atomicMeasure_measure,Measure.finsetSum_apply]
    have hj : 0<(ENNReal.ofReal (atomicWeight z j) • Measure.dirac (atomicOverlap z hz j)) U := by
      rw [Measure.smul_apply,Measure.dirac_apply_of_mem (mem_of_mem_nhds hU),smul_eq_mul,mul_one]
      exact ENNReal.ofReal_pos.mpr (hz.2.2 j)
    exact hj.trans_le (Finset.single_le_sum (fun i _=>(show 0≤
      ((ENNReal.ofReal (atomicWeight z i) • Measure.dirac (atomicOverlap z hz i)) U) from bot_le))
        (Finset.mem_univ j))

def IsFiniteRSB (r : ℕ) (μ : ParisiMeasure) : Prop :=
  (μ : Measure Overlap).support.Finite ∧ (μ : Measure Overlap).support.ncard=r+1

theorem atomicMeasure_isFiniteRSB {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z) :
    IsFiniteRSB r (atomicMeasure z hz) := by
  unfold IsFiniteRSB
  rw [support_atomicMeasure]
  refine ⟨finite_range _,?_⟩
  simpa only [Nat.card_fin] using ncard_range_of_injective (atomicOverlap_injective z hz)

end GeneralDepthPaper
