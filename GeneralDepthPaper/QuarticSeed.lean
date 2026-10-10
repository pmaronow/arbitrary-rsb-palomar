module

public import GeneralDepthPaper.FirstVariation

@[expose] public section


/-! The genuine quartic seed of Section 6, with strict contact geometry
for every competing Parisi measure and a unique actual Dirac optimizer. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace GeneralDepthPaper

def quarticSeed : AdmissibleCovariance where
  degrees := {4}
  nonempty := ⟨4,by simp⟩
  coefficient := fun _=>1/16
  coefficient_pos := by intros;norm_num
  degree_ge_two := by
    intro p hp
    have he : p=4 := Finset.mem_singleton.mp hp
    rw [he]
    norm_num
  degree_even := by
    intro p hp
    have he : p=4 := Finset.mem_singleton.mp hp
    rw [he]
    decide

@[simp] theorem quarticSeed_value (q : ℝ) : quarticSeed.value q=q^4/16 := by
  simp only [AdmissibleCovariance.value,quarticSeed,Finset.sum_singleton]
  ring

@[simp] theorem quarticSeed_first (q : ℝ) : quarticSeed.first q=q^3/4 := by
  simp only [AdmissibleCovariance.first,quarticSeed,Finset.sum_singleton]
  norm_num
  ring

@[simp] theorem quarticSeed_second (q : ℝ) : quarticSeed.second q=3*q^2/4 := by
  simp only [AdmissibleCovariance.second,quarticSeed,Finset.sum_singleton]
  norm_num
  ring

theorem quarticSeed_Gamma_lt_overlap (μ : ParisiMeasure) {q : ℝ}
    (hq : q∈Ioc (0:ℝ) 1) : Gamma quarticSeed μ q<q := by
  have hh := Gamma_le_first quarticSeed μ ⟨hq.1.le,hq.2⟩
  rw [quarticSeed_first] at hh
  have hq3 := pow_le_of_le_one hq.1.le hq.2 (by decide : 3≠0)
  linarith [hq.1]

theorem quarticSeed_firstVariation_neg (μ : ParisiMeasure) {q : ℝ}
    (hq : q∈Ioc (0:ℝ) 1) : firstVariation quarticSeed μ q<0 := by
  have hm : StrictAntiOn (firstVariation quarticSeed μ) (Icc (0:ℝ) 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (continuousOn_firstVariation quarticSeed μ)
    intro s hs
    rw [interior_Icc] at hs
    rw [(hasDerivAt_firstVariation quarticSeed μ hs).deriv]
    exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) (quarticSeed.second_pos hs.1))
      (sub_neg.mpr (quarticSeed_Gamma_lt_overlap μ ⟨hs.1,hs.2.le⟩))
  simpa only [firstVariation_zero] using
    hm (by norm_num : (0:ℝ)∈Icc (0:ℝ) 1) ⟨hq.1.le,hq.2⟩ hq.1

theorem quarticSeed_firstVariation_zero_iff (μ : ParisiMeasure) {q : ℝ}
    (hq : q∈Icc (0:ℝ) 1) : firstVariation quarticSeed μ q=0 ↔ q=0 := by
  constructor
  · intro h
    by_contra hq0
    have := quarticSeed_firstVariation_neg μ ⟨lt_of_le_of_ne hq.1 (fun he=>hq0 he.symm),hq.2⟩
    linarith
  · rintro rfl
    exact firstVariation_zero _ _

theorem quarticSeed_dirac_minimizes :
    IsParisiMinimizer quarticSeed (Paper.diracOverlap 0 (by norm_num)) := by
  apply isParisiMinimizer_of_nonpos_zero_support
  · intro q hq
    rcases hq.1.eq_or_lt with rfl|hq0
    · simp only [firstVariation_zero,le_refl]
    · exact (quarticSeed_firstVariation_neg _ ⟨hq0,hq.2⟩).le
  · intro q hq
    rw [Paper.support_diracOverlap] at hq
    have hq0 := Set.mem_singleton_iff.mp hq
    subst q
    exact firstVariation_zero _ _

theorem quarticSeed_parisiMinimizer :
    parisiMinimizer quarticSeed=Paper.diracOverlap 0 (by norm_num) :=
  (parisiMinimizer_unique quarticSeed _ quarticSeed_dirac_minimizes).symm

end GeneralDepthPaper
