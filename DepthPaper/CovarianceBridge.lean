module

public import DepthPaper.Covariance
public import FourPapersCommon.Mixture

@[expose] public section


/-! A finite positive even polynomial is a genuine exponentially summable
mixed covariance. The bridge preserves its actual value and derivatives. -/
noncomputable section
open scoped BigOperators
namespace DepthPaper.AdmissibleCovariance

def toEvenMixture (Ξ : DepthPaper.AdmissibleCovariance) :
    FourPapersCommon.AdmissibleEvenMixture where
  coefficient p := if p ∈ Ξ.degrees then Ξ.coefficient p else 0
  nonneg p := by
    split_ifs with hp
    · exact (Ξ.coefficient_pos p hp).le
    · exact le_rfl
  active_even p hp := by
    by_cases hm : p ∈ Ξ.degrees
    · exact ⟨by have := Ξ.degree_ge_four p hm; omega,Ξ.degree_even p hm⟩
    · simp only [if_neg hm,ne_eq,not_true_eq_false] at hp
  nonzero := by
    obtain ⟨p,hp⟩ := Ξ.nonempty
    exact ⟨p,by simpa only [if_pos hp] using Ξ.coefficient_pos p hp⟩
  summable := summable_of_ne_finset_zero (s := Ξ.degrees) (by
    intro p hp
    simp only [if_neg hp,mul_zero])

@[simp] theorem toEvenMixture_coefficient (Ξ : DepthPaper.AdmissibleCovariance) (p : ℕ) :
    Ξ.toEvenMixture.coefficient p = if p ∈ Ξ.degrees then Ξ.coefficient p else 0 := rfl

@[simp] theorem toEvenMixture_value (Ξ : DepthPaper.AdmissibleCovariance) (q : ℝ) :
    Ξ.toEvenMixture.value q=Ξ.value q := by
  unfold FourPapersCommon.AdmissibleEvenMixture.value
  rw [tsum_eq_sum (s := Ξ.degrees) (fun p hp => by simp [hp])]
  exact Finset.sum_congr rfl fun p hp => by simp only [toEvenMixture_coefficient,if_pos hp]

@[simp] theorem toEvenMixture_first (Ξ : DepthPaper.AdmissibleCovariance) (q : ℝ) :
    Ξ.toEvenMixture.first q=Ξ.first q := by
  unfold FourPapersCommon.AdmissibleEvenMixture.first
  rw [tsum_eq_sum (s := Ξ.degrees) (fun p hp => by simp [hp])]
  exact Finset.sum_congr rfl fun p hp => by
    simp only [toEvenMixture_coefficient,if_pos hp]
    ring

@[simp] theorem toEvenMixture_second (Ξ : DepthPaper.AdmissibleCovariance) (q : ℝ) :
    Ξ.toEvenMixture.second q=Ξ.second q := by
  unfold FourPapersCommon.AdmissibleEvenMixture.second
  rw [tsum_eq_sum (s := Ξ.degrees) (fun p hp => by simp [hp])]
  exact Finset.sum_congr rfl fun p hp => by
    simp only [toEvenMixture_coefficient,if_pos hp]
    ring

@[simp] theorem toEvenMixture_variance (Ξ : DepthPaper.AdmissibleCovariance) :
    Ξ.toEvenMixture.variance=Ξ.variance := by
  simp only [FourPapersCommon.AdmissibleEvenMixture.variance,variance,toEvenMixture_first]

@[simp] theorem toEvenMixture_clock (Ξ : DepthPaper.AdmissibleCovariance) (q : ℝ) :
    Ξ.toEvenMixture.clock q=Ξ.clock q := by
  simp only [FourPapersCommon.AdmissibleEvenMixture.clock,clock,toEvenMixture_first,
    toEvenMixture_variance]

end DepthPaper.AdmissibleCovariance
