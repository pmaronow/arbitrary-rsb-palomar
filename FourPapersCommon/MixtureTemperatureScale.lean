module

public import FourPapersCommon.Mixture

@[expose] public section


/-! Genuine rescaling of the countable covariance mixture by temperature. -/
noncomputable section
namespace FourPapersCommon.AdmissibleEvenMixture

def temperatureScale (ξ : AdmissibleEvenMixture) (b : ℝ) (hb : b ≠ 0) : AdmissibleEvenMixture where
  coefficient p := b^2*ξ.coefficient p
  nonneg p := mul_nonneg (sq_nonneg b) (ξ.nonneg p)
  active_even p hp := ξ.active_even p (by intro hz; apply hp; simp [hz])
  nonzero := by
    obtain ⟨p,hp⟩ := ξ.nonzero
    exact ⟨p,mul_pos (sq_pos_of_ne_zero hb) hp⟩
  summable := by
    convert ξ.summable.mul_left (b^2) using 1
    funext p
    ring

@[simp] theorem temperatureScale_coefficient (ξ : AdmissibleEvenMixture) (b : ℝ) (hb : b ≠ 0) (p : ℕ) :
    (ξ.temperatureScale b hb).coefficient p=b^2*ξ.coefficient p := rfl

theorem temperatureScale_value (ξ : AdmissibleEvenMixture) (b : ℝ) (hb : b ≠ 0) (q : ℝ) :
    (ξ.temperatureScale b hb).value q=b^2*ξ.value q := by
  unfold value
  rw [←tsum_mul_left]
  apply tsum_congr
  intro p
  simp only [temperatureScale_coefficient]
  ring

theorem temperatureScale_first (ξ : AdmissibleEvenMixture) (b : ℝ) (hb : b ≠ 0) (q : ℝ) :
    (ξ.temperatureScale b hb).first q=b^2*ξ.first q := by
  unfold first
  rw [←tsum_mul_left]
  apply tsum_congr
  intro p
  simp only [temperatureScale_coefficient]
  ring

theorem temperatureScale_second (ξ : AdmissibleEvenMixture) (b : ℝ) (hb : b ≠ 0) (q : ℝ) :
    (ξ.temperatureScale b hb).second q=b^2*ξ.second q := by
  unfold second
  rw [←tsum_mul_left]
  apply tsum_congr
  intro p
  simp only [temperatureScale_coefficient]
  ring

theorem temperatureScale_clock (ξ : AdmissibleEvenMixture) (b : ℝ) (hb : b ≠ 0) (q : ℝ) :
    (ξ.temperatureScale b hb).clock q=ξ.clock q := by
  unfold clock variance
  rw [temperatureScale_first,temperatureScale_first]
  exact mul_div_mul_left _ _ (pow_ne_zero _ hb)

end FourPapersCommon.AdmissibleEvenMixture
