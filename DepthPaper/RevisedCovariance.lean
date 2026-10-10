module

public import DepthPaper.CovarianceBridge
public import FourPapersCommon.MixtureTemperatureScale

@[expose] public section

/-! Finite positive even polynomial covariances, including a quadratic term.
Subcriticality at the origin is a separate hypothesis: unrestricted temperature
rescaling is needed to define the physical pressure curve. -/
noncomputable section
open Set
open scoped BigOperators
namespace DepthPaper

abbrev RevisedCovariance :=
  {ξ : FourPapersCommon.AdmissibleEvenMixture // (Function.support ξ.coefficient).Finite}

namespace RevisedCovariance

def toEvenMixture (Ξ : RevisedCovariance) : FourPapersCommon.AdmissibleEvenMixture := Ξ.val

def degrees (Ξ : RevisedCovariance) : Finset ℕ := Ξ.property.toFinset

def coefficient (Ξ : RevisedCovariance) : ℕ → ℝ := Ξ.toEvenMixture.coefficient

@[simp] theorem mem_degrees (Ξ : RevisedCovariance) (p : ℕ) :
    p ∈ Ξ.degrees ↔ Ξ.coefficient p ≠ 0 := by
  simp [degrees, coefficient, toEvenMixture, Function.mem_support]

theorem coefficient_nonneg (Ξ : RevisedCovariance) (p : ℕ) : 0 ≤ Ξ.coefficient p :=
  Ξ.toEvenMixture.nonneg p

theorem coefficient_pos (Ξ : RevisedCovariance) (p : ℕ) (hp : p ∈ Ξ.degrees) :
    0 < Ξ.coefficient p :=
  lt_of_le_of_ne (Ξ.coefficient_nonneg p) ((Ξ.mem_degrees p).mp hp).symm

theorem nonempty (Ξ : RevisedCovariance) : Ξ.degrees.Nonempty := by
  obtain ⟨p,hp⟩ := Ξ.toEvenMixture.nonzero
  exact ⟨p,(Ξ.mem_degrees p).mpr hp.ne'⟩

theorem degree_ge_two (Ξ : RevisedCovariance) (p : ℕ) (hp : p ∈ Ξ.degrees) : 2 ≤ p :=
  (Ξ.toEvenMixture.active_even p ((Ξ.mem_degrees p).mp hp)).1

theorem degree_even (Ξ : RevisedCovariance) (p : ℕ) (hp : p ∈ Ξ.degrees) : Even p :=
  (Ξ.toEvenMixture.active_even p ((Ξ.mem_degrees p).mp hp)).2

end RevisedCovariance

namespace RevisedCovariance

def value (Ξ : RevisedCovariance) (q : ℝ) : ℝ :=
  ∑ p ∈ Ξ.degrees, Ξ.coefficient p * q ^ p

def first (Ξ : RevisedCovariance) (q : ℝ) : ℝ :=
  ∑ p ∈ Ξ.degrees, Ξ.coefficient p * (p : ℝ) * q ^ (p-1)

def second (Ξ : RevisedCovariance) (q : ℝ) : ℝ :=
  ∑ p ∈ Ξ.degrees, Ξ.coefficient p * (p : ℝ) * ((p-1 : ℕ) : ℝ) * q ^ (p-2)

theorem hasDerivAt_value (Ξ : RevisedCovariance) (q : ℝ) :
    HasDerivAt Ξ.value (Ξ.first q) q := by
  unfold value first
  simpa [mul_assoc] using
    (HasDerivAt.fun_sum fun p (_hp : p ∈ Ξ.degrees) =>
      ((hasDerivAt_id q).pow p).const_mul (Ξ.coefficient p))

theorem hasDerivAt_first (Ξ : RevisedCovariance) (q : ℝ) :
    HasDerivAt Ξ.first (Ξ.second q) q := by
  have hn (p : ℕ) (hp : p ∈ Ξ.degrees) : p-1-1=p-2 := by omega
  unfold first second
  simpa [mul_assoc, Nat.sub_sub] using
    (HasDerivAt.fun_sum fun p (hp : p ∈ Ξ.degrees) =>
      ((hasDerivAt_id q).pow (p-1)).const_mul (Ξ.coefficient p * (p:ℝ)))

theorem continuous_value (Ξ : RevisedCovariance) : Continuous Ξ.value :=
  continuous_finsetSum _ fun _ _ => continuous_const.mul (continuous_id.pow _)

theorem continuous_first (Ξ : RevisedCovariance) : Continuous Ξ.first :=
  continuous_finsetSum _ fun _ _ => continuous_const.mul (continuous_id.pow _)

theorem continuous_second (Ξ : RevisedCovariance) : Continuous Ξ.second :=
  continuous_finsetSum _ fun _ _ => continuous_const.mul (continuous_id.pow _)

@[simp] theorem value_zero (Ξ : RevisedCovariance) : Ξ.value 0 = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  have hn : p ≠ 0 := by have := Ξ.degree_ge_two p hp; omega
  simp [hn]

@[simp] theorem first_zero (Ξ : RevisedCovariance) : Ξ.first 0 = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  have hn : p-1 ≠ 0 := by have := Ξ.degree_ge_two p hp; omega
  simp [hn]

theorem value_even (Ξ : RevisedCovariance) (q : ℝ) : Ξ.value (-q)=Ξ.value q := by
  apply Finset.sum_congr rfl
  intro p hp
  rw [(Ξ.degree_even p hp).neg_pow]

theorem first_nonneg (Ξ : RevisedCovariance) {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ Ξ.first q := by
  apply Finset.sum_nonneg
  intro p hp
  exact mul_nonneg (mul_nonneg (Ξ.coefficient_pos p hp).le (Nat.cast_nonneg p))
    (pow_nonneg hq _)

theorem second_nonneg (Ξ : RevisedCovariance) {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ Ξ.second q := by
  apply Finset.sum_nonneg
  intro p hp
  exact mul_nonneg (mul_nonneg (mul_nonneg (Ξ.coefficient_pos p hp).le
    (Nat.cast_nonneg p)) (Nat.cast_nonneg _)) (pow_nonneg hq _)

theorem first_pos (Ξ : RevisedCovariance) {q : ℝ} (hq : 0 < q) :
    0 < Ξ.first q := by
  apply Finset.sum_pos
  · intro p hp
    have hn : 0 < p := by have := Ξ.degree_ge_two p hp; omega
    exact mul_pos (mul_pos (Ξ.coefficient_pos p hp) (Nat.cast_pos.mpr hn)) (pow_pos hq _)
  · exact Ξ.nonempty

theorem second_pos (Ξ : RevisedCovariance) {q : ℝ} (hq : 0 < q) :
    0 < Ξ.second q := by
  apply Finset.sum_pos
  · intro p hp
    have hn : 0 < p := by have := Ξ.degree_ge_two p hp; omega
    have hn1 : 0 < p-1 := by have := Ξ.degree_ge_two p hp; omega
    exact mul_pos (mul_pos (mul_pos (Ξ.coefficient_pos p hp)
      (Nat.cast_pos.mpr hn)) (Nat.cast_pos.mpr hn1)) (pow_pos hq _)
  · exact Ξ.nonempty

theorem first_strictMonoOn (Ξ : RevisedCovariance) : StrictMonoOn Ξ.first (Ici 0) := by
  intro x hx y hy hxy
  apply Finset.sum_lt_sum
  · intro p hp
    have hn : p-1 ≠ 0 := by have := Ξ.degree_ge_two p hp; omega
    have hc : 0 < Ξ.coefficient p * (p:ℝ) := mul_pos (Ξ.coefficient_pos p hp)
      (Nat.cast_pos.mpr (by have := Ξ.degree_ge_two p hp; omega))
    exact (mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hxy hx hn) hc).le
  · obtain ⟨p,hp⟩ := Ξ.nonempty
    refine ⟨p,hp,?_⟩
    have hn : p-1 ≠ 0 := by have := Ξ.degree_ge_two p hp; omega
    exact mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hxy hx hn)
      (mul_pos (Ξ.coefficient_pos p hp)
        (Nat.cast_pos.mpr (by have := Ξ.degree_ge_two p hp; omega)))

/-- Total variance of the time-changed Gaussian driver. -/
def variance (Ξ : RevisedCovariance) : ℝ := Ξ.first 1

theorem variance_pos (Ξ : RevisedCovariance) : 0 < Ξ.variance :=
  Ξ.first_pos zero_lt_one

/-- Normalized variance clock; the original overlap coordinate is retained. -/
def clock (Ξ : RevisedCovariance) (q : ℝ) : ℝ := Ξ.first q / Ξ.variance

theorem continuous_clock (Ξ : RevisedCovariance) : Continuous Ξ.clock :=
  Ξ.continuous_first.div_const _

@[simp] theorem clock_zero (Ξ : RevisedCovariance) : Ξ.clock 0=0 := by simp [clock]
@[simp] theorem clock_one (Ξ : RevisedCovariance) : Ξ.clock 1=1 := by
  simp [clock,variance,ne_of_gt (Ξ.first_pos zero_lt_one)]

theorem clock_strictMonoOn (Ξ : RevisedCovariance) : StrictMonoOn Ξ.clock (Ici 0) := by
  intro x hx y hy hxy
  exact (div_lt_div_iff_of_pos_right Ξ.variance_pos).mpr (Ξ.first_strictMonoOn hx hy hxy)

theorem clock_mem_unit (Ξ : RevisedCovariance) {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) :
    Ξ.clock q ∈ Icc (0:ℝ) 1 := by
  constructor
  · exact div_nonneg (Ξ.first_nonneg hq.1) Ξ.variance_pos.le
  · rw [← Ξ.clock_one]
    exact Ξ.clock_strictMonoOn.monotoneOn hq.1 (by norm_num) hq.2

theorem hasDerivAt_clock (Ξ : RevisedCovariance) (q : ℝ) :
    HasDerivAt Ξ.clock (Ξ.second q / Ξ.variance) q :=
  (Ξ.hasDerivAt_first q).div_const _

@[simp] theorem second_zero (Ξ : RevisedCovariance) :
    Ξ.second 0 = 2 * Ξ.coefficient 2 := by
  unfold second
  rw [Finset.sum_eq_single 2]
  · norm_num
    ring
  · intro p hp hpn
    have hn : p-2 ≠ 0 := by have := Ξ.degree_ge_two p hp; omega
    simp [hn]
  · intro hp
    have hc : Ξ.coefficient 2=0 := not_ne_iff.mp (by simpa using hp)
    simp [hc]

def IsSubcritical (Ξ : RevisedCovariance) : Prop := Ξ.second 0 < 1

@[simp] theorem toEvenMixture_coefficient (Ξ : RevisedCovariance) (p : ℕ) :
    Ξ.toEvenMixture.coefficient p = Ξ.coefficient p := rfl

@[simp] theorem toEvenMixture_value (Ξ : RevisedCovariance) (q : ℝ) :
    Ξ.toEvenMixture.value q=Ξ.value q := by
  unfold FourPapersCommon.AdmissibleEvenMixture.value
  rw [tsum_eq_sum (s := Ξ.degrees) (fun p hp => by
    have hc : Ξ.coefficient p=0 := not_ne_iff.mp (by simpa using hp)
    simp [hc])]
  rfl

@[simp] theorem toEvenMixture_first (Ξ : RevisedCovariance) (q : ℝ) :
    Ξ.toEvenMixture.first q=Ξ.first q := by
  unfold FourPapersCommon.AdmissibleEvenMixture.first
  rw [tsum_eq_sum (s := Ξ.degrees) (fun p hp => by
    have hc : Ξ.coefficient p=0 := not_ne_iff.mp (by simpa using hp)
    simp [hc])]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [toEvenMixture_coefficient]
  ring

@[simp] theorem toEvenMixture_second (Ξ : RevisedCovariance) (q : ℝ) :
    Ξ.toEvenMixture.second q=Ξ.second q := by
  unfold FourPapersCommon.AdmissibleEvenMixture.second
  rw [tsum_eq_sum (s := Ξ.degrees) (fun p hp => by
    have hc : Ξ.coefficient p=0 := not_ne_iff.mp (by simpa using hp)
    simp [hc])]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [toEvenMixture_coefficient]
  ring

@[simp] theorem toEvenMixture_variance (Ξ : RevisedCovariance) :
    Ξ.toEvenMixture.variance=Ξ.variance := by
  simp only [FourPapersCommon.AdmissibleEvenMixture.variance,variance,toEvenMixture_first]

@[simp] theorem toEvenMixture_clock (Ξ : RevisedCovariance) (q : ℝ) :
    Ξ.toEvenMixture.clock q=Ξ.clock q := by
  simp only [FourPapersCommon.AdmissibleEvenMixture.clock,clock,toEvenMixture_first,
    toEvenMixture_variance]

def temperatureScale (Ξ : RevisedCovariance) (b : ℝ) (hb : b≠0) : RevisedCovariance :=
  ⟨Ξ.toEvenMixture.temperatureScale b hb, Ξ.property.subset (by
    intro p hp
    simp only [Function.mem_support,
      FourPapersCommon.AdmissibleEvenMixture.temperatureScale_coefficient] at hp ⊢
    intro hc
    change Ξ.toEvenMixture.coefficient p=0 at hc
    exact hp (by rw [hc,mul_zero]))⟩

@[simp] theorem toEvenMixture_temperatureScale (Ξ : RevisedCovariance) (b : ℝ) (hb : b≠0) :
    (Ξ.temperatureScale b hb).toEvenMixture=Ξ.toEvenMixture.temperatureScale b hb := rfl

theorem temperatureScale_value (Ξ : RevisedCovariance) (b : ℝ) (hb : b≠0) (q : ℝ) :
    (Ξ.temperatureScale b hb).value q=b^2*Ξ.value q := by
  rw [←toEvenMixture_value,toEvenMixture_temperatureScale,
    FourPapersCommon.AdmissibleEvenMixture.temperatureScale_value,toEvenMixture_value]

theorem temperatureScale_first (Ξ : RevisedCovariance) (b : ℝ) (hb : b≠0) (q : ℝ) :
    (Ξ.temperatureScale b hb).first q=b^2*Ξ.first q := by
  rw [←toEvenMixture_first,toEvenMixture_temperatureScale,
    FourPapersCommon.AdmissibleEvenMixture.temperatureScale_first,toEvenMixture_first]

theorem temperatureScale_second (Ξ : RevisedCovariance) (b : ℝ) (hb : b≠0) (q : ℝ) :
    (Ξ.temperatureScale b hb).second q=b^2*Ξ.second q := by
  rw [←toEvenMixture_second,toEvenMixture_temperatureScale,
    FourPapersCommon.AdmissibleEvenMixture.temperatureScale_second,toEvenMixture_second]

def addHighDegree (Ξ : RevisedCovariance) (p : ℕ) (hp : 4≤p) (he : Even p)
    (hn : p∉Ξ.degrees) (lam : ℝ) (hlam : 0<lam) : RevisedCovariance :=
  ⟨{
    coefficient j := if j=p then lam else Ξ.coefficient j
    nonneg j := by split_ifs;exact hlam.le;exact Ξ.coefficient_nonneg j
    active_even j hj := by
      by_cases hjp : j=p
      · subst j;exact ⟨by omega,he⟩
      · exact Ξ.toEvenMixture.active_even j (by
          simpa only [ite_eq_right hjp,coefficient] using hj)
    nonzero := ⟨p,by simpa using hlam⟩
    summable := summable_of_ne_finset_zero (s := insert p Ξ.degrees) (by
      intro j hj
      have hjp : j≠p := fun h => hj (h ▸ Finset.mem_insert_self p Ξ.degrees)
      have hjd : j∉Ξ.degrees := fun h => hj (Finset.mem_insert_of_mem h)
      have hc : Ξ.coefficient j=0 := not_ne_iff.mp (by simpa using hjd)
      simp [hjp,hc])
    }, (insert p Ξ.degrees).finite_toSet.subset (by
      intro j hj
      by_cases hjp : j=p
      · exact hjp ▸ Finset.mem_insert_self p Ξ.degrees
      · apply Finset.mem_insert_of_mem
        apply (Ξ.mem_degrees j).mpr
        simpa only [Function.mem_support,if_neg hjp] using hj)⟩

@[simp] theorem addHighDegree_coefficient (Ξ : RevisedCovariance) (p : ℕ) (hp : 4≤p)
    (he : Even p) (hn : p∉Ξ.degrees) (lam : ℝ) (hlam : 0<lam) (j : ℕ) :
    (Ξ.addHighDegree p hp he hn lam hlam).coefficient j=
      if j=p then lam else Ξ.coefficient j := rfl

@[simp] theorem addHighDegree_degrees (Ξ : RevisedCovariance) (p : ℕ) (hp : 4≤p)
    (he : Even p) (hn : p∉Ξ.degrees) (lam : ℝ) (hlam : 0<lam) :
    (Ξ.addHighDegree p hp he hn lam hlam).degrees=insert p Ξ.degrees := by
  ext j
  rw [mem_degrees,Finset.mem_insert,mem_degrees,addHighDegree_coefficient]
  by_cases hj : j=p <;> simp [hj,hlam.ne']

theorem addHighDegree_value (Ξ : RevisedCovariance) (p : ℕ) (hp : 4≤p)
    (he : Even p) (hn : p∉Ξ.degrees) (lam : ℝ) (hlam : 0<lam) (q : ℝ) :
    (Ξ.addHighDegree p hp he hn lam hlam).value q=Ξ.value q+lam*q^p := by
  rw [value,addHighDegree_degrees,Finset.sum_insert hn]
  simp only [addHighDegree_coefficient,ite_eq_left rfl]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [ite_eq_right (fun (hjp:j=p) => hn (hjp ▸ hj))]

theorem addHighDegree_first (Ξ : RevisedCovariance) (p : ℕ) (hp : 4≤p)
    (he : Even p) (hn : p∉Ξ.degrees) (lam : ℝ) (hlam : 0<lam) (q : ℝ) :
    (Ξ.addHighDegree p hp he hn lam hlam).first q=Ξ.first q+lam*(p:ℝ)*q^(p-1) := by
  rw [first,addHighDegree_degrees,Finset.sum_insert hn]
  simp only [addHighDegree_coefficient,ite_eq_left rfl]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [ite_eq_right (fun (hjp:j=p) => hn (hjp ▸ hj))]

theorem addHighDegree_second (Ξ : RevisedCovariance) (p : ℕ) (hp : 4≤p)
    (he : Even p) (hn : p∉Ξ.degrees) (lam : ℝ) (hlam : 0<lam) (q : ℝ) :
    (Ξ.addHighDegree p hp he hn lam hlam).second q=
      Ξ.second q+lam*(p:ℝ)*(p-1:ℕ)*q^(p-2) := by
  rw [second,addHighDegree_degrees,Finset.sum_insert hn]
  simp only [addHighDegree_coefficient,ite_eq_left rfl]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [ite_eq_right (fun (hjp:j=p) => hn (hjp ▸ hj))]

theorem addHighDegree_second_zero (Ξ : RevisedCovariance) (p : ℕ) (hp : 4≤p)
    (he : Even p) (hn : p∉Ξ.degrees) (lam : ℝ) (hlam : 0<lam) :
    (Ξ.addHighDegree p hp he hn lam hlam).second 0=Ξ.second 0 := by
  rw [addHighDegree_second]
  have hn2 : p-2≠0 := by omega
  simp [hn2]

theorem addHighDegree_isSubcritical (Ξ : RevisedCovariance) (p : ℕ) (hp : 4≤p)
    (he : Even p) (hn : p∉Ξ.degrees) (lam : ℝ) (hlam : 0<lam)
    (hsub : Ξ.IsSubcritical) : (Ξ.addHighDegree p hp he hn lam hlam).IsSubcritical := by
  simpa only [IsSubcritical,addHighDegree_second_zero] using hsub

end RevisedCovariance

namespace AdmissibleCovariance

def toRevisedCovariance (Ξ : AdmissibleCovariance) : RevisedCovariance :=
  ⟨Ξ.toEvenMixture, Ξ.degrees.finite_toSet.subset (by
    intro p hp
    by_contra hn
    change Ξ.toEvenMixture.coefficient p≠0 at hp
    have hn' : p∉Ξ.degrees := hn
    exact hp (by rw [toEvenMixture_coefficient,if_neg hn']))⟩

@[simp] theorem toRevisedCovariance_toEvenMixture (Ξ : AdmissibleCovariance) :
    Ξ.toRevisedCovariance.toEvenMixture=Ξ.toEvenMixture := rfl

@[simp] theorem toRevisedCovariance_value (Ξ : AdmissibleCovariance) (q : ℝ) :
    Ξ.toRevisedCovariance.value q=Ξ.value q := by
  rw [←RevisedCovariance.toEvenMixture_value,toRevisedCovariance_toEvenMixture,
    toEvenMixture_value]

@[simp] theorem toRevisedCovariance_first (Ξ : AdmissibleCovariance) (q : ℝ) :
    Ξ.toRevisedCovariance.first q=Ξ.first q := by
  rw [←RevisedCovariance.toEvenMixture_first,toRevisedCovariance_toEvenMixture,
    toEvenMixture_first]

@[simp] theorem toRevisedCovariance_second (Ξ : AdmissibleCovariance) (q : ℝ) :
    Ξ.toRevisedCovariance.second q=Ξ.second q := by
  rw [←RevisedCovariance.toEvenMixture_second,toRevisedCovariance_toEvenMixture,
    toEvenMixture_second]

theorem toRevisedCovariance_isSubcritical (Ξ : AdmissibleCovariance) :
    Ξ.toRevisedCovariance.IsSubcritical := by
  change Ξ.toRevisedCovariance.second 0<1
  rw [toRevisedCovariance_second,AdmissibleCovariance.second_zero]
  norm_num

end AdmissibleCovariance
end DepthPaper
