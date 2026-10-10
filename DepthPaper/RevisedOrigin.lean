module

public import DepthPaper.RevisedModel

@[expose] public section

/-! Uniform origin control for the revised admissibility condition ξ″(0)<1.
The quadratic contribution is retained explicitly; all higher even orders
have cubic suppression. The constants are uniform over every probability
measure and every covariance with the stated two numerical bounds. -/
noncomputable section
open Set
open scoped BigOperators
namespace DepthPaper.RevisedCovariance

set_option maxHeartbeats 500000

theorem first_eq_quadratic_add_higher (Ξ : RevisedCovariance) (q : ℝ) :
    Ξ.first q = Ξ.second 0*q +
      ∑p ∈ Ξ.degrees.erase 2, Ξ.coefficient p*(p:ℝ)*q^(p-1) := by
  rw [second_zero]
  unfold first
  by_cases h2 : 2∈Ξ.degrees
  · rw [←Finset.sum_erase_add _ _ h2]
    norm_num
    ring
  · rw [Finset.erase_eq_self.mpr h2]
    have hc : Ξ.coefficient 2=0 := not_ne_iff.mp (by simpa using h2)
    simp [hc]

theorem first_le_quadratic_add_cubic (Ξ : RevisedCovariance)
    {q : ℝ} (hq : q∈Icc (0:ℝ) (1/2)) :
    Ξ.first q ≤ Ξ.second 0*q + (2*q)^3*Ξ.first (1/2) := by
  have hh : (∑p ∈ Ξ.degrees.erase 2, Ξ.coefficient p*(p:ℝ)*q^(p-1)) ≤
      (2*q)^3*(∑p ∈ Ξ.degrees.erase 2, Ξ.coefficient p*(p:ℝ)*(1/2:ℝ)^(p-1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hp' : p∈Ξ.degrees := Finset.mem_of_mem_erase hp
    have hpn : p≠2 := (Finset.mem_erase.mp hp).1
    have hge : 4≤p := by
      have htwo := Ξ.degree_ge_two p hp'
      rcases Ξ.degree_even p hp' with ⟨k,hk⟩
      omega
    have hn : 3≤p-1 := by omega
    have hbase0 : 0≤2*q := by linarith [hq.1]
    have hbase1 : 2*q≤1 := by linarith [hq.2]
    have hb := pow_le_pow_of_le_one hbase0 hbase1 hn
    have he : q^(p-1)=(1/2:ℝ)^(p-1)*(2*q)^(p-1) := by
      rw [←mul_pow]
      congr 1
      ring
    rw [he]
    have hc : 0≤Ξ.coefficient p*(p:ℝ)*(1/2:ℝ)^(p-1) := by
      exact mul_nonneg (mul_nonneg (Ξ.coefficient_pos p hp').le (Nat.cast_nonneg _))
        (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hb hc]
  have hhalf : (∑p ∈ Ξ.degrees.erase 2, Ξ.coefficient p*(p:ℝ)*(1/2:ℝ)^(p-1)) ≤
      Ξ.first (1/2) := by
    rw [Ξ.first_eq_quadratic_add_higher (1/2)]
    have hn : 0≤Ξ.second 0 := Ξ.second_nonneg le_rfl
    linarith
  rw [Ξ.first_eq_quadratic_add_higher q]
  exact add_le_add le_rfl (hh.trans
    (mul_le_mul_of_nonneg_left hhalf (pow_nonneg (by linarith [hq.1]) _)))

def subcriticalOriginRadius (a C : ℝ) : ℝ :=
  min (1/2) (Real.sqrt ((1-a)/(16*C)))

theorem subcriticalOriginRadius_pos {a C : ℝ} (ha : a<1) (hC : 0<C) :
    0<subcriticalOriginRadius a C := by
  exact lt_min (by norm_num) (Real.sqrt_pos.mpr (by positivity))

theorem first_le_subcritical_overlap (Ξ : RevisedCovariance)
    {a C q : ℝ} (ha : Ξ.second 0≤a) (ha1 : a<1) (hC : Ξ.first (1/2)≤C)
    (hq : q∈Icc (0:ℝ) (subcriticalOriginRadius a C)) :
    Ξ.first q ≤ ((1+a)/2)*q := by
  have hCp : 0<C := (Ξ.first_pos (by norm_num : (0:ℝ)<1/2)).trans_le hC
  have hqhalf : q≤1/2 := hq.2.trans (min_le_left _ _)
  have hs : 0≤(1-a)/(16*C) := by positivity
  have hqroot : q≤Real.sqrt ((1-a)/(16*C)) := hq.2.trans (min_le_right _ _)
  have hqsq := pow_le_pow_left₀ hq.1 hqroot 2
  rw [Real.sq_sqrt hs] at hqsq
  have hh := (le_div_iff₀ (by positivity : 0<16*C)).mp hqsq
  have hf := Ξ.first_le_quadratic_add_cubic ⟨hq.1,hqhalf⟩
  have hlin := mul_le_mul_of_nonneg_right ha hq.1
  have hcub := mul_le_mul_of_nonneg_left hC
    (pow_nonneg (by linarith [hq.1] : 0≤2*q) 3)
  have hm := mul_le_mul_of_nonneg_left hh hq.1
  nlinarith

theorem Gamma_le_subcritical_overlap (Ξ : RevisedCovariance) (μ : ParisiMeasure)
    {a C q : ℝ} (ha : Ξ.second 0≤a) (ha1 : a<1) (hC : Ξ.first (1/2)≤C)
    (hq : q∈Icc (0:ℝ) (subcriticalOriginRadius a C)) :
    Gamma Ξ μ q ≤ ((1+a)/2)*q := by
  have hqone : q≤1 := (hq.2.trans (min_le_left _ _)).trans (by norm_num)
  exact (Gamma_le_first Ξ μ ⟨hq.1,hqone⟩).trans
    (Ξ.first_le_subcritical_overlap ha ha1 hC hq)

theorem deriv_firstVariation_neg_near_origin (Ξ : RevisedCovariance) (μ : ParisiMeasure)
    {a C q : ℝ} (ha : Ξ.second 0≤a) (ha1 : a<1) (hC : Ξ.first (1/2)≤C)
    (hq : q∈Ioc (0:ℝ) (subcriticalOriginRadius a C)) :
    deriv (firstVariation Ξ μ) q<0 := by
  have hqhalf : q≤1/2 := hq.2.trans (min_le_left _ _)
  rw [(hasDerivAt_firstVariation Ξ μ ⟨hq.1,by linarith⟩).deriv]
  have hG := Gamma_le_subcritical_overlap Ξ μ ha ha1 hC ⟨hq.1.le,hq.2⟩
  have hm : ((1+a)/2)*q<q := by nlinarith [hq.1]
  exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) (Ξ.second_pos hq.1))
    (by linarith)

theorem firstVariation_neg_near_origin (Ξ : RevisedCovariance) (μ : ParisiMeasure)
    {a C q : ℝ} (ha : Ξ.second 0≤a) (ha1 : a<1) (hC : Ξ.first (1/2)≤C)
    (hq : q∈Ioc (0:ℝ) (subcriticalOriginRadius a C)) :
    firstVariation Ξ μ q<0 := by
  have hCp : 0<C := (Ξ.first_pos (by norm_num : (0:ℝ)<1/2)).trans_le hC
  have hR := subcriticalOriginRadius_pos ha1 hCp
  have hm : StrictAntiOn (firstVariation Ξ μ) (Icc (0:ℝ) (subcriticalOriginRadius a C)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      ((continuousOn_firstVariation Ξ μ).mono (Icc_subset_Icc_right
        ((min_le_left _ _).trans (by norm_num : (1/2:ℝ)≤1))))
    intro s hs
    rw [interior_Icc] at hs
    exact deriv_firstVariation_neg_near_origin Ξ μ ha ha1 hC ⟨hs.1,hs.2.le⟩
  simpa only [firstVariation_zero] using
    hm ⟨le_rfl,hR.le⟩ ⟨hq.1.le,hq.2⟩ hq.1

/-- Lemma 2.2's genuine uniform origin clause for every revised admissible
covariance and every probability measure. -/
theorem exists_uniform_origin_margin (Ξ : RevisedCovariance) (hsub : Ξ.IsSubcritical) :
    ∃ε:ℝ,ε∈Ioo (0:ℝ) 1 ∧ ∃δ:ℝ,δ∈Ioo (0:ℝ) 1 ∧
      ∀μ:ParisiMeasure,
        (∀q∈Icc (0:ℝ) δ,Gamma Ξ μ q≤(1-ε)*q) ∧
        (∀q∈Ioc (0:ℝ) δ,firstVariation Ξ μ q<0) := by
  let ε := (1-Ξ.second 0)/2
  let δ := subcriticalOriginRadius (Ξ.second 0) (Ξ.first (1/2))
  have hn : 0≤Ξ.second 0 := Ξ.second_nonneg le_rfl
  have he : ε∈Ioo (0:ℝ) 1 := by dsimp only [ε];change Ξ.second 0<1 at hsub;constructor <;> linarith
  have hd : δ∈Ioo (0:ℝ) 1 := by
    refine ⟨subcriticalOriginRadius_pos hsub (Ξ.first_pos (by norm_num)),?_⟩
    exact (min_le_left _ _).trans_lt (by norm_num)
  refine ⟨ε,he,δ,hd,?_⟩
  intro μ
  constructor
  · intro q hq
    have H := Gamma_le_subcritical_overlap Ξ μ le_rfl hsub le_rfl hq
    convert H using 1 <;> dsimp only [ε] <;> ring
  · intro q hq
    exact firstVariation_neg_near_origin Ξ μ le_rfl hsub le_rfl hq

def highDegreeOriginBound (Ξ : RevisedCovariance) (L : ℝ) : ℝ := Ξ.first (1/2)+2*L

theorem highDegreeOriginBound_pos (Ξ : RevisedCovariance) {L : ℝ} (hL : 0≤L) :
    0<highDegreeOriginBound Ξ L := by
  have hf := Ξ.first_pos (by norm_num : (0:ℝ)<1/2)
  dsimp only [highDegreeOriginBound]
  linarith

theorem nat_mul_half_pow_sub_one_le_two (p : ℕ) (hp : 1≤p) :
    (p:ℝ)*(1/2:ℝ)^(p-1)≤2 := by
  have hn : (p:ℝ)≤(2:ℝ)^p := by exact_mod_cast p.lt_two_pow_self.le
  have he : (2:ℝ)^p=2*(2:ℝ)^(p-1) := by
    conv_lhs => rw [show p=(p-1)+1 by omega]
    rw [pow_succ]
    ring
  have hh := mul_le_mul_of_nonneg_right hn (pow_nonneg (by norm_num : (0:ℝ)≤1/2) (p-1))
  rw [he] at hh
  have hid : 2*(2:ℝ)^(p-1)*(1/2:ℝ)^(p-1)=2 := by
    rw [mul_assoc,←mul_pow]
    norm_num
  exact hh.trans_eq hid

theorem highDegree_first_half_le (Ξ : RevisedCovariance)
    (p : ℕ) (hp : 4≤p) (he : Even p) (hn : p∉Ξ.degrees)
    (lam : ℝ) (hlam : 0<lam) {L : ℝ} (hl : lam≤L) :
    (Ξ.addHighDegree p hp he hn lam hlam).first (1/2)≤highDegreeOriginBound Ξ L := by
  rw [Ξ.addHighDegree_first]
  have hb := nat_mul_half_pow_sub_one_le_two p (by omega)
  have hL : 0≤L := hlam.le.trans hl
  have hh := mul_le_mul hl hb (by positivity : 0≤(p:ℝ)*(1/2:ℝ)^(p-1)) hL
  dsimp only [highDegreeOriginBound]
  nlinarith

/-- One radius and one strict magnetization margin work for every positive
bounded high-degree perturbation, including every probability measure. -/
theorem highDegree_uniform_origin (Ξ : RevisedCovariance) (hsub : Ξ.IsSubcritical)
    {L : ℝ} (hL : 0≤L) (p : ℕ) (hp : 4≤p) (he : Even p) (hn : p∉Ξ.degrees)
    (lam : ℝ) (hlam : 0<lam) (hl : lam≤L) (μ : ParisiMeasure) :
    let Ψ := Ξ.addHighDegree p hp he hn lam hlam
    let δ := subcriticalOriginRadius (Ξ.second 0) (highDegreeOriginBound Ξ L)
    (∀q∈Icc (0:ℝ) δ,Gamma Ψ μ q≤((1+Ξ.second 0)/2)*q) ∧
    (∀q∈Ioc (0:ℝ) δ,firstVariation Ψ μ q<0) := by
  let Ψ := Ξ.addHighDegree p hp he hn lam hlam
  have ha : Ψ.second 0≤Ξ.second 0 := (Ξ.addHighDegree_second_zero p hp he hn lam hlam).le
  have hC := Ξ.highDegree_first_half_le p hp he hn lam hlam hl
  exact ⟨fun q hq=>Gamma_le_subcritical_overlap Ψ μ ha hsub hC hq,
    fun q hq=>firstVariation_neg_near_origin Ψ μ ha hsub hC hq⟩

end DepthPaper.RevisedCovariance
