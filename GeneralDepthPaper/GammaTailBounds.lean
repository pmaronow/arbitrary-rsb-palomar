module

public import GeneralDepthPaper.Curvature
public import GeneralDepthPaper.HighDegreeModel

@[expose] public section


/-! Actual monotonicity and a uniform upper-overlap slope estimate.
These supporting results retain the genuine selected diffusion in Γ. -/
noncomputable section
open Set
namespace GeneralDepthPaper
set_option maxHeartbeats 600000

theorem Gamma_monotoneOn (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) :
    MonotoneOn (Gamma Ξ μ) (Icc (0:ℝ) 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) (continuousOn_Gamma Ξ μ)
    (f':=GammaPrime Ξ μ)
  · intro q hq
    rw [interior_Icc] at hq
    exact (hasDerivAt_Gamma Ξ μ hq).hasDerivWithinAt
  · intro q hq
    rw [interior_Icc] at hq
    exact GammaPrime_nonneg Ξ μ ⟨hq.1.le,hq.2.le⟩

theorem AdmissibleCovariance.second_le_endpoint (Ξ : AdmissibleCovariance)
    {q : ℝ} (hq : q∈Icc (0:ℝ) 1) : Ξ.second q≤Ξ.second 1 := by
  unfold AdmissibleCovariance.second
  apply Finset.sum_le_sum
  intro p hp
  simp only [one_pow,mul_one]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ hq.1 hq.2 (n:=p-2))
    (mul_nonneg (mul_nonneg (Ξ.coefficient_pos p hp).le (Nat.cast_nonneg p)) (Nat.cast_nonneg (p-1)))

theorem highDegree_second_uniform_bound (Ξ : AdmissibleCovariance) (p : ℕ)
    (hp : 4≤p) (he : Even p) (hn : p∉Ξ.degrees) {lam L : ℝ}
    (hlam : 0 < lam) (hL : lam≤L) {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    (Ξ.addHighDegree p hp he hn lam hlam).second q≤(Ξ.second 1+L)*(p:ℝ)^2 := by
  rw [Ξ.addHighDegree_second]
  have hb:=Ξ.second_le_endpoint hq
  have hpow:=pow_le_one₀ hq.1 hq.2 (n:=p-2)
  have hn' : ((p-1:ℕ):ℝ)≤(p:ℝ) := by exact_mod_cast Nat.sub_le p 1
  have hpp : 1≤(p:ℝ)^2 := by
    have hh : 1≤(p:ℝ) := by exact_mod_cast (show 1≤p by omega)
    nlinarith
  have hl0 : 0≤L:=hlam.le.trans hL
  have hmul:=mul_le_mul_of_nonneg_left hpow
    (show 0≤lam*(p:ℝ)*((p-1:ℕ):ℝ) by positivity)
  have hm:=mul_le_mul_of_nonneg_left hn' (show 0≤lam*(p:ℝ) by positivity)
  have hl:=mul_le_mul_of_nonneg_right hL (sq_nonneg (p:ℝ))
  have hbase:=mul_le_mul_of_nonneg_left hpp (Ξ.second_nonneg (by norm_num : (0:ℝ)≤1))
  nlinarith

theorem GammaPrime_tail_bound (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    {q0 q δ : ℝ} (h0 : q0∈Icc (0:ℝ) 1) (hq : q∈Icc q0 1)
    (hδ : 1-Gamma Ξ μ q0≤δ) : GammaPrime Ξ μ q≤Ξ.second 1*δ := by
  have hqu : q∈Icc (0:ℝ) 1 := ⟨h0.1.trans hq.1,hq.2⟩
  have hmon:=Gamma_monotoneOn Ξ μ h0 hqu hq.1
  have hg : 0≤1-Gamma Ξ μ q := sub_nonneg.mpr (Gamma_le_one Ξ μ q)
  have hd : 1-Gamma Ξ μ q≤δ := by linarith
  apply (GammaPrime_le Ξ μ hqu).trans
  exact mul_le_mul (Ξ.second_le_endpoint hqu) hd hg
    (Ξ.second_nonneg (by norm_num : (0:ℝ)≤1))

theorem highDegree_GammaPrime_tail_bound (Ξ : AdmissibleCovariance) (p : ℕ)
    (hp : 4≤p) (he : Even p) (hn : p∉Ξ.degrees) {lam L : ℝ}
    (hlam : 0 < lam) (hL : lam≤L) (μ : ParisiMeasure)
    {q0 q δ : ℝ} (h0 : q0∈Icc (0:ℝ) 1) (hq : q∈Icc q0 1)
    (hδ : 1-Gamma (Ξ.addHighDegree p hp he hn lam hlam) μ q0≤δ) :
    GammaPrime (Ξ.addHighDegree p hp he hn lam hlam) μ q≤(Ξ.second 1+L)*(p:ℝ)^2*δ := by
  have hd : 0≤δ := (sub_nonneg.mpr (Gamma_le_one _ μ q0)).trans hδ
  exact (GammaPrime_tail_bound _ μ h0 hq hδ).trans
    (mul_le_mul_of_nonneg_right (highDegree_second_uniform_bound Ξ p hp he hn hlam hL
      (by norm_num : (1:ℝ)∈Icc (0:ℝ) 1)) hd)

end GeneralDepthPaper
