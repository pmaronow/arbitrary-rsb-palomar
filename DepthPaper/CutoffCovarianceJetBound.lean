module

public import DepthPaper.CutoffData
public import DepthPaper.HighDegreeJetBounds
public import DepthPaper.CutoffRecursionDifferenceBound

@[expose] public section


/-! The restricted C³ covariance jets of the genuine added high-spin model
converge in the compact uniform norm. The exponentially small cutoff power
controls every jet, rather than only the finitely many recursion increments. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 800000

theorem cutoffCovarianceJetMap_highDegree_sub (Ξ : AdmissibleCovariance)
    (p : ℕ) (hp : 4≤p) (he : Even p) (hn : p∉Ξ.degrees)
    (lam : ℝ) (hlam : 0<lam) (qc : ℝ) (j : Fin 4)
    (q : TruncatedClockDomain qc) :
    (cutoffCovarianceJetMap (Ξ.addHighDegree p hp he hn lam hlam) qc j-
      cutoffCovarianceJetMap Ξ qc j) q=
      lam*iteratedDeriv j (fun x : ℝ=>x^p) q := by
  have hv : (Ξ.addHighDegree p hp he hn lam hlam).value=
      (fun x=>Ξ.value x+lam*x^p) := by
    funext x
    exact Ξ.addHighDegree_value p hp he hn lam hlam x
  change iteratedDeriv j (Ξ.addHighDegree p hp he hn lam hlam).value q-
    iteratedDeriv j Ξ.value q=_
  have hg : ContDiff ℝ ∞ (fun x : ℝ=>lam*x^p) := by fun_prop
  rw [hv,iteratedDeriv_fun_add
    (Ξ.contDiff_value.of_le (show (j:ℕ∞ω)≤∞ by simp)).contDiffAt
    (hg.of_le (show (j:ℕ∞ω)≤∞ by simp)).contDiffAt,
    iteratedDeriv_const_mul_field,add_sub_cancel_left]

theorem cutoffCovarianceJetMap_highDegree_bound (Ξ : AdmissibleCovariance)
    {qc L : ℝ} (hc : qc∈Ioo (0:ℝ) 1) (hL : 0≤L)
    (p : ℕ) (hp : 4≤p) (he : Even p) (hn : p∉Ξ.degrees)
    (lam : ℝ) (hlam : 0<lam) (hl : lam≤L) (j : Fin 4) :
    ‖cutoffCovarianceJetMap (Ξ.addHighDegree p hp he hn lam hlam) qc j-
      cutoffCovarianceJetMap Ξ qc j‖≤
      L*qc^(-(3:ℤ))*(p:ℝ)^3*Real.exp (Real.log qc*(p:ℝ)) := by
  have hz : 0≤qc^(-(3:ℤ)) := (zpow_pos hc.1 _).le
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro q
  rw [cutoffCovarianceJetMap_highDegree_sub,norm_mul,Real.norm_of_nonneg hlam.le]
  have H:=norm_iteratedDeriv_pow_cutoff p j hc.1.le q.property
  have hp1 : (1:ℝ)≤p := by exact_mod_cast (show 1≤p by omega)
  have hj : (j:ℕ)≤3 := by omega
  have hpow : (p:ℝ)^(j:ℕ)≤(p:ℝ)^3 := pow_le_pow_right₀ hp1 hj
  have hcut : qc^(p-(j:ℕ))≤qc^(p-3) :=
    pow_right_anti₀ hc.1.le hc.2.le (by omega)
  have HH:=mul_le_mul hl (H.trans (mul_le_mul hpow hcut
    (pow_nonneg hc.1.le _) (pow_nonneg (Nat.cast_nonneg p) _)))
    (norm_nonneg _) hL
  rw [pow_cutoff_exponential hc.1 p 3 (by omega)] at HH
  convert HH using 1 <;> ring

theorem tendsto_cutoffCovarianceJetMap_highDegree (Ξ : AdmissibleCovariance)
    {qc L : ℝ} (hc : qc∈Ioo (0:ℝ) 1) (hL : 0≤L)
    (p : ℕ→ℕ) (hp : ∀n,4≤p n) (he : ∀n,Even (p n))
    (hn : ∀n,p n∉Ξ.degrees) (lam : ℕ→ℝ) (hlam : ∀n,0<lam n)
    (hl : ∀n,lam n≤L) (ht : Tendsto p atTop atTop) (j : Fin 4) :
    Tendsto (fun n=>cutoffCovarianceJetMap
      (Ξ.addHighDegree (p n) (hp n) (he n) (hn n) (lam n) (hlam n)) qc j)
      atTop (𝓝 (cutoffCovarianceJetMap Ξ qc j)) := by
  have hb := fun n=>cutoffCovarianceJetMap_highDegree_bound Ξ hc hL
    (p n) (hp n) (he n) (hn n) (lam n) (hlam n) (hl n) j
  have hc' : 0< -Real.log qc := neg_pos.mpr (Real.log_neg hc.1 hc.2)
  have hz := (tendsto_nat_polynomial_exp (L*qc^(-(3:ℤ)))
    (-Real.log qc) 3 hc').comp ht
  have Hnorm : Tendsto (fun n=>‖cutoffCovarianceJetMap
      (Ξ.addHighDegree (p n) (hp n) (he n) (hn n) (lam n) (hlam n)) qc j-
        cutoffCovarianceJetMap Ξ qc j‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>norm_nonneg _) (fun n=>?_ ) hz
    simpa only [neg_neg,Function.comp_def] using hb n
  exact tendsto_iff_norm_sub_tendsto_zero.mpr Hnorm

end DepthPaper
