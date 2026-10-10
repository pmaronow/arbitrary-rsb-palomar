module

public import DepthPaper.TruncatedAtomicMoments
public import DepthPaper.AtomicDataContinuity
public import DepthPaper.ContactPerturbation

@[expose] public section


/-! Genuine closed-interval C² continuity of the selected atomic first
variation under a smooth finite-polynomial covariance family. -/
noncomputable section
open Set Filter
open scoped Topology
namespace DepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem contDiffOn_firstVariation_atomicMeasure (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) :
    ContDiffOn ℝ 2 (firstVariation Ξ (atomicMeasure z hz)) (Icc (0:ℝ) 1) := by
  exact (atomicTruncatedData Ξ z hz).contDiffOn_firstVariation.congr
    (fun q hq=>firstVariation_atomicMeasure_eq_truncated Ξ z hz q hq)

theorem closedJet_firstVariation_atomicMeasure (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (j : Fin 3)
    (q : ℝ) (hq : q∈Icc (0:ℝ) 1) :
    closedJet 1 j (firstVariation Ξ (atomicMeasure z hz)) q=
      (atomicTruncatedData Ξ z hz).firstVariationJets j ⟨q,hq⟩ := by
  let d:=atomicTruncatedData Ξ z hz
  have hu : UniqueDiffOn ℝ (Icc (0:ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  have h0 : EqOn (firstVariation Ξ (atomicMeasure z hz)) d.firstVariation (Icc (0:ℝ) 1) :=
    fun t ht=>firstVariation_atomicMeasure_eq_truncated Ξ z hz t ht
  have h1 : EqOn (derivWithin (firstVariation Ξ (atomicMeasure z hz)) (Icc (0:ℝ) 1))
      d.firstVariationPrime (Icc (0:ℝ) 1) := by
    intro t ht
    exact ((d.hasDerivAt_firstVariation t).hasDerivWithinAt.congr h0 (h0 ht)).derivWithin (hu t ht)
  fin_cases j
  · exact h0 hq
  · change derivWithin (firstVariation Ξ (atomicMeasure z hz)) (Icc (0:ℝ) 1) q=
      d.firstVariationPrimeMap ⟨q,hq⟩
    rw [TruncatedParisiData.firstVariationPrimeMap_apply]
    exact h1 hq
  · change derivWithin (derivWithin (firstVariation Ξ (atomicMeasure z hz)) (Icc (0:ℝ) 1))
      (Icc (0:ℝ) 1) q=d.firstVariationSecondMap ⟨q,hq⟩
    rw [TruncatedParisiData.firstVariationSecondMap_apply]
    exact ((d.hasDerivWithinAt_firstVariationPrime q hq).congr h1 (h1 hq)).derivWithin (hu q hq)

namespace SmoothCovarianceFamily
variable {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]

theorem firstVariation_atomic_C2_convergence (F : SmoothCovarianceFamily Θ) {θ : Θ}
    (hθ : θ∈F.domain) {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (θn : ℕ→Θ) (hθn : ∀n,θn n∈F.domain) (zN : ℕ→AtomicPoint r)
    (hzN : ∀n,IsAtomicPoint (zN n)) (hθt : Tendsto θn atTop (𝓝 θ))
    (hzt : Tendsto zN atTop (𝓝 z)) :
    ∀j≤2,TendstoUniformlyOn
      (fun n=>closedJet 1 j (firstVariation (F.covariance (θn n)) (atomicMeasure (zN n) (hzN n))))
      (closedJet 1 j (firstVariation (F.covariance θ) (atomicMeasure z hz)))
      atTop (Icc (0:ℝ) 1) := by
  have hc:=F.atomicTruncatedData_convergence hθ z hz θn hθn zN hzN hθt hzt
  have ht:=hc.firstVariation_C2
  intro j hj
  let jj:Fin 3:=⟨j,by omega⟩
  have hJ:= (tendsto_pi_nhds.mp ht) jj
  have hn : Tendsto (fun n=>‖(atomicTruncatedData (F.covariance (θn n)) (zN n) (hzN n)).firstVariationJets jj-
      (atomicTruncatedData (F.covariance θ) z hz).firstVariationJets jj‖) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero] using (hJ.sub
      (tendsto_const_nhds (x:=(atomicTruncatedData (F.covariance θ) z hz).firstVariationJets jj))).norm
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hn.eventually (eventually_lt_nhds hε)] with n hne
  intro q hq
  rw [Real.dist_eq,←Real.norm_eq_abs]
  rw [show j=(jj:ℕ) from rfl,
    closedJet_firstVariation_atomicMeasure _ (zN n) (hzN n) jj q hq,
    closedJet_firstVariation_atomicMeasure _ z hz jj q hq]
  rw [norm_sub_rev]
  exact (ContinuousMap.norm_coe_le_norm
    ((atomicTruncatedData (F.covariance (θn n)) (zN n) (hzN n)).firstVariationJets jj-
      (atomicTruncatedData (F.covariance θ) z hz).firstVariationJets jj) ⟨q,hq⟩).trans_lt hne

end SmoothCovarianceFamily
end DepthPaper
