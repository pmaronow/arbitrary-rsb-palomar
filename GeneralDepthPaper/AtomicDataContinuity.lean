module

public import GeneralDepthPaper.TruncatedAtomicData
public import GeneralDepthPaper.SmoothCovarianceFamily

@[expose] public section


/-! Genuine compact covariance-jet and atomic-grid convergence for a smooth
finite polynomial covariance family. Every jet is an actual derivative. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace GeneralDepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

def monomialJetMap (p j : ℕ) : C(TruncatedClockDomain 1,ℝ) :=
  ⟨fun q=>(p.descFactorial j:ℝ)*(q:ℝ)^(p-j),by fun_prop⟩

theorem covarianceJetMap_eq_sum (Ξ : AdmissibleCovariance) (j : Fin 4) :
    covarianceJetMap Ξ j=∑p∈Ξ.degrees,Ξ.coefficient p • monomialJetMap p j := by
  ext q
  change iteratedDeriv (j:ℕ) (fun x=>∑p∈Ξ.degrees,Ξ.coefficient p*x^p) (q:ℝ)=_
  rw [iteratedDeriv_fun_sum (fun p _=>by fun_prop)]
  simp only [iteratedDeriv_const_mul_field,iteratedDeriv_pow,ContinuousMap.sum_apply,
    ContinuousMap.smul_apply,monomialJetMap,ContinuousMap.coe_mk,smul_eq_mul]

namespace SmoothCovarianceFamily
variable {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]

theorem continuousOn_covarianceJetMap (F : SmoothCovarianceFamily Θ) (j : Fin 4) :
    ContinuousOn (fun θ=>covarianceJetMap (F.covariance θ) j) F.domain := by
  have hraw : ContinuousOn (fun θ=>∑p∈F.degrees,(F.covariance θ).coefficient p • monomialJetMap p j)
      F.domain := by
    apply continuousOn_finsetSum
    intro p hp
    exact (F.smooth_coefficient p hp).continuousOn.smul continuousOn_const
  apply hraw.congr
  intro θ hθ
  change covarianceJetMap (F.covariance θ) j=∑p∈F.degrees,
    (F.covariance θ).coefficient p • monomialJetMap p j
  rw [covarianceJetMap_eq_sum,F.degrees_eq θ hθ]

theorem tendsto_covarianceJetMap (F : SmoothCovarianceFamily Θ) {θ : Θ}
    (hθ : θ∈F.domain) (θn : ℕ→Θ) (hθn : ∀n,θn n∈F.domain)
    (ht : Tendsto θn atTop (𝓝 θ)) (j : Fin 4) :
    Tendsto (fun n=>covarianceJetMap (F.covariance (θn n)) j) atTop
      (𝓝 (covarianceJetMap (F.covariance θ) j)) := by
  exact ((F.continuousOn_covarianceJetMap j).continuousAt (F.isOpen_domain.mem_nhds hθ)).tendsto.comp ht

theorem atomicTruncatedData_convergence (F : SmoothCovarianceFamily Θ) {θ : Θ}
    (hθ : θ∈F.domain) {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (θn : ℕ→Θ) (hθn : ∀n,θn n∈F.domain) (zN : ℕ→AtomicPoint r)
    (hzN : ∀n,IsAtomicPoint (zN n)) (hθt : Tendsto θn atTop (𝓝 θ))
    (hzt : Tendsto zN atTop (𝓝 z)) :
    TruncatedDataConvergence (fun n=>atomicTruncatedData (F.covariance (θn n)) (zN n) (hzN n))
      (atomicTruncatedData (F.covariance θ) z hz) := by
  constructor
  · intro j
    exact F.tendsto_covarianceJetMap hθ θn hθn hθt j
  · apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_subtype_rng.mpr
    exact (contDiff_atomicNode i).continuous.continuousAt.tendsto.comp hzt
  · apply tendsto_pi_nhds.mpr
    intro i
    exact (contDiff_atomicLevel i).continuous.continuousAt.tendsto.comp hzt
  · intro j
    exact tendsto_const_nhds

end SmoothCovarianceFamily
end GeneralDepthPaper
