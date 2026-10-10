module

public import DepthPaper.AtomicVariationContinuity
public import DepthPaper.Nondegeneracy

@[expose] public section


/-! Actual stationary atomic gradients, their contact equations, and the
smooth parameterized gradient used in the nondegenerate stability theorem. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem fderiv_atomicFunctional_eq_zero_of_minimizer (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (hmin : IsParisiMinimizer Ξ (atomicMeasure z hz)) :
    fderiv ℝ (atomicFunctionalExtension Ξ r) z=0 := by
  apply IsLocalMin.fderiv_eq_zero
  filter_upwards [(isOpen_atomic_domain r).mem_nhds hz] with y hy
  rw [atomicFunctionalExtension_eq Ξ z hz,atomicFunctionalExtension_eq Ξ y hy]
  exact hmin (atomicMeasure y hy)

theorem atomic_stationary_contacts (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (hs : fderiv ℝ (atomicFunctionalExtension Ξ r) z=0) :
    (∀i : Fin (r+1),firstVariation Ξ (atomicMeasure z hz) (atomicLocation z i)=0) ∧
    (∀i : Fin r,deriv (firstVariation Ξ (atomicMeasure z hz)) (z.1 i)=0) := by
  let Q:Overlap:=⟨(atomicLocation z (Fin.last r)+1)/2,
    ⟨by linarith [(atomicLocation_mem_unit hz (Fin.last r)).1],by linarith [hz.2.1]⟩⟩
  have hQ : atomicLocation z (Fin.last r)<(Q:ℝ) ∧ (Q:ℝ)<1 := by
    dsimp only [Q];constructor <;> linarith [hz.2.1]
  have he : partialAtomicFunctionalExtension Ξ r 1 Q =ᶠ[𝓝 z] atomicFunctionalExtension Ξ r := by
    filter_upwards [(isOpen_atomic_domain r).mem_nhds hz] with y hy
    rw [partialAtomicFunctionalExtension,partialAtomicMeasureExtension_eq y hy,
      partialAtomicMeasure,Paper.parisiMix_one,atomicFunctionalExtension_eq Ξ y hy]
  have hzero : fderiv ℝ (partialAtomicFunctionalExtension Ξ r 1 Q) z=0 :=
    he.fderiv_eq.trans hs
  have hh := (atomic_gradient_zero_iff Ξ z hz 1 ⟨by norm_num,le_rfl⟩ Q hQ).mp hzero
  simp only [partialAtomicMeasure,Paper.parisiMix_one] at hh
  constructor
  · intro i
    exact hh.1 (atomicOverlap z hz i) (by rw [support_atomicMeasure];exact ⟨i,rfl⟩)
  · intro i
    have hn : atomicOverlap z hz i.succ≠⟨0,by norm_num⟩ := by
      intro h
      have heq:=congrArg (fun q:Overlap=>(q:ℝ)) h
      have hp:=hz.1 (Fin.succ_pos i)
      simp only [atomicOverlap,atomicLocation_zero,atomicLocation_succ] at heq hp
      linarith
    have hq : z.1 i∈Ioo (0:ℝ) 1 :=
      ⟨by simpa only [atomicLocation_zero,atomicLocation_succ] using hz.1 (Fin.succ_pos i),
        (hz.1.monotone (Fin.le_last i.succ)).trans_lt hz.2.1⟩
    rw [(hasDerivAt_firstVariation Ξ (atomicMeasure z hz) hq).deriv]
    exact hh.2 (atomicOverlap z hz i.succ) (by rw [support_atomicMeasure];exact ⟨i.succ,rfl⟩) hn

def atomicGradientFamily {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
    (F : SmoothCovarianceFamily Θ) (r : ℕ) (p : Θ×AtomicPoint r) : AtomicPoint r→L[ℝ]ℝ :=
  fderiv ℝ (atomicFunctionalExtension (F.covariance p.1) r) p.2

namespace SmoothCovarianceFamily
variable {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]

theorem contDiffAt_atomicGradientFamily (F : SmoothCovarianceFamily Θ) {r : ℕ}
    {θ : Θ} (hθ : θ∈F.domain) (z : AtomicPoint r) (hz : IsAtomicPoint z) :
    ContDiffAt ℝ ∞ (atomicGradientFamily F r) (θ,z) := by
  have hJ : ContDiffAt ℝ ∞
      (fun p:Θ×AtomicPoint r=>atomicFunctionalExtension (F.covariance p.1) r p.2) (θ,z) :=
    (F.finite_step_regularity r).contDiffAt
    ((F.isOpen_domain.prod (isOpen_atomic_domain r)).mem_nhds ⟨hθ,hz⟩)
  have hL : ContDiffAt ℝ ∞
      (fun w:(Θ×AtomicPoint r)×AtomicPoint r=>atomicFunctionalExtension (F.covariance w.1.1) r w.2)
      ((θ,z),z) := hJ.comp ((θ,z),z) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  exact hL.fderiv contDiffAt_snd (by simp)

theorem atomicGradientFamily_partial_hessian (F : SmoothCovarianceFamily Θ) {r : ℕ}
    {θ : Θ} (hθ : θ∈F.domain) (z : AtomicPoint r) (hz : IsAtomicPoint z) :
    fderiv ℝ (atomicGradientFamily F r) (θ,z) ∘L ContinuousLinearMap.inr ℝ Θ (AtomicPoint r)=
      fderiv ℝ (fun y=>fderiv ℝ (atomicFunctionalExtension (F.covariance θ) r) y) z := by
  have hG := (F.contDiffAt_atomicGradientFamily hθ z hz).differentiableAt (by norm_num)
  have hp:= (hasFDerivAt_const (𝕜:=ℝ) (x:=z) θ).prodMk (hasFDerivAt_id (𝕜:=ℝ) z)
  have hc:=hG.hasFDerivAt.comp z hp
  have he : (ContinuousLinearMap.prod (0 : AtomicPoint r→L[ℝ]Θ)
      (ContinuousLinearMap.id ℝ (AtomicPoint r)))=ContinuousLinearMap.inr ℝ Θ (AtomicPoint r) := rfl
  simpa only [Function.comp_def,atomicGradientFamily,he] using hc.fderiv.symm

end SmoothCovarianceFamily
end DepthPaper
