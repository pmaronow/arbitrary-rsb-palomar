module

public import DepthPaper.LimitingPressureCalculus

@[expose] public section


/-! Actual atomic reduced objectives and their genuine partial derivatives. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

def limitingAtomicPhi (Ξ : AdmissibleCovariance) (r : ℕ) (p : AtomicPoint r×ℝ) : ℝ :=
  atomicFunctionalExtension ((temperatureCovarianceFamily Ξ).covariance p.2) r p.1/p.2

def limitingAtomicObjective (Ξ : AdmissibleCovariance) (r : ℕ) (lam : ℝ)
    (p : AtomicPoint r×ℝ) : ℝ := limitingAtomicPhi Ξ r p+lam*p.2/2

theorem contDiffAt_limitingAtomicPhi (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : 0 < m) :
    ContDiffAt ℝ ∞ (limitingAtomicPhi Ξ r) (z,m) := by
  have hJ : ContDiffAt ℝ ∞
      (fun p:ℝ×AtomicPoint r=>atomicFunctionalExtension ((temperatureCovarianceFamily Ξ).covariance p.1) r p.2)
      (m,z) :=
    ((temperatureCovarianceFamily Ξ).finite_step_regularity r).contDiffAt
      ((isOpen_Ioi.prod (isOpen_atomic_domain r)).mem_nhds ⟨hm,hz⟩)
  have hswap:=hJ.comp (z,m) (contDiffAt_snd.prodMk contDiffAt_fst)
  exact hswap.div contDiffAt_snd hm.ne'

theorem contDiffAt_limitingAtomicObjective (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : 0 < m) (lam : ℝ) :
    ContDiffAt ℝ ∞ (limitingAtomicObjective Ξ r lam) (z,m) :=
  (contDiffAt_limitingAtomicPhi Ξ z hz m hm).add
    ((contDiffAt_const.mul contDiffAt_snd).div_const 2)

theorem fderiv_limitingAtomicPhi_locations (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : 0 < m) :
    fderiv ℝ (fun y=>limitingAtomicPhi Ξ r (y,m)) z=
      m⁻¹ • fderiv ℝ (atomicFunctionalExtension ((temperatureCovarianceFamily Ξ).covariance m) r) z := by
  have he:(fun y=>limitingAtomicPhi Ξ r (y,m))=
      fun y=>m⁻¹ • atomicFunctionalExtension ((temperatureCovarianceFamily Ξ).covariance m) r y := by
    funext y
    dsimp only [limitingAtomicPhi,smul_eq_mul]
    ring
  rw [he]
  exact ((contDiffAt_atomicFunctionalExtension _ z hz).differentiableAt (by norm_num)).hasFDerivAt.const_smul m⁻¹ |>.fderiv

theorem fderiv_limitingAtomicObjective_locations (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : 0 < m) (lam : ℝ) :
    fderiv ℝ (fun y=>limitingAtomicObjective Ξ r lam (y,m)) z=
      fderiv ℝ (fun y=>limitingAtomicPhi Ξ r (y,m)) z := by
  have hf : DifferentiableAt ℝ (fun y=>limitingAtomicPhi Ξ r (y,m)) z :=
    ((contDiffAt_limitingAtomicPhi Ξ z hz m hm).comp z
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by norm_num)
  exact (hf.hasFDerivAt.add_const (lam*m/2)).fderiv

theorem positive_limitingAtomicPhi_hessian (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : 0 < m)
    (hH : positiveAtomicHessian ((temperatureCovarianceFamily Ξ).covariance m) z) :
    ∀v:AtomicPoint r,v≠0→
      0 < (fderiv ℝ (fun y=>fderiv ℝ (fun w=>limitingAtomicPhi Ξ r (w,m)) y) z v) v := by
  have he : (fun y=>fderiv ℝ (fun w=>limitingAtomicPhi Ξ r (w,m)) y)=ᶠ[𝓝 z]
      (fun y=>m⁻¹ • fderiv ℝ (atomicFunctionalExtension ((temperatureCovarianceFamily Ξ).covariance m) r) y) := by
    filter_upwards [(isOpen_atomic_domain r).mem_nhds hz] with y hy
    exact fderiv_limitingAtomicPhi_locations Ξ y hy m hm
  have hd:=((contDiffAt_atomicFunctionalExtension
    ((temperatureCovarianceFamily Ξ).covariance m) z hz).fderiv_right (m:=∞) (by simp)).differentiableAt
    (by norm_num)
  have hh:=he.fderiv_eq.trans (hd.hasFDerivAt.const_smul m⁻¹).fderiv
  intro v hv
  rw [hh]
  change 0 < m⁻¹*(fderiv ℝ
    (fun y=>fderiv ℝ (atomicFunctionalExtension ((temperatureCovarianceFamily Ξ).covariance m) r) y) z v) v
  exact mul_pos (inv_pos.mpr hm) (hH v hv)

/-- Along a stationary branch, the genuine total derivative equals the
genuine partial parameter derivative with the atomic coordinates frozen. -/
theorem hasDerivAt_frozen_parameter_of_stationary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E×ℝ→ℝ) (z : ℝ→E) (m c : ℝ)
    (hf : DifferentiableAt ℝ f (z m,m)) (hz : DifferentiableAt ℝ z m)
    (hs : fderiv ℝ (fun y=>f (y,m)) (z m)=0)
    (ht : HasDerivAt (fun t=>f (z t,t)) c m) :
    HasDerivAt (fun t=>f (z m,t)) c m := by
  let L:=fderiv ℝ f (z m,m)
  have hpartial:=hf.hasFDerivAt.comp (z m)
    ((hasFDerivAt_id (𝕜:=ℝ) (z m)).prodMk (hasFDerivAt_const (𝕜:=ℝ) (x:=z m) m))
  have hp : L (deriv z m,0)=0 := by
    have he:=hpartial.fderiv
    change fderiv ℝ (fun y=>f (y,m)) (z m)=L ∘L
      (ContinuousLinearMap.id ℝ E).prod (0:E→L[ℝ]ℝ) at he
    rw [hs] at he
    have hev:=congrArg (fun T:E→L[ℝ]ℝ=>T (deriv z m)) he
    exact hev.symm
  have hchain:=hf.hasFDerivAt.comp_hasDerivAt (f:=fun t=>(z t,t)) m (hz.hasDerivAt.prodMk (hasDerivAt_id m))
  have hc : L (deriv z m,1)=c := hchain.unique ht
  have he : L (deriv z m,1)=L (0,1) := by
    rw [show (deriv z m,(1:ℝ))=(deriv z m,0)+(0,1) by simp,L.map_add,hp,zero_add]
  exact (hf.hasFDerivAt.comp_hasDerivAt m
    ((hasDerivAt_const m (z m)).prodMk (hasDerivAt_id m))).congr_deriv (he.symm.trans hc)

end DepthPaper
