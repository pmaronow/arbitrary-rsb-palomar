module

public import GeneralDepthPaper.AtomicPotentialRegularity

@[expose] public section


/-! Literal smooth finite-polynomial covariance families and joint regularity
of their actual atomic Parisi functional. Only smoothness of the finitely many
coefficient functions is part of the family data. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators ContDiff BoundedContinuousFunction
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000
universe u
variable (Θ:Type u) [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]

structure SmoothCovarianceFamily where
  domain : Set Θ
  isOpen_domain : IsOpen domain
  covariance : Θ→AdmissibleCovariance
  degrees : Finset ℕ
  degrees_eq : ∀θ∈domain,(covariance θ).degrees=degrees
  smooth_coefficient : ∀p∈degrees,ContDiffOn ℝ ∞ (fun θ=> (covariance θ).coefficient p) domain

variable {Θ}
namespace SmoothCovarianceFamily

theorem contDiffAt_second (F : SmoothCovarianceFamily Θ) {θ : Θ}
    (hθ : θ ∈ F.domain) (q : ℝ) :
    ContDiffAt ℝ ∞ (fun w : Θ × ℝ => (F.covariance w.1).second w.2) (θ, q) := by
  have hraw : ContDiffAt ℝ ∞ (fun w : Θ × ℝ => ∑ p ∈ F.degrees,
      (F.covariance w.1).coefficient p * (p : ℝ) * ((p - 1 : ℕ) : ℝ) *
        w.2 ^ (p - 2)) (θ, q) := by
    apply ContDiffAt.sum
    intro p hp
    have hc := (F.smooth_coefficient p hp).contDiffAt (F.isOpen_domain.mem_nhds hθ)
    exact (((hc.comp (θ, q) contDiffAt_fst).mul contDiffAt_const).mul
      contDiffAt_const).mul (contDiffAt_snd.pow (p - 2))
  apply hraw.congr_of_eventuallyEq
  have he : ∀ᶠ w : Θ × ℝ in 𝓝 (θ, q), w.1 ∈ F.domain :=
    continuous_fst.continuousAt (F.isOpen_domain.mem_nhds hθ)
  filter_upwards [he] with w hw
  unfold AdmissibleCovariance.second
  rw [F.degrees_eq w.1 hw]

theorem contDiffAt_first (F:SmoothCovarianceFamily Θ) {θ:Θ} (hθ:θ∈F.domain) (q:ℝ) :
    ContDiffAt ℝ ∞ (fun p:Θ×ℝ=>(F.covariance p.1).first p.2) (θ,q) := by
  have hraw : ContDiffAt ℝ ∞ (fun w:Θ×ℝ=>∑p∈F.degrees,
      (F.covariance w.1).coefficient p*(p:ℝ)*w.2^(p-1)) (θ,q) := by
    apply ContDiffAt.sum
    intro p hp
    have hc := (F.smooth_coefficient p hp).contDiffAt (F.isOpen_domain.mem_nhds hθ)
    exact ((hc.comp (θ,q) contDiffAt_fst).mul contDiffAt_const).mul (contDiffAt_snd.pow (p-1))
  apply hraw.congr_of_eventuallyEq
  have he : ∀ᶠw:Θ×ℝ in 𝓝 (θ,q),w.1∈F.domain :=
    continuous_fst.continuousAt (F.isOpen_domain.mem_nhds hθ)
  filter_upwards [he] with w hw
  unfold AdmissibleCovariance.first
  rw [F.degrees_eq w.1 hw]

theorem contDiffAt_value (F:SmoothCovarianceFamily Θ) {θ:Θ} (hθ:θ∈F.domain) (q:ℝ) :
    ContDiffAt ℝ ∞ (fun p:Θ×ℝ=>(F.covariance p.1).value p.2) (θ,q) := by
  have hraw : ContDiffAt ℝ ∞ (fun w:Θ×ℝ=>∑p∈F.degrees,
      (F.covariance w.1).coefficient p*w.2^p) (θ,q) := by
    apply ContDiffAt.sum
    intro p hp
    have hc := (F.smooth_coefficient p hp).contDiffAt (F.isOpen_domain.mem_nhds hθ)
    exact (hc.comp (θ,q) contDiffAt_fst).mul (contDiffAt_snd.pow p)
  apply hraw.congr_of_eventuallyEq
  have he : ∀ᶠw:Θ×ℝ in 𝓝 (θ,q),w.1∈F.domain :=
    continuous_fst.continuousAt (F.isOpen_domain.mem_nhds hθ)
  filter_upwards [he] with w hw
  unfold AdmissibleCovariance.value
  rw [F.degrees_eq w.1 hw]

theorem contDiffAt_correctionPrimitive (F:SmoothCovarianceFamily Θ) {θ:Θ}
    (hθ:θ∈F.domain) (q:ℝ) :
    ContDiffAt ℝ ∞ (fun p:Θ×ℝ=>covarianceCorrectionPrimitive (F.covariance p.1) p.2) (θ,q) :=
  (contDiffAt_snd.mul (F.contDiffAt_first hθ q)).sub (F.contDiffAt_value hθ q)

theorem contDiffAt_atomicRecursionData (F:SmoothCovarianceFamily Θ) {θ:Θ}
    (hθ:θ∈F.domain) {r:ℕ} (z:AtomicPoint r) :
    ContDiffAt ℝ ∞ (fun p:Θ×AtomicPoint r=>atomicRecursionData (F.covariance p.1) p.2) (θ,z) := by
  rw [contDiffAt_pi]
  intro i
  have hnode (j:Fin (r+2)) :
      ContDiffAt ℝ ∞ (fun p:Θ×AtomicPoint r=>(p.1,atomicNode p.2 j)) (θ,z) :=
    contDiffAt_fst.prodMk ((contDiff_atomicNode j).contDiffAt.comp (θ,z) contDiffAt_snd)
  have hupper := (F.contDiffAt_first hθ (atomicNode z i.succ)).comp (θ,z) (hnode i.succ)
  have hlower := (F.contDiffAt_first hθ (atomicNode z i.castSucc)).comp (θ,z) (hnode i.castSucc)
  exact ((contDiff_atomicLevel i).contDiffAt.comp (θ,z) contDiffAt_snd).prodMk (hupper.sub hlower)

theorem contDiffAt_atomicPotentialRecursion (F:SmoothCovarianceFamily Θ) {θ:Θ}
    (hθ:θ∈F.domain) {r:ℕ} (z:AtomicPoint r) (hz:IsAtomicPoint z) :
    ContDiffAt ℝ ∞ (fun p:Θ×AtomicPoint r=>atomicPotentialRecursion (F.covariance p.1) p.2) (θ,z) :=
  (GeneralDepthPaper.contDiffAt_coleHopfRecursion (r+1)
    (atomicRecursionData (F.covariance θ) z,logCoshTerminal)
    (atomicRecursionData_variance_pos (F.covariance θ) z hz)).comp (θ,z)
      ((F.contDiffAt_atomicRecursionData hθ z).prodMk contDiffAt_const)

theorem contDiffAt_atomicCorrection (F:SmoothCovarianceFamily Θ) {θ:Θ}
    (hθ:θ∈F.domain) {r:ℕ} (z:AtomicPoint r) :
    ContDiffAt ℝ ∞ (fun p:Θ×AtomicPoint r=>atomicCorrection (F.covariance p.1) p.2) (θ,z) := by
  apply ContDiffAt.sum
  intro i _
  have hloc : ContDiffAt ℝ ∞ (fun p:Θ×AtomicPoint r=>(p.1,atomicLocation p.2 i)) (θ,z) :=
    contDiffAt_fst.prodMk ((contDiff_atomicLocation i).contDiffAt.comp (θ,z) contDiffAt_snd)
  have h1 := (F.contDiffAt_correctionPrimitive hθ 1).comp (θ,z)
    (contDiffAt_fst.prodMk contDiffAt_const)
  have hq := (F.contDiffAt_correctionPrimitive hθ (atomicLocation z i)).comp (θ,z) hloc
  exact ((contDiff_atomicWeight i).contDiffAt.comp (θ,z) contDiffAt_snd).mul (h1.sub hq)

theorem contDiffAt_atomicFunctionalRecursion (F:SmoothCovarianceFamily Θ) {θ:Θ}
    (hθ:θ∈F.domain) {r:ℕ} (z:AtomicPoint r) (hz:IsAtomicPoint z) :
    ContDiffAt ℝ ∞ (fun p:Θ×AtomicPoint r=>atomicFunctionalRecursion (F.covariance p.1) p.2) (θ,z) := by
  have hval : ContDiffAt ℝ ∞ (fun p:Θ×AtomicPoint r=>
      terminalValue (atomicPotentialRecursion (F.covariance p.1) p.2) 0) (θ,z) := by
    let ev := (ContinuousLinearMap.fst ℝ ℝ (Fin 3→ℝ →ᵇ ℝ)).comp terminalJetSubmodule.subtypeL
    simp only [terminalValue_zero]
    convert! ev.contDiff.contDiffAt.comp (θ,z) (F.contDiffAt_atomicPotentialRecursion hθ z hz) using 1
  exact (contDiffAt_const.add hval).sub (contDiffAt_const.mul (F.contDiffAt_atomicCorrection hθ z))

/-- Proposition 2.4: the actual atomic mixed-model Parisi functional is jointly
C∞ for every smooth finite-polynomial covariance family and every finite depth. -/
theorem finite_step_regularity (F:SmoothCovarianceFamily Θ) (r:ℕ) :
    ContDiffOn ℝ ∞ (fun p:Θ×AtomicPoint r=>atomicFunctionalExtension (F.covariance p.1) r p.2)
      (F.domain×ˢ{z:AtomicPoint r|IsAtomicPoint z}) := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  apply (F.contDiffAt_atomicFunctionalRecursion hp.1 p.2 hp.2).congr_of_eventuallyEq
  have he : ∀ᶠw:Θ×AtomicPoint r in 𝓝 p,IsAtomicPoint w.2 :=
    continuous_snd.continuousAt ((isOpen_atomic_domain r).mem_nhds hp.2)
  filter_upwards [he] with w hw
  rw [atomicFunctionalExtension_eq _ w.2 hw,atomicFunctional_eq_recursion _ w.2 hw]

end SmoothCovarianceFamily
end GeneralDepthPaper
