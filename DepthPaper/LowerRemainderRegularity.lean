module

public import DepthPaper.CutoffRecursionRegularity
public import DepthPaper.HighDegreeCorrection

@[expose] public section


/-! The actual lower remainder has a genuine smooth extension in mass past
one. This is obtained from the unrestricted Cole–Hopf recursion, rather than
from an atomic chart whose top atom disappears at that boundary. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BoundedContinuousFunction
namespace DepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

abbrev LowerRemainderParameter (Θ : Type*) (r : ℕ) := Θ × (AtomicPoint r × (ℝ × ℝ))

def lowerRecursionDifferenceExtension (Ξ Ψ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (m Q qc : ℝ) : ℝ :=
  terminalValue (cutoffRecursionTerminal Ψ z m qc
    (cutoffTerminal m (Ψ.first Q-Ψ.first qc))) 0-
  terminalValue (cutoffRecursionTerminal Ξ z m qc (scaledLogCoshTerminal m)) 0

def lowerRecursionRemainderExtension (Ξ Ψ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (m Q qc : ℝ) : ℝ :=
  lowerRecursionDifferenceExtension Ξ Ψ z m Q qc+lowerCovarianceRemainder Ξ Ψ z m qc

theorem lowerRecursionDifference_eq_extension (Ξ Ψ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Ioc (0:ℝ) 1)
    (Q : Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc) (hcQ : qc≤(Q:ℝ)) :
    lowerRecursionDifference Ξ Ψ z hz m hm Q qc hc hcQ=
      lowerRecursionDifferenceExtension Ξ Ψ z m Q qc := by
  unfold lowerRecursionDifference lowerRecursionDifferenceExtension
  dsimp only [cutoffCandidateData,cutoffComparisonData]
  exact congrArg₂ (fun a b : ℝ => a-b)
    (cutoffTruncatedData_initial_eq_recursion Ψ z hz m ⟨hm.1.le,hm.2⟩ qc hc _ _ 0)
    (cutoffTruncatedData_initial_eq_recursion Ξ z hz m ⟨hm.1.le,hm.2⟩ qc hc _ _ 0)

theorem lowerRecursionRemainder_eq_extension (Ξ Ψ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Ioc (0:ℝ) 1)
    (Q : Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc) (hcQ : qc≤(Q:ℝ)) :
    lowerRecursionRemainder Ξ Ψ z hz m hm Q qc hc hcQ=
      lowerRecursionRemainderExtension Ξ Ψ z m Q qc := by
  rw [lowerRecursionRemainder,lowerRecursionRemainderExtension,lowerRecursionDifference_eq_extension]

namespace SmoothCovarianceFamily
variable {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]

theorem contDiffAt_lowerRecursionDifferenceExtension (F : SmoothCovarianceFamily Θ)
    (Ξ : AdmissibleCovariance) {θ : Θ} (hθ : θ∈F.domain) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m Q qc : ℝ)
    (hm : m∈Ioo (0:ℝ) 2) (hc : atomicLocation z (Fin.last r)<qc)
    (hV : 0<(F.covariance θ).first Q-(F.covariance θ).first qc) :
    ContDiffAt ℝ ∞ (fun p : LowerRemainderParameter Θ r =>
      lowerRecursionDifferenceExtension Ξ (F.covariance p.1) p.2.1 p.2.2.1 p.2.2.2 qc)
        (θ,(z,(m,Q))) := by
  let base : LowerRemainderParameter Θ r := (θ,(z,(m,Q)))
  have harg : ContDiffAt ℝ ∞ (fun p : LowerRemainderParameter Θ r =>
      (p.1,(p.2.1,p.2.2.1))) base := by fun_prop
  have hQ : ContDiffAt ℝ ∞ (fun p : LowerRemainderParameter Θ r => (p.1,p.2.2.2)) base := by fun_prop
  have hcarg : ContDiffAt ℝ ∞ (fun p : LowerRemainderParameter Θ r => (p.1,qc)) base := by fun_prop
  have hv := ((F.contDiffAt_first hθ Q).comp base hQ).sub
    ((F.contDiffAt_first hθ qc).comp base hcarg)
  have hmarg : ContDiffAt ℝ ∞ (fun p : LowerRemainderParameter Θ r => p.2.2.1) base := by fun_prop
  have hg := (contDiffAt_cutoffTerminal hm.1.ne' hV).comp base (hmarg.prodMk hv)
  have hrec := (F.contDiffAt_cutoffRecursionTerminal hθ z hz m qc hc
    (cutoffTerminal m ((F.covariance θ).first Q-(F.covariance θ).first qc))).comp base
      (harg.prodMk hg)
  let ev := (ContinuousLinearMap.fst ℝ ℝ (Fin 3→ℝ →ᵇ ℝ)).comp terminalJetSubmodule.subtypeL
  have hval := ev.contDiff.contDiffAt.comp base hrec
  have hsteps : ContDiffAt ℝ ∞ (fun p : LowerRemainderParameter Θ r =>
      cutoffRecursionSteps Ξ p.2.1 p.2.2.1 qc) base := by
    rw [contDiffAt_pi]
    intro i
    have hn (j : Fin (r+2)) : ContDiffAt ℝ ∞
        (fun p : LowerRemainderParameter Θ r => cutoffAtomicNode p.2.1 qc j) base :=
      (contDiff_cutoffAtomicNode qc j).contDiffAt.comp base (by fun_prop)
    exact (hmarg.mul ((contDiff_atomicLevel i).contDiffAt.comp base (by fun_prop))).prodMk
      ((Ξ.contDiff_first.contDiffAt.comp base (hn i.succ)).sub
        (Ξ.contDiff_first.contDiffAt.comp base (hn i.castSucc)))
  have hpsi := (contDiffAt_scaledLogCoshTerminal hm).comp base hmarg
  have href := (DepthPaper.contDiffAt_coleHopfRecursion (r+1)
    (cutoffRecursionSteps Ξ z m qc,scaledLogCoshTerminal m)
    (cutoffRecursionSteps_variance_pos Ξ z hz m qc hc)).comp base (hsteps.prodMk hpsi)
  have hvalref := ev.contDiff.contDiffAt.comp base href
  convert! hval.sub hvalref using 1
  simp only [lowerRecursionDifferenceExtension,terminalValue_zero,ev,
    Function.comp_def,ContinuousLinearMap.comp_apply]
  rfl


theorem contDiffAt_lowerCovarianceRemainder (F : SmoothCovarianceFamily Θ)
    (Ξ : AdmissibleCovariance) {θ : Θ} (hθ : θ∈F.domain) {r : ℕ}
    (z : AtomicPoint r) (m Q qc : ℝ) :
    ContDiffAt ℝ ∞ (fun p : LowerRemainderParameter Θ r =>
      lowerCovarianceRemainder Ξ (F.covariance p.1) p.2.1 p.2.2.1 qc)
        (θ,(z,(m,Q))) := by
  let base : LowerRemainderParameter Θ r := (θ,(z,(m,Q)))
  have hfirst (q : ℝ) := (F.contDiffAt_first hθ q).comp base
    (show ContDiffAt ℝ ∞ (fun p : LowerRemainderParameter Θ r => (p.1,q)) base by fun_prop)
  have hvalue := (F.contDiffAt_value hθ 1).comp base
    (show ContDiffAt ℝ ∞ (fun p : LowerRemainderParameter Θ r => (p.1,(1:ℝ))) base by fun_prop)
  have hcorr := (F.contDiffAt_atomicCorrection hθ z).comp base
    (show ContDiffAt ℝ ∞ (fun p : LowerRemainderParameter Θ r => (p.1,p.2.1)) base by fun_prop)
  have href := (contDiff_atomicCorrection Ξ r).contDiffAt.comp base
    (show ContDiffAt ℝ ∞ (fun p : LowerRemainderParameter Θ r => p.2.1) base by fun_prop)
  have hmass : ContDiffAt ℝ ∞ (fun p : LowerRemainderParameter Θ r => p.2.2.1/2) base := by fun_prop
  exact hmass.mul ((((hfirst 1).sub contDiffAt_const).sub
    ((hfirst qc).sub contDiffAt_const)).sub (hcorr.sub href) |>.sub
      (hvalue.sub contDiffAt_const))

theorem contDiffAt_lowerRecursionRemainderExtension (F : SmoothCovarianceFamily Θ)
    (Ξ : AdmissibleCovariance) {θ : Θ} (hθ : θ∈F.domain) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m Q qc : ℝ)
    (hm : m∈Ioo (0:ℝ) 2) (hc : atomicLocation z (Fin.last r)<qc)
    (hV : 0<(F.covariance θ).first Q-(F.covariance θ).first qc) :
    ContDiffAt ℝ ∞ (fun p : LowerRemainderParameter Θ r =>
      lowerRecursionRemainderExtension Ξ (F.covariance p.1) p.2.1 p.2.2.1 p.2.2.2 qc)
        (θ,(z,(m,Q))) :=
  (F.contDiffAt_lowerRecursionDifferenceExtension Ξ hθ z hz m Q qc hm hc hV).add
    (F.contDiffAt_lowerCovarianceRemainder Ξ hθ z m Q qc)

end SmoothCovarianceFamily
end DepthPaper
