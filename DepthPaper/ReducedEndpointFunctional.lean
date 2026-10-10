module

public import DepthPaper.EndpointRemainderMassAverageIdentity
public import DepthPaper.EndpointTermExpression
public import DepthPaper.DistinguishedEndpointContact

@[expose] public section


/-! A genuine smooth extension of the actual endpoint functional.  Its
Q derivative factors through the actual removable contact equation on an
open mass neighborhood, including both sides of mass one. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 64

def limitingObjectiveCore (Ξ : AdmissibleCovariance) {r : ℕ}
    (theta : HighDegreeLowerParameter r) : ℝ :=
  limitingAtomicObjective Ξ r theta.2.2 (theta.1,theta.2.1)

def endpointFunctionalExtension (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (qc : ℝ) (x : CutoffInputParameter r) : ℝ :=
  limitingObjectiveCore Ξ (cutoffVarianceProjection x)+
    endpointTermExpression Ξ p x+lowerRecursionErrorRaw Ξ p qc x

def endpointFunctionalChart (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (qc : ℝ) : HighDegreeLowerParameter r×ℝ→ℝ :=
  endpointFunctionalExtension Ξ p qc ∘ cutoffParameterAssembly

def reducedEndpointFunctional (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (qc cQ CQ : ℝ) (theta : HighDegreeLowerParameter r) : ℝ :=
  endpointFunctionalChart Ξ p qc (theta,distinguishedEndpoint Ξ p qc cQ CQ theta)

theorem contDiffAt_limitingObjectiveCore (Ξ : AdmissibleCovariance) {r : ℕ}
    {theta : HighDegreeLowerParameter r} (hz : IsAtomicPoint theta.1)
    (hm : 0 < theta.2.1) : ContDiffAt ℝ ∞ (limitingObjectiveCore Ξ) theta := by
  have hp := (contDiffAt_limitingAtomicPhi Ξ theta.1 hz theta.2.1 hm).comp theta
    (contDiffAt_fst.prodMk contDiffAt_snd.fst)
  exact hp.add (show ContDiffAt ℝ ∞ (fun w:HighDegreeLowerParameter r=>w.2.2*w.2.1/2) theta by
    fun_prop)

theorem contDiffAt_endpointFunctionalExtension (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (qc : ℝ) {x : CutoffInputParameter r}
    (hz : IsAtomicPoint x.1) (hx : x∈cutoffInputSmoothDomain Ξ p qc) :
    ContDiffAt ℝ ∞ (endpointFunctionalExtension Ξ p qc) x := by
  have hlim := (contDiffAt_limitingObjectiveCore Ξ hz hx.1.1).comp x
    cutoffVarianceProjection.contDiff.contDiffAt
  exact (hlim.add (contDiff_endpointTermExpression Ξ p).contDiffAt).add
    ((contDiffOn_lowerRecursionErrorRaw Ξ p qc).contDiffAt
      ((isOpen_cutoffInputSmoothDomain Ξ p qc).mem_nhds hx))

theorem endpointFunctionalExtension_eq_actual (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (hp : 4 ≤ p) (he : Even p) (hn : p∉Ξ.degrees)
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Ioc (0:ℝ) 1)
    (lam : ℝ) (hlam : 0 < lam) (Q : Overlap) {qc : ℝ}
    (hc : atomicLocation z (Fin.last r) < qc) (hcQ : qc ≤ (Q:ℝ)) :
    endpointFunctionalExtension Ξ p qc (z,(m,(lam,(Q:ℝ))))=
      twoLevelFunctional (Ξ.addHighDegree p hp he hn lam hlam) z hz m Q := by
  rw [twoLevelFunctional_eq_lowerRecursionErrorRaw Ξ p hp he hn z hz m hm lam hlam Q qc hc hcQ]
  unfold endpointFunctionalExtension limitingObjectiveCore
  rw [endpointTermExpression_eq_integral Ξ p hp he hn z m lam Q hlam]
  rfl

theorem hasDerivAt_endpointFunctionalExtension_endpoint (Ξ : AdmissibleCovariance)
    {r : ℕ} (p : ℕ) (hp : 4 ≤ p) (he : Even p) (hn : p∉Ξ.degrees)
    (z : AtomicPoint r) (hz : IsAtomicPoint z) {m : ℝ} (hm : m∈Ioo (0:ℝ) 2)
    (lam : ℝ) (hlam : 0 < lam) (Q : Overlap) {qc : ℝ}
    (hc : atomicLocation z (Fin.last r) < qc) (hcQ : qc < (Q:ℝ)) (hQ1 : (Q:ℝ) < 1) :
    HasDerivAt (fun q=>endpointFunctionalExtension Ξ p qc (z,(m,(lam,q))))
      ((1-m)/2*highDegreeSecondExpression Ξ p (lam,(Q:ℝ))*
        endpointRootEquation Ξ p qc ((z,(m,lam)),(Q:ℝ))) Q := by
  let x : CutoffInputParameter r := (z,(m,(lam,(Q:ℝ))))
  have hc0 : 0 < qc := (atomicLocation_mem_unit hz (Fin.last r)).1.trans_lt hc
  have hW : 0 < endpointVarianceExpression Ξ p qc (lam,(Q:ℝ)) := by
    rw [←endpointVariance_eq_expression Ξ p hp he hn lam hlam qc Q]
    exact sub_pos.mpr ((Ξ.addHighDegree p hp he hn lam hlam).first_strictMonoOn
      hc0.le ((hc0.trans hcQ).le) hcQ)
  have hx : x∈cutoffInputSmoothDomain Ξ p qc :=
    cutoffInputSmoothDomain_mem Ξ p x hz hc hm hlam.le hW
  have hR : HasDerivAt (fun q=>lowerRecursionErrorRaw Ξ p qc (z,(m,(lam,q))))
      (lowerRemainderEndpointDerivative Ξ p qc x) Q := by
    have hf := ((contDiffOn_lowerRecursionErrorRaw Ξ p qc).contDiffAt
      ((isOpen_cutoffInputSmoothDomain Ξ p qc).mem_nhds hx)).differentiableAt (by simp)
    exact hf.hasFDerivAt.comp_hasDerivAt (Q:ℝ)
      ((hasDerivAt_const (Q:ℝ) z).prodMk ((hasDerivAt_const (Q:ℝ) m).prodMk
        ((hasDerivAt_const (Q:ℝ) lam).prodMk (hasDerivAt_id (Q:ℝ)))))
  have hsum := ((hasDerivAt_const (Q:ℝ) (limitingObjectiveCore Ξ (z,(m,lam)))).add
    (hasDerivAt_endpointTermExpression_endpoint Ξ p (by omega) z m lam Q)).add hR
  rw [lowerRemainderEndpointDerivative_eq_extendedDeficit Ξ p hp he hn z hz hm lam hlam Q hc hcQ hQ1]
    at hsum
  convert hsum using 1
  · rfl
  · dsimp only [endpointRootEquation,cutoffParameterAssembly_apply]
    ring

theorem contDiffAt_reducedEndpointFunctional (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (qc cQ CQ : ℝ) (hCQ : cQ < CQ) (hp : 0 < p)
    {theta : HighDegreeLowerParameter r} (hz : IsAtomicPoint theta.1)
    (htheta : theta∈distinguishedEndpointDomain Ξ p qc cQ CQ) :
    ContDiffAt ℝ ∞ (reducedEndpointFunctional Ξ p qc cQ CQ) theta := by
  have hs := distinguishedEndpoint_spec Ξ p qc cQ CQ hCQ hp htheta
  have hm := (htheta.1 _ (Ioo_subset_Icc_self hs.1)).1.1
  exact ((contDiffAt_endpointFunctionalExtension Ξ p qc hz hm).comp _
    cutoffParameterAssembly.contDiff.contDiffAt).comp theta (contDiffAt_id.prodMk hs.2.2)

end DepthPaper
