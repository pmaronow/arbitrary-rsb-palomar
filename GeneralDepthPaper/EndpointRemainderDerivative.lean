module

public import GeneralDepthPaper.LowerRecursionLemma
public import GeneralDepthPaper.TopAtomDerivative

@[expose] public section


/-! The exact Q-derivative of the actual lower remainder. It identifies
the endpoint deficit through the genuine atom-moving first variation,
including mass one where the top atom has zero weight. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace GeneralDepthPaper
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 64

def lowerEndpointDirection {r : ℕ} : CutoffInputParameter r := ((0,0),(0,(0,1)))

def lowerRemainderEndpointDerivative (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (qc : ℝ) (x : CutoffInputParameter r) : ℝ :=
  fderiv ℝ (lowerRecursionErrorRaw Ξ p qc) x lowerEndpointDirection

theorem hasDerivAt_endpointTerm_shift (Ψ : AdmissibleCovariance) (m Q : ℝ) :
    HasDerivAt (fun t:ℝ=>(1-m)/2*(∫q in Q+t..1,(1-q)*Ψ.second q))
      (-(1-m)/2*(1-Q)*Ψ.second Q) 0 := by
  have hf : Continuous (fun q:ℝ=>(1-q)*Ψ.second q) :=
    (continuous_const.sub continuous_id).mul Ψ.continuous_second
  have hd := intervalIntegral.integral_hasDerivAt_left (hf.intervalIntegrable Q 1)
    hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have harg : HasDerivAt (fun t:ℝ=>Q+t) 1 0 := by
    simpa only [id_eq] using (hasDerivAt_id (0:ℝ)).const_add Q
  have hd' : HasDerivAt (fun u=>∫q in u..1,(1-q)*Ψ.second q)
      (-((1-Q)*Ψ.second Q)) (Q+0) := by simpa only [add_zero] using hd
  have hout := (hd'.comp 0 harg).const_mul ((1-m)/2)
  convert hout using 1 <;> simp only [Function.comp_def,mul_one] <;> ring

theorem hasDerivAt_lowerRecursionErrorRaw_endpoint (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (hp : 4≤p) (he : Even p) (hn : p∉Ξ.degrees)
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Ioc (0:ℝ) 1)
    (lam : ℝ) (hlam : 0<lam) (Q : Overlap) {qc : ℝ}
    (hc : atomicLocation z (Fin.last r)<qc) (hcQ : qc<(Q:ℝ)) (hQ1 : (Q:ℝ)<1) :
    HasDerivAt (fun t:ℝ=>lowerRecursionErrorRaw Ξ p qc (z,(m,(lam,(Q:ℝ)+t))))
      ((1-m)/2*(Ξ.addHighDegree p hp he hn lam hlam).second Q*
        (1-Gamma (Ξ.addHighDegree p hp he hn lam hlam) (twoLevelMeasure z hz m Q) Q)) 0 := by
  let Ψ := Ξ.addHighDegree p hp he hn lam hlam
  have hc0 : 0<qc := (atomicLocation_mem_unit hz (Fin.last r)).1.trans_lt hc
  have htop := hasDerivAt_twoLevelFunctional_top Ψ z hz m ⟨hm.1.le,hm.2⟩ Q
    (hc.trans hcQ) hQ1
  have hterm := hasDerivAt_endpointTerm_shift Ψ m Q
  have hcomb := (htop.sub_const (limitingAtomicObjective Ξ r lam (z,m))).sub hterm
  have ht : ∀ᶠt:ℝ in 𝓝 0,(Q:ℝ)+t∈Ioo qc 1 := by
    apply (continuous_const.add continuous_id).continuousAt
    simpa only [Pi.add_apply,id_eq,add_zero] using Ioo_mem_nhds hcQ hQ1
  have heq : (fun t:ℝ=>lowerRecursionErrorRaw Ξ p qc (z,(m,(lam,(Q:ℝ)+t))))=ᶠ[𝓝 0]
      (fun t=>twoLevelFunctional Ψ z hz m (movedOverlap Q t)-
        limitingAtomicObjective Ξ r lam (z,m)-
          (1-m)/2*(∫q in (Q:ℝ)+t..1,(1-q)*Ψ.second q)) := by
    filter_upwards [ht] with t ht
    have hmoved : (movedOverlap Q t:ℝ)=(Q:ℝ)+t := by
      simp only [movedOverlap,projIcc_of_mem (by norm_num : (0:ℝ)≤1)
        ⟨hc0.le.trans ht.1.le,ht.2.le⟩]
    have HH := twoLevelFunctional_eq_lowerRecursionErrorRaw Ξ p hp he hn z hz m hm lam hlam
      (movedOverlap Q t) qc hc (by rw [hmoved];exact ht.1.le)
    rw [hmoved] at HH
    change twoLevelFunctional Ψ z hz m (movedOverlap Q t)=_ at HH
    linarith
  have hout := hcomb.congr_of_eventuallyEq heq
  convert hout using 1
  ring

theorem lowerRemainderEndpointDerivative_eq_deficit (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (hp : 4≤p) (he : Even p) (hn : p∉Ξ.degrees)
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Ioc (0:ℝ) 1)
    (lam : ℝ) (hlam : 0<lam) (Q : Overlap) {qc : ℝ}
    (hc : atomicLocation z (Fin.last r)<qc) (hcQ : qc<(Q:ℝ)) (hQ1 : (Q:ℝ)<1) :
    lowerRemainderEndpointDerivative Ξ p qc (z,(m,(lam,(Q:ℝ))))=
      (1-m)/2*(Ξ.addHighDegree p hp he hn lam hlam).second Q*
        (1-Gamma (Ξ.addHighDegree p hp he hn lam hlam) (twoLevelMeasure z hz m Q) Q) := by
  let x : CutoffInputParameter r := (z,(m,(lam,(Q:ℝ))))
  have hc0 : 0<qc := (atomicLocation_mem_unit hz (Fin.last r)).1.trans_lt hc
  have hW : 0<endpointVarianceExpression Ξ p qc (lam,(Q:ℝ)) := by
    rw [←endpointVariance_eq_expression Ξ p hp he hn lam hlam qc Q]
    exact sub_pos.mpr ((Ξ.addHighDegree p hp he hn lam hlam).first_strictMonoOn
      hc0.le ((hc0.trans hcQ).le) hcQ)
  have hdom := cutoffInputSmoothDomain_mem Ξ p x hz hc
    ⟨hm.1,hm.2.trans_lt (by norm_num)⟩ hlam.le hW
  have hRd := ((contDiffOn_lowerRecursionErrorRaw Ξ p qc) x hdom).contDiffAt
    ((isOpen_cutoffInputSmoothDomain Ξ p qc).mem_nhds hdom)
  have hcurve : HasDerivAt (fun t:ℝ=>x+t • lowerEndpointDirection)
      lowerEndpointDirection 0 := by
    simpa only [id_eq,one_smul] using ((hasDerivAt_id (0:ℝ)).smul_const
      (lowerEndpointDirection (r:=r))).const_add x
  have hbase : HasFDerivAt (lowerRecursionErrorRaw Ξ p qc)
      (fderiv ℝ (lowerRecursionErrorRaw Ξ p qc) x) (x+(0:ℝ) • lowerEndpointDirection) := by
    simpa only [zero_smul,add_zero] using (hRd.differentiableAt (by simp)).hasFDerivAt
  have hd := hbase.comp_hasDerivAt 0 hcurve
  have hpath : (fun t:ℝ=>x+t • lowerEndpointDirection)=
      (fun t=> (z,(m,(lam,(Q:ℝ)+t)))) := by
    funext t
    simp [x,lowerEndpointDirection,Prod.smul_mk,smul_eq_mul]
  rw [hpath] at hd
  have hknown := hasDerivAt_lowerRecursionErrorRaw_endpoint Ξ p hp he hn z hz m hm lam hlam Q hc hcQ hQ1
  exact hd.unique hknown

theorem lowerRemainderEndpointDerivative_mass_one (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (hp : 4≤p) (he : Even p) (hn : p∉Ξ.degrees)
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (lam : ℝ) (hlam : 0<lam)
    (Q : Overlap) {qc : ℝ} (hc : atomicLocation z (Fin.last r)<qc)
    (hcQ : qc<(Q:ℝ)) (hQ1 : (Q:ℝ)<1) :
    lowerRemainderEndpointDerivative Ξ p qc (z,(1,(lam,(Q:ℝ))))=0 := by
  rw [lowerRemainderEndpointDerivative_eq_deficit Ξ p hp he hn z hz 1
    (by simp : (1:ℝ)∈Ioc (0:ℝ) 1) lam hlam Q hc hcQ hQ1]
  ring

end GeneralDepthPaper
