module

public import GeneralDepthPaper.EndpointDeficitAverage

@[expose] public section


/-! The anchored FTC identity holds on both sides of mass one.  It
identifies the derivative of the actual smooth remainder extension,
without dividing by the disappearing atom mass. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 64

theorem anchored_mass_average_identity (f df : ℝ→ℝ) (m : ℝ)
    (hzero : f 1=0)
    (hd : ∀t∈Icc (0:ℝ) 1,HasDerivAt f (df (1-(1-m)*t)) (1-(1-m)*t))
    (hc : ContinuousOn (fun t=>df (1-(1-m)*t)) (Icc (0:ℝ) 1)) :
    f m=(m-1)*(∫t in (0:ℝ)..1,df (1-(1-m)*t)) := by
  have hder : ∀t∈uIcc (0:ℝ) 1,
      HasDerivAt (fun t=>f (1-(1-m)*t)) ((m-1)*df (1-(1-m)*t)) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have harg : HasDerivAt (fun t:ℝ=>1-(1-m)*t) (m-1) t := by
      have H : HasDerivAt (fun t:ℝ=>1-(1-m)*t) (-(1-m)) t := by
        simpa only [id_eq,mul_one] using ((hasDerivAt_id t).const_mul (1-m)).const_sub 1
      convert H using 1 <;> ring
    simpa only [Function.comp_def,mul_comm] using (hd t ht).comp t harg
  have hi : IntervalIntegrable (fun t=>(m-1)*df (1-(1-m)*t)) volume 0 1 :=
    (continuousOn_const.mul hc).intervalIntegrable_of_Icc zero_le_one
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hi
  rw [intervalIntegral.integral_const_mul] at H
  simpa only [mul_one,sub_sub_cancel,mul_zero,sub_zero,hzero] using H.symm

theorem lowerRemainderEndpointDerivative_eq_massAverage (Ξ : AdmissibleCovariance)
    {r : ℕ} (p : ℕ) (hp : 4 ≤ p) (he : Even p) (hn : p∉Ξ.degrees)
    (z : AtomicPoint r) (hz : IsAtomicPoint z) {m : ℝ} (hm : m∈Ioo (0:ℝ) 2)
    (lam : ℝ) (hlam : 0 < lam) (Q : Overlap) {qc : ℝ}
    (hc : atomicLocation z (Fin.last r) < qc) (hcQ : qc < (Q:ℝ)) (hQ1 : (Q:ℝ) < 1) :
    lowerRemainderEndpointDerivative Ξ p qc (z,(m,(lam,(Q:ℝ))))=
      (m-1)*endpointDeficitAverage Ξ p qc (z,(m,(lam,(Q:ℝ)))) := by
  let x : CutoffInputParameter r := (z,(m,(lam,(Q:ℝ))))
  have hc0 : 0 < qc := (atomicLocation_mem_unit hz (Fin.last r)).1.trans_lt hc
  let Ψ := Ξ.addHighDegree p hp he hn lam hlam
  have hW : 0 < endpointVarianceExpression Ξ p qc (lam,(Q:ℝ)) := by
    rw [←endpointVariance_eq_expression Ξ p hp he hn lam hlam qc Q]
    exact sub_pos.mpr (Ψ.first_strictMonoOn hc0.le ((hc0.trans hcQ).le) hcQ)
  have hx : x∈cutoffInputSmoothDomain Ξ p qc :=
    cutoffInputSmoothDomain_mem Ξ p x hz hc hm hlam.le hW
  have hmem : ∀t∈Icc (0:ℝ) 1,massInterpolation t x∈cutoffInputSmoothDomain Ξ p qc :=
    fun t ht=>massInterpolation_mem_smoothDomain Ξ p qc hx ht
  let f : ℝ→ℝ := fun s=>lowerRemainderEndpointDerivative Ξ p qc (z,(s,(lam,(Q:ℝ))))
  let df : ℝ→ℝ := fun s=>lowerRemainderMassEndpointDerivative Ξ p qc (z,(s,(lam,(Q:ℝ))))
  have hd : ∀t∈Icc (0:ℝ) 1,HasDerivAt f (df (1-(1-m)*t)) (1-(1-m)*t) := by
    intro t ht
    exact hasDerivAt_massSection z (1-(1-m)*t) lam Q
      ((((contDiffOn_lowerRemainderEndpointDerivative Ξ p qc) _ (hmem t ht)).contDiffAt
        ((isOpen_cutoffInputSmoothDomain Ξ p qc).mem_nhds (hmem t ht))).differentiableAt (by simp))
  have hcont : ContinuousOn (fun t=>df (1-(1-m)*t)) (Icc (0:ℝ) 1) := by
    exact (contDiffOn_lowerRemainderMassEndpointDerivative Ξ p qc).continuousOn.comp
      (show ContinuousOn (fun t:ℝ=>massInterpolation t x) (Icc (0:ℝ) 1) by
        unfold massInterpolation
        fun_prop) hmem
  have H := anchored_mass_average_identity f df m
    (lowerRemainderEndpointDerivative_mass_one Ξ p hp he hn z hz lam hlam Q hc hcQ hQ1) hd hcont
  simpa only [endpointDeficitAverage,massAverage_eq_intervalIntegral,massInterpolation,f,df,x] using H

theorem lowerRemainderEndpointDerivative_eq_extendedDeficit (Ξ : AdmissibleCovariance)
    {r : ℕ} (p : ℕ) (hp : 4 ≤ p) (he : Even p) (hn : p∉Ξ.degrees)
    (z : AtomicPoint r) (hz : IsAtomicPoint z) {m : ℝ} (hm : m∈Ioo (0:ℝ) 2)
    (lam : ℝ) (hlam : 0 < lam) (Q : Overlap) {qc : ℝ}
    (hc : atomicLocation z (Fin.last r) < qc) (hcQ : qc < (Q:ℝ)) (hQ1 : (Q:ℝ) < 1) :
    lowerRemainderEndpointDerivative Ξ p qc (z,(m,(lam,(Q:ℝ))))=
      (1-m)/2*highDegreeSecondExpression Ξ p (lam,(Q:ℝ))*
        endpointDeficitFromRemainder Ξ p qc (z,(m,(lam,(Q:ℝ)))) := by
  rw [lowerRemainderEndpointDerivative_eq_massAverage Ξ p hp he hn z hz hm lam hlam Q hc hcQ hQ1,
    endpointDeficitFromRemainder_eq_average]
  have hc0 : 0 < qc := (atomicLocation_mem_unit hz (Fin.last r)).1.trans_lt hc
  have hne : highDegreeSecondExpression Ξ p (lam,(Q:ℝ))≠0 := by
    unfold highDegreeSecondExpression
    rw [←Ξ.addHighDegree_second p hp he hn lam hlam Q]
    exact ((Ξ.addHighDegree p hp he hn lam hlam).second_pos (hc0.trans hcQ)).ne'
  field_simp [hne]
  ring

end GeneralDepthPaper
