module

public import GeneralDepthPaper.LowerRecursionDecomposition
public import GeneralDepthPaper.HighDegreeRegularity

@[expose] public section


/-! Literal finite-sum covariance remainder of the high-degree candidate.
This exposes its dependence on lower atom coordinates without differentiating
a discontinuous CDF or hiding the remainder in the full objective. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace GeneralDepthPaper
set_option maxHeartbeats 800000

theorem highDegree_correctionPrimitive (Ξ : AdmissibleCovariance) (p : ℕ) (hp : 4≤p)
    (he : Even p) (hn : p∉Ξ.degrees) (lam : ℝ) (hlam : 0 < lam) (q : ℝ) :
    covarianceCorrectionPrimitive (Ξ.addHighDegree p hp he hn lam hlam) q=
      covarianceCorrectionPrimitive Ξ q+lam*((p:ℝ)-1)*q^p := by
  rw [covarianceCorrectionPrimitive,Ξ.addHighDegree_first,Ξ.addHighDegree_value,
    covarianceCorrectionPrimitive]
  have hpow : q*q^(p-1)=q^p := by
    rw [←pow_succ',Nat.sub_add_cancel (by omega : 1≤p)]
  calc
    _=q*Ξ.first q-Ξ.value q+lam*(p:ℝ)*(q*q^(p-1))-lam*q^p := by ring
    _=_ := by rw [hpow];ring

theorem atomicCorrection_highDegree (Ξ : AdmissibleCovariance) (p : ℕ) (hp : 4≤p)
    (he : Even p) (hn : p∉Ξ.degrees) (lam : ℝ) (hlam : 0 < lam)
    {r : ℕ} (z : AtomicPoint r) :
    atomicCorrection (Ξ.addHighDegree p hp he hn lam hlam) z=atomicCorrection Ξ z+
      lam*((p:ℝ)-1)*(1-∑i:Fin (r+1),atomicWeight z i*(atomicLocation z i)^p) := by
  simp only [atomicCorrection,highDegree_correctionPrimitive,one_pow]
  let L:ℝ:=lam*((p:ℝ)-1)
  calc
    _=(∑i:Fin (r+1),atomicWeight z i*(covarianceCorrectionPrimitive Ξ 1-
        covarianceCorrectionPrimitive Ξ (atomicLocation z i)))+
      L*(∑i:Fin (r+1),atomicWeight z i)-
        L*(∑i:Fin (r+1),atomicWeight z i*(atomicLocation z i)^p) := by
      rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [L]
      ring
    _=_ := by rw [sum_atomicWeight];dsimp only [L];ring

theorem lowerCovarianceRemainder_highDegree (Ξ : AdmissibleCovariance) (p : ℕ) (hp : 4≤p)
    (he : Even p) (hn : p∉Ξ.degrees) (lam : ℝ) (hlam : 0 < lam)
    {r : ℕ} (z : AtomicPoint r) (m qc : ℝ) :
    lowerCovarianceRemainder Ξ (Ξ.addHighDegree p hp he hn lam hlam) z m qc=
      lam*m/2*(((p:ℝ)-1)*
        (∑i:Fin (r+1),atomicWeight z i*(atomicLocation z i)^p)-(p:ℝ)*qc^(p-1)) := by
  simp only [lowerCovarianceRemainder,Ξ.addHighDegree_first,Ξ.addHighDegree_value,
    atomicCorrection_highDegree,one_pow]
  ring

theorem twoLevelFunctional_highDegree_decomposition (Ξ : AdmissibleCovariance)
    (p : ℕ) (hp : 4≤p) (he : Even p) (hn : p∉Ξ.degrees) (lam : ℝ) (hlam : 0 < lam)
    {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Ioc (0:ℝ) 1)
    (Q : Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc) (hcQ : qc≤(Q:ℝ)) :
    twoLevelFunctional (Ξ.addHighDegree p hp he hn lam hlam) z hz m Q=
      limitingAtomicObjective Ξ r lam (z,m)+
        (1-m)/2*(∫q in (Q:ℝ)..1,(1-q)*(Ξ.addHighDegree p hp he hn lam hlam).second q)+
          lowerRecursionDifference Ξ (Ξ.addHighDegree p hp he hn lam hlam) z hz m hm Q qc hc hcQ+
            lam*m/2*(((p:ℝ)-1)*
              (∑i:Fin (r+1),atomicWeight z i*(atomicLocation z i)^p)-(p:ℝ)*qc^(p-1)) := by
  have H:=twoLevelFunctional_decomposition Ξ (Ξ.addHighDegree p hp he hn lam hlam)
    z hz m hm Q qc hc hcQ
  rw [Ξ.addHighDegree_value] at H
  simp only [one_pow,add_sub_cancel_left,mul_one] at H
  rw [lowerRecursionRemainder,lowerCovarianceRemainder_highDegree] at H
  exact H.trans (by ring)

end GeneralDepthPaper
