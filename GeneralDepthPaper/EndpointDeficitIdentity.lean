module

public import GeneralDepthPaper.EndpointMassRegularity
public import GeneralDepthPaper.DividedMassIdentity

@[expose] public section


/-! The literal endpoint deficit identity of Lemma 4.3, including m=1.
The apparent singular quotient is removed using actual weak-measure
continuity and the ordinary mixed derivative of the actual remainder. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace GeneralDepthPaper
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 64

def highDegreeSecondExpression (Ξ : AdmissibleCovariance) (p : ℕ) (w : ℝ×ℝ) : ℝ :=
  Ξ.second w.2+w.1*(p:ℝ)*(p-1:ℕ)*w.2^(p-2)

def endpointDeficitFromRemainder (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (qc : ℝ) (x : CutoffInputParameter r) : ℝ :=
  -2/highDegreeSecondExpression Ξ p x.2.2*
    (∫τ in (0:ℝ)..1,lowerRemainderMassEndpointDerivative Ξ p qc
      (x.1,(1-(1-x.2.1)*τ,x.2.2)))

theorem endpoint_deficit_remainder_identity (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (hp : 4≤p) (he : Even p) (hn : p∉Ξ.degrees)
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Ioc (0:ℝ) 1)
    (lam : ℝ) (hlam : 0<lam) (Q : Overlap) {qc : ℝ}
    (hc : atomicLocation z (Fin.last r)<qc) (hcQ : qc<(Q:ℝ)) (hQ1 : (Q:ℝ)<1) :
    1-Gamma (Ξ.addHighDegree p hp he hn lam hlam) (twoLevelMeasure z hz m Q) Q=
      endpointDeficitFromRemainder Ξ p qc (z,(m,(lam,(Q:ℝ)))) := by
  let Ψ := Ξ.addHighDegree p hp he hn lam hlam
  let a : ℝ := m/2
  have ha : 0<a := by dsimp only [a];linarith [hm.1]
  have ha1 : a<1 := by dsimp only [a];linarith [hm.2]
  have ham : a ≤ m := by dsimp only [a];linarith [hm.1]
  have hc0 : 0<qc := (atomicLocation_mem_unit hz (Fin.last r)).1.trans_lt hc
  have hW : 0<endpointVarianceExpression Ξ p qc (lam,(Q:ℝ)) := by
    rw [←endpointVariance_eq_expression Ξ p hp he hn lam hlam qc Q]
    exact sub_pos.mpr (Ψ.first_strictMonoOn hc0.le ((hc0.trans hcQ).le) hcQ)
  let f : ℝ→ℝ := fun s=>lowerRemainderEndpointDerivative Ξ p qc (z,(s,(lam,(Q:ℝ))))
  let df : ℝ→ℝ := fun s=>lowerRemainderMassEndpointDerivative Ξ p qc (z,(s,(lam,(Q:ℝ))))
  let A : ℝ→ℝ := fun s=>1-Gamma Ψ (twoLevelMeasure z hz s Q) Q
  have hd : ∀s∈Icc a 1,HasDerivAt f (df s) s := by
    intro s hs
    exact hasDerivAt_lowerRemainderEndpointDerivative_mass Ξ p z hz
      ⟨ha.trans_le hs.1,hs.2.trans_lt (by norm_num)⟩ hc hlam.le hW
  have hdf : ContinuousOn df (Icc a 1) :=
    continuousOn_lowerRemainderMassEndpointDerivative_mass Ξ p z hz ha hc hlam.le hW
  have hzero : f 1=0 := lowerRemainderEndpointDerivative_mass_one Ξ p hp he hn z hz lam hlam Q hc hcQ hQ1
  have hA : ContinuousWithinAt A (Icc a 1) 1 :=
    ((continuousOn_const.sub (continuousOn_twoLevelGamma_mass Ψ z hz Q)).mono
      (show Icc a 1⊆Icc (0:ℝ) 1 by intro s hs;exact ⟨ha.le.trans hs.1,hs.2⟩)) 1 ⟨ha1.le,le_rfl⟩
  have hid : ∀s∈Ico a 1,f s=(1-s)/2*Ψ.second Q*A s := by
    intro s hs
    exact lowerRemainderEndpointDerivative_eq_deficit Ξ p hp he hn z hz s
      ⟨ha.trans_le hs.1,hs.2.le⟩ lam hlam Q hc hcQ hQ1
  have hsecond : Ψ.second Q≠0 := (Ψ.second_pos (hc0.trans hcQ)).ne'
  have H := divided_mass_integral_identity ha1 hsecond f df A hd hdf hzero hA hid m ⟨ham,hm.2⟩
  change 1-Gamma Ψ (twoLevelMeasure z hz m Q) Q=_
  rw [endpointDeficitFromRemainder]
  have hcEq : highDegreeSecondExpression Ξ p (lam,(Q:ℝ))=Ψ.second Q := by
    exact (Ξ.addHighDegree_second p hp he hn lam hlam Q).symm
  rw [hcEq]
  exact H

end GeneralDepthPaper
