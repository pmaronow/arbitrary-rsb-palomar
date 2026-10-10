module

public import DepthPaper.PartialAtomicMeasure
public import FourPapersCommon.MixedSupport
public import FourPapersCommon.MixedColeHopf

@[expose] public section


/-! Actual high-degree covariance perturbations and genuine two-level
candidate measures. Existing base coefficients and atom masses are retained. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace DepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64
namespace AdmissibleCovariance

def addHighDegree (Ξ : AdmissibleCovariance) (p : ℕ) (hp : 4≤p) (he : Even p)
    (hn : p∉Ξ.degrees) (lam : ℝ) (hlam : 0<lam) : AdmissibleCovariance where
  degrees:=insert p Ξ.degrees
  nonempty:=Finset.insert_nonempty _ _
  coefficient j:=if j=p then lam else Ξ.coefficient j
  coefficient_pos j hj:=by
    rcases Finset.mem_insert.mp hj with rfl|hj
    · simp only [ite_eq_left rfl];exact hlam
    · rw [ite_eq_right (fun (hjp:j=p)=>hn (hjp ▸ hj))]
      exact Ξ.coefficient_pos j hj
  degree_ge_four j hj:=by
    rcases Finset.mem_insert.mp hj with rfl|hj
    · exact hp
    · exact Ξ.degree_ge_four j hj
  degree_even j hj:=by
    rcases Finset.mem_insert.mp hj with rfl|hj
    · exact he
    · exact Ξ.degree_even j hj

theorem addHighDegree_value (Ξ : AdmissibleCovariance) (p : ℕ) (hp : 4≤p) (he : Even p)
    (hn : p∉Ξ.degrees) (lam : ℝ) (hlam : 0<lam) (q : ℝ) :
    (Ξ.addHighDegree p hp he hn lam hlam).value q=Ξ.value q+lam*q^p := by
  rw [value,addHighDegree,Finset.sum_insert hn]
  simp only [ite_eq_left rfl]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [ite_eq_right (fun (hjp:j=p)=>hn (hjp ▸ hj))]

theorem addHighDegree_first (Ξ : AdmissibleCovariance) (p : ℕ) (hp : 4≤p) (he : Even p)
    (hn : p∉Ξ.degrees) (lam : ℝ) (hlam : 0<lam) (q : ℝ) :
    (Ξ.addHighDegree p hp he hn lam hlam).first q=Ξ.first q+lam*(p:ℝ)*q^(p-1) := by
  rw [first,addHighDegree,Finset.sum_insert hn]
  simp only [ite_eq_left rfl]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [ite_eq_right (fun (hjp:j=p)=>hn (hjp ▸ hj))]

theorem addHighDegree_second (Ξ : AdmissibleCovariance) (p : ℕ) (hp : 4≤p) (he : Even p)
    (hn : p∉Ξ.degrees) (lam : ℝ) (hlam : 0<lam) (q : ℝ) :
    (Ξ.addHighDegree p hp he hn lam hlam).second q=
      Ξ.second q+lam*(p:ℝ)*(p-1:ℕ)*q^(p-2) := by
  rw [second,addHighDegree,Finset.sum_insert hn]
  simp only [ite_eq_left rfl]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [ite_eq_right (fun (hjp:j=p)=>hn (hjp ▸ hj))]

end AdmissibleCovariance

abbrev twoLevelMeasure {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (m : ℝ) (Q : Overlap) : ParisiMeasure := partialAtomicMeasure z hz m Q

def twoLevelFunctional {r : ℕ} (Ξ : AdmissibleCovariance) (z : AtomicPoint r)
    (hz : IsAtomicPoint z) (m : ℝ) (Q : Overlap) : ℝ :=
  parisiFunctional Ξ (twoLevelMeasure z hz m Q)

theorem parisiCDF_twoLevelMeasure {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (m : ℝ) (hm : m∈Icc (0:ℝ) 1) (Q : Overlap) (q : ℝ) :
    Paper.parisiCDF (twoLevelMeasure z hz m Q) q=
      (1-m)*(if (Q:ℝ)≤q then 1 else 0)+m*Paper.parisiCDF (atomicMeasure z hz) q := by
  change Paper.parisiCDF (partialAtomicMeasure z hz m Q) q=_
  rw [partialAtomicMeasure,Paper.parisiCDF_mix _ _ m q hm]
  have he : (Measure.dirac Q).toProbabilityMeasure=Paper.diracOverlap Q Q.property := rfl
  rw [he,Paper.parisiCDF_dirac]

theorem parisiCDF_atomicMeasure_above_last {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (q : ℝ) (hq : atomicLocation z (Fin.last r)≤q) :
    Paper.parisiCDF (atomicMeasure z hz) q=1 := by
  rw [parisiCDF_atomicMeasure]
  have hsum : (∑i:Fin (r+1),if atomicLocation z i≤q then atomicWeight z i else 0)=
      ∑i:Fin (r+1),atomicWeight z i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [ite_eq_left ((hz.1.monotone (Fin.le_last i)).trans hq)]
  rw [hsum,sum_atomicWeight]

theorem parisiCDF_twoLevelMeasure_middle {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (m : ℝ) (hm : m∈Icc (0:ℝ) 1) (Q : Overlap) (q : ℝ)
    (hq : q∈Ico (atomicLocation z (Fin.last r)) (Q:ℝ)) :
    Paper.parisiCDF (twoLevelMeasure z hz m Q) q=m := by
  rw [parisiCDF_twoLevelMeasure z hz m hm Q q,ite_eq_right (not_le_of_gt hq.2),
    parisiCDF_atomicMeasure_above_last z hz q hq.1]
  ring

theorem parisiCDF_twoLevelMeasure_above {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (m : ℝ) (hm : m∈Icc (0:ℝ) 1) (Q : Overlap)
    (hQ : atomicLocation z (Fin.last r)≤(Q:ℝ)) (q : ℝ) (hq : (Q:ℝ)≤q) :
    Paper.parisiCDF (twoLevelMeasure z hz m Q) q=1 := by
  rw [parisiCDF_twoLevelMeasure z hz m hm Q q,ite_eq_left hq,
    parisiCDF_atomicMeasure_above_last z hz q (hQ.trans hq)]
  ring

end DepthPaper
