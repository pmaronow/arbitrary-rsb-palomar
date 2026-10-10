module

public import GeneralDepthPaper.HighDegreeModel
public import GeneralDepthPaper.AtomMoveDerivative

@[expose] public section


/-! Literal endpoint-atom stationarity of the genuine candidate measure.
The top weight may vanish at mass one; its derivative then vanishes too. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators
namespace GeneralDepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem atomicMeasure_singleton_above {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (Q : Overlap) (hQ : atomicLocation z (Fin.last r)<(Q:ℝ)) :
    (atomicMeasure z hz : Measure Overlap) {Q}=0 := by
  rw [atomicMeasure_measure,Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hne : atomicOverlap z hz i≠Q := by
    intro he
    have hlt := (hz.1.monotone (Fin.le_last i)).trans_lt hQ
    have hv := congrArg (fun q : Overlap => (q:ℝ)) he
    exact (ne_of_lt hlt) hv
  simp [Measure.smul_apply,Measure.dirac_apply',hne]

theorem atomWeight_twoLevel_top {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (m : ℝ) (hm : m∈Icc (0:ℝ) 1) (Q : Overlap)
    (hQ : atomicLocation z (Fin.last r)<(Q:ℝ)) :
    atomWeight (twoLevelMeasure z hz m Q) Q=1-m := by
  simp only [atomWeight,Measure.real,twoLevelMeasure,partialAtomicMeasure]
  rw [Paper.parisiMix_measure _ _ m hm]
  simp only [Measure.add_apply,Measure.smul_apply,Measure.toProbabilityMeasure,
    ProbabilityMeasure.toMeasure,Measure.dirac_apply_of_mem (mem_singleton Q),
    smul_eq_mul,mul_one,atomicMeasure_singleton_above z hz Q hQ,mul_zero,add_zero]
  change (ENNReal.ofReal (1-m)+ENNReal.ofReal m*(atomicMeasure z hz : Measure Overlap) {Q}).toReal=1-m
  rw [atomicMeasure_singleton_above z hz Q hQ,mul_zero,add_zero]
  exact ENNReal.toReal_ofReal (sub_nonneg.mpr hm.2)

theorem moveAtom_twoLevel_top {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (m : ℝ) (hm : m∈Icc (0:ℝ) 1) (Q : Overlap)
    (hQ : atomicLocation z (Fin.last r)<(Q:ℝ)) (t : ℝ) :
    moveAtom (twoLevelMeasure z hz m Q) Q t=twoLevelMeasure z hz m (movedOverlap Q t) := by
  classical
  apply ProbabilityMeasure.toMeasure_injective
  have hmap := measurable_moveAtomMap Q t
  simp only [moveAtom,ProbabilityMeasure.toMeasure_map,twoLevelMeasure,partialAtomicMeasure]
  rw [Paper.parisiMix_measure _ _ m hm,Measure.map_add _ _ hmap,
    Measure.map_smul _ hmap.aemeasurable,Measure.map_smul _ hmap.aemeasurable]
  have hdirac : (Measure.dirac Q).map (moveAtomMap Q t)=Measure.dirac (movedOverlap Q t) := by
    rw [Measure.map_dirac Q]
    simp [moveAtomMap]
  have hatomic : (atomicMeasure z hz : Measure Overlap).map (moveAtomMap Q t)=atomicMeasure z hz := by
    apply (Measure.map_congr ?_).trans Measure.map_id
    have hno : ∀ᵐq ∂(atomicMeasure z hz : Measure Overlap),q≠Q := by
      rw [ae_iff]
      simpa only [not_not,Set.setOf_eq_eq_singleton] using atomicMeasure_singleton_above z hz Q hQ
    filter_upwards [hno] with q hq
    simp only [moveAtomMap,ite_eq_right hq,id_eq]
  simp only [Measure.toProbabilityMeasure,ProbabilityMeasure.toMeasure] at *
  rw [hdirac,hatomic]
  simpa only [Measure.toProbabilityMeasure,ProbabilityMeasure.toMeasure] using
    (Paper.parisiMix_measure (Measure.dirac (movedOverlap Q t)).toProbabilityMeasure
      (atomicMeasure z hz) m hm).symm

theorem hasDerivAt_twoLevelFunctional_top (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (Q : Overlap) (hQ : atomicLocation z (Fin.last r)<(Q:ℝ)) (hQ1 : (Q:ℝ)<1) :
    HasDerivAt (fun t => twoLevelFunctional Ξ z hz m (movedOverlap Q t))
      (-(1-m)/2*Ξ.second Q*(Gamma Ξ (twoLevelMeasure z hz m Q) Q-(Q:ℝ))) 0 := by
  have hQ0 : 0 < (Q:ℝ) := (atomicLocation_mem_unit hz (Fin.last r)).1.trans_lt hQ
  have H := hasDerivAt_parisiFunctional_moveAtom Ξ (twoLevelMeasure z hz m Q) Q ⟨hQ0,hQ1⟩
  simp_rw [moveAtom_twoLevel_top z hz m hm Q hQ] at H
  rw [atomWeight_twoLevel_top z hz m hm Q hQ] at H
  convert H using 1 <;> dsimp only [firstVariationDerivative,twoLevelFunctional] <;> ring

end GeneralDepthPaper
