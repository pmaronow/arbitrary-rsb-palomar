module

public import DepthPaper.PartialAtomicDerivative
public import DepthPaper.PartialAtomicSmooth

@[expose] public section


/-! Corollary 2.3 with the actual Fréchet derivative of the actual partial
atomic Parisi functional. The zero-dimensional chart is included. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace DepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem fderiv_partialAtomicFunctional_location {r : ℕ} (Ξ : AdmissibleCovariance)
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Ioc (0:ℝ) 1)
    (Q : Overlap) (hQ : atomicLocation z (Fin.last r)<(Q:ℝ) ∧ (Q:ℝ)<1) (i : Fin r) :
    fderiv ℝ (partialAtomicFunctionalExtension Ξ r m Q) z (atomicLocationDirection i)=
      -(m*atomicWeight z i.succ)*firstVariationDerivative Ξ
        (partialAtomicMeasure z hz m Q) (z.1 i) := by
  have hF:=(contDiffAt_partialAtomicFunctionalExtension Ξ z hz m hm Q hQ).differentiableAt (by norm_num)
  have hpath := ((hasDerivAt_id (0:ℝ)).smul_const (atomicLocationDirection i)).const_add z
  have houter : HasFDerivAt (partialAtomicFunctionalExtension Ξ r m Q)
      (fderiv ℝ (partialAtomicFunctionalExtension Ξ r m Q) z)
      (z+(0:ℝ) • atomicLocationDirection i) := by simpa using hF.hasFDerivAt
  have hd:=houter.comp_hasDerivAt 0 hpath
  have he:=hasDerivAt_partialAtomicLocationFunctional Ξ z hz m ⟨hm.1.le,hm.2⟩ Q i
  simpa only [Function.comp_def,atomicLocationPath,id_eq,one_smul] using hd.unique he

theorem fderiv_partialAtomicFunctional_mass {r : ℕ} (Ξ : AdmissibleCovariance)
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Ioc (0:ℝ) 1)
    (Q : Overlap) (hQ : atomicLocation z (Fin.last r)<(Q:ℝ) ∧ (Q:ℝ)<1) (i : Fin r) :
    fderiv ℝ (partialAtomicFunctionalExtension Ξ r m Q) z (atomicMassDirection i)=
      m*(firstVariation Ξ (partialAtomicMeasure z hz m Q) (atomicLocation z (Fin.last r))-
        firstVariation Ξ (partialAtomicMeasure z hz m Q) (atomicLocation z i.castSucc)) := by
  have hF:=(contDiffAt_partialAtomicFunctionalExtension Ξ z hz m hm Q hQ).differentiableAt (by norm_num)
  have hpath := ((hasDerivAt_id (0:ℝ)).smul_const (atomicMassDirection i)).const_add z
  have houter : HasFDerivAt (partialAtomicFunctionalExtension Ξ r m Q)
      (fderiv ℝ (partialAtomicFunctionalExtension Ξ r m Q) z)
      (z+(0:ℝ) • atomicMassDirection i) := by simpa using hF.hasFDerivAt
  have hd:=houter.comp_hasDerivAt 0 hpath
  have he:=hasDerivAt_partialAtomicMassFunctional Ξ z hz m ⟨hm.1.le,hm.2⟩ Q i
  simpa only [Function.comp_def,atomicMassPath,id_eq,one_smul] using hd.unique he

theorem atomicPoint_eq_sum_directions {r : ℕ} (v : AtomicPoint r) :
    v=(∑i:Fin r,v.1 i • atomicLocationDirection i)+(∑i:Fin r,v.2 i • atomicMassDirection i) := by
  classical
  apply Prod.ext
  · funext j
    simp [atomicLocationDirection,atomicMassDirection,Finset.sum_apply,Pi.single_apply,
      Prod.fst_sum]
  · funext j
    simp [atomicLocationDirection,atomicMassDirection,Finset.sum_apply,Pi.single_apply,
      Prod.snd_sum]

theorem atomicContinuousLinearMap_eq_zero_iff {r : ℕ} (L : AtomicPoint r→L[ℝ]ℝ) :
    L=0 ↔ (∀i,L (atomicLocationDirection i)=0) ∧ (∀i,L (atomicMassDirection i)=0) := by
  constructor
  · intro h
    subst L
    simp
  · rintro ⟨hq,hw⟩
    apply ContinuousLinearMap.ext
    intro v
    rw [atomicPoint_eq_sum_directions v,L.map_add]
    simp only [map_sum,map_smul,hq,hw,smul_zero,Finset.sum_const_zero,add_zero,
      ContinuousLinearMap.zero_apply]

theorem atomic_gradient_zero_iff {r : ℕ} (Ξ : AdmissibleCovariance)
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Ioc (0:ℝ) 1)
    (Q : Overlap) (hQ : atomicLocation z (Fin.last r)<(Q:ℝ) ∧ (Q:ℝ)<1) :
    fderiv ℝ (partialAtomicFunctionalExtension Ξ r m Q) z=0 ↔
      (∀q∈(atomicMeasure z hz : Measure Overlap).support,
        firstVariation Ξ (partialAtomicMeasure z hz m Q) q=0) ∧
      (∀q∈(atomicMeasure z hz : Measure Overlap).support,q≠⟨0,by norm_num⟩→
        firstVariationDerivative Ξ (partialAtomicMeasure z hz m Q) q=0) := by
  let μ:=partialAtomicMeasure z hz m Q
  rw [atomicContinuousLinearMap_eq_zero_iff]
  simp_rw [fderiv_partialAtomicFunctional_location Ξ z hz m hm Q hQ,
    fderiv_partialAtomicFunctional_mass Ξ z hz m hm Q hQ]
  rw [support_atomicMeasure]
  constructor
  · rintro ⟨hq,hw⟩
    have hprime (i : Fin r) : firstVariationDerivative Ξ μ (z.1 i)=0 := by
      have h:=hq i
      have hpos : 0 < m*atomicWeight z i.succ := mul_pos hm.1 (hz.2.2 i.succ)
      exact (mul_eq_zero.mp h).resolve_left (neg_ne_zero.mpr hpos.ne')
    have hlast : firstVariation Ξ μ (atomicLocation z (Fin.last r))=0 := by
      by_cases hr:r=0
      · subst r
        change firstVariation Ξ μ 0=0
        exact firstVariation_zero Ξ μ
      · let i:Fin r:=⟨0,Nat.pos_of_ne_zero hr⟩
        have h:=hw i
        have he := (mul_eq_zero.mp h).resolve_left hm.1.ne'
        have hi : i.castSucc=(0:Fin (r+1)) := rfl
        rw [hi,atomicLocation_zero,firstVariation_zero] at he
        exact sub_eq_zero.mp he
    constructor
    · rintro q ⟨i,rfl⟩
      refine Fin.lastCases ?_ (fun j=>?_) i
      · exact hlast
      · have h:=hw j
        have he:=(mul_eq_zero.mp h).resolve_left hm.1.ne'
        change firstVariation Ξ μ (atomicLocation z j.castSucc)=0
        linarith [sub_eq_zero.mp he]
    · rintro q ⟨i,rfl⟩ hne
      cases i using Fin.cases with
      | zero => exact False.elim (hne rfl)
      | succ j => exact hprime j
  · rintro ⟨hzf,hzp⟩
    constructor
    · intro i
      have hne : atomicOverlap z hz i.succ≠⟨0,by norm_num⟩ := by
        intro he
        have hi:=congrArg (fun q:Overlap=>(q:ℝ)) he
        have hp:=hz.1 (Fin.succ_pos i)
        simp only [atomicOverlap,atomicLocation_zero,atomicLocation_succ] at hi hp
        linarith
      have he:=hzp (atomicOverlap z hz i.succ) ⟨i.succ,rfl⟩ hne
      change firstVariationDerivative Ξ μ (z.1 i)=0 at he
      change -(m*atomicWeight z i.succ)*firstVariationDerivative Ξ μ (z.1 i)=0
      rw [he,mul_zero]
    · intro i
      have hi:=hzf (atomicOverlap z hz i.castSucc) ⟨i.castSucc,rfl⟩
      have hl:=hzf (atomicOverlap z hz (Fin.last r)) ⟨Fin.last r,rfl⟩
      change firstVariation Ξ μ (atomicLocation z i.castSucc)=0 at hi
      change firstVariation Ξ μ (atomicLocation z (Fin.last r))=0 at hl
      change m*(firstVariation Ξ μ (atomicLocation z (Fin.last r))-
        firstVariation Ξ μ (atomicLocation z i.castSucc))=0
      rw [hi,hl,sub_self,mul_zero]

/-- Literal Corollary 2.3, including every depth and `m=1`. -/
theorem atomic_gradient {r : ℕ} (Ξ : AdmissibleCovariance)
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Ioc (0:ℝ) 1)
    (Q : Overlap) (hQ : atomicLocation z (Fin.last r)<(Q:ℝ) ∧ (Q:ℝ)<1) :
    (∀i : Fin r,HasDerivAt
      (fun t=>partialAtomicFunctionalExtension Ξ r m Q (atomicLocationPath z i t))
      (-(m*atomicWeight z i.succ)*firstVariationDerivative Ξ
        (partialAtomicMeasure z hz m Q) (z.1 i)) 0) ∧
    (∀i : Fin r,HasDerivAt
      (fun t=>partialAtomicFunctionalExtension Ξ r m Q (atomicMassPath z i t))
      (m*(firstVariation Ξ (partialAtomicMeasure z hz m Q) (atomicLocation z (Fin.last r))-
        firstVariation Ξ (partialAtomicMeasure z hz m Q) (atomicLocation z i.castSucc))) 0) ∧
    (fderiv ℝ (partialAtomicFunctionalExtension Ξ r m Q) z=0 ↔
      (∀q∈(atomicMeasure z hz : Measure Overlap).support,
        firstVariation Ξ (partialAtomicMeasure z hz m Q) q=0) ∧
      (∀q∈(atomicMeasure z hz : Measure Overlap).support,q≠⟨0,by norm_num⟩→
        firstVariationDerivative Ξ (partialAtomicMeasure z hz m Q) q=0)) :=
  ⟨hasDerivAt_partialAtomicLocationFunctional Ξ z hz m ⟨hm.1.le,hm.2⟩ Q,
    hasDerivAt_partialAtomicMassFunctional Ξ z hz m ⟨hm.1.le,hm.2⟩ Q,
    atomic_gradient_zero_iff Ξ z hz m hm Q hQ⟩

end DepthPaper
