module

public import DepthPaper.RevisedAtomicStationary
public import DepthPaper.RevisedAtomicContactLine
public import DepthPaper.RevisedAtomicMassLine
public import DepthPaper.RevisedControlSecondDerivative
public import DepthPaper.RevisedControlInjectivity
public import DepthPaper.RevisedAtomicControlComparison

@[expose] public section

/-! Revised finite-step nondegeneracy and the genuine atomic Hessian.
The nondegeneracy definition contains the paper's mathematical conditions,
without assuming a positive Hessian as part of the data. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace DepthPaper.RevisedCovariance
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 64

def positiveAtomicHessian (Ξ : RevisedCovariance) {r : ℕ} (z : AtomicPoint r) : Prop :=
  ∀v : AtomicPoint r,v≠0 →
    0<(fderiv ℝ (fun y=>fderiv ℝ (atomicFunctionalExtension Ξ r) y) z v) v

def Nondegenerate (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) : Prop :=
  IsParisiMinimizer Ξ (atomicMeasure z hz) ∧
    (∀q∈Icc (0:ℝ) 1,firstVariation Ξ (atomicMeasure z hz) q≤0 ∧
      (firstVariation Ξ (atomicMeasure z hz) q=0 ↔ ∃i,q=atomicLocation z i)) ∧
    (∀i : Fin r,closedJet 1 2 (firstVariation Ξ (atomicMeasure z hz)) (z.1 i)<0)

theorem positiveAtomicHessian_zero_depth (Ξ : RevisedCovariance) (z : AtomicPoint 0) :
    positiveAtomicHessian Ξ z := by
  intro v hv
  exact False.elim (hv (Subsingleton.elim _ _))

theorem atomic_hessian_location_lower_bound_of_contacts (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (hcontact : ∀i : Fin (r+1),firstVariation Ξ (atomicMeasure z hz) (atomicLocation z i)=0)
    (hprime : ∀i : Fin r,deriv (firstVariation Ξ (atomicMeasure z hz)) (z.1 i)=0)
    (v : AtomicPoint r) :
    -(∑i : Fin r,atomicWeight z i.succ*
      deriv (deriv (firstVariation Ξ (atomicMeasure z hz))) (z.1 i)*(v.1 i)^2) ≤
      (fderiv ℝ (fderiv ℝ (atomicFunctionalExtension Ξ r)) z v) v := by
  let f := firstVariation Ξ (atomicMeasure z hz)
  let F : ℝ → ℝ := fun t => atomicFunctionalExtension Ξ r (z+t • v)
  let S := atomicContactIntegralLine f z v
  let G : ℝ → ℝ := fun t => F 0-S t
  have hintegral : ∫q : Overlap,firstVariation Ξ (atomicMeasure z hz) q ∂(atomicMeasure z hz)=0 := by
    rw [integral_atomicMeasure]
    apply Finset.sum_eq_zero
    intro i _
    change atomicWeight z i*firstVariation Ξ (atomicMeasure z hz) (atomicLocation z i)=0
    rw [hcontact i,mul_zero]
  have hq (i : Fin r) : z.1 i∈Ioo (0:ℝ) 1 :=
    ⟨by simpa only [atomicLocation_zero,atomicLocation_succ] using hz.1 (Fin.succ_pos i),
      (hz.1.monotone (Fin.le_last i.succ)).trans_lt hz.2.1⟩
  have hf (i : Fin r) : ContDiffAt ℝ 2 f (z.1 i) :=
    contDiffAt_firstVariation_two Ξ (atomicMeasure z hz) (hq i)
  have hF : ContDiffAt ℝ 2 F 0 := by
    have hb : ContDiffAt ℝ 2 (atomicFunctionalExtension Ξ r) (z+(0 : ℝ) • v) := by
      simpa using (contDiffAt_atomicFunctionalExtension Ξ z hz).of_le (by simp)
    exact hb.comp (0 : ℝ) (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
  have hS : ContDiffAt ℝ 2 S 0 := contDiffAt_atomicContactIntegralLine f z v hf
  have hG : ContDiffAt ℝ 2 G 0 := contDiffAt_const.sub hS
  have hS0 : S 0=0 := by
    change (∑i : Fin r,atomicWeight (z+(0 : ℝ) • v) i.succ*f ((z+(0 : ℝ) • v).1 i))=0
    simp only [zero_smul,add_zero]
    apply Finset.sum_eq_zero
    intro i _
    have hi := hcontact i.succ
    change f (z.1 i)=0 at hi
    rw [hi,mul_zero]
  have hFG : ∀ᶠ t in 𝓝 (0 : ℝ),G t≤F t := by
    filter_upwards [atomicMassLine_eventually_valid z v hz] with t ht
    have hp := firstVariation_supporting_plane Ξ (atomicMeasure z hz) (atomicMeasure (z+t • v) ht)
    rw [hintegral,
      integral_atomicMeasure_affine_contact_line f z v t ht (firstVariation_zero Ξ _)] at hp
    change -(S t-0)≤parisiFunctional Ξ (atomicMeasure (z+t • v) ht)-
      parisiFunctional Ξ (atomicMeasure z hz) at hp
    have hFt : F t=parisiFunctional Ξ (atomicMeasure (z+t • v) ht) :=
      atomicFunctionalExtension_eq Ξ _ ht
    have hF0 : F 0=parisiFunctional Ξ (atomicMeasure z hz) := by
      simpa only [F,zero_smul,add_zero] using atomicFunctionalExtension_eq Ξ z hz
    dsimp only [G]
    rw [hFt,hF0]
    linarith
  have hF2 := hasDerivAt_deriv_affine_line
    ((contDiffAt_atomicFunctionalExtension Ξ z hz).of_le (by simp)) (v:=v)
  have hS2 := hasDerivAt_deriv_atomicContactIntegralLine f z v hf hprime
  have hG2 : HasDerivAt (deriv G)
      (-(∑i : Fin r,atomicWeight z i.succ*deriv (deriv f) (z.1 i)*(v.1 i)^2)) 0 := by
    have he : deriv G = -deriv S := by
      funext t
      simp only [G,deriv_const_sub',Pi.neg_apply]
    rw [he]
    exact hS2.neg
  exact secondDerivative_le_of_touching hFG (by dsimp only [G];rw [hS0,sub_zero])
    ((hF.eventually (by norm_num)).mono fun _ ht=>ht.differentiableAt (by norm_num))
    ((hG.eventually (by norm_num)).mono fun _ ht=>ht.differentiableAt (by norm_num)) hF2 hG2

theorem atomic_hessian_location_lower_bound (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (hmin : IsParisiMinimizer Ξ (atomicMeasure z hz)) (v : AtomicPoint r) :
    -(∑i : Fin r,atomicWeight z i.succ*
      deriv (deriv (firstVariation Ξ (atomicMeasure z hz))) (z.1 i)*(v.1 i)^2) ≤
      (fderiv ℝ (fderiv ℝ (atomicFunctionalExtension Ξ r)) z v) v := by
  have hcontact := atomic_minimizer_contacts Ξ z hz hmin
  exact atomic_hessian_location_lower_bound_of_contacts Ξ z hz hcontact.2.1 hcontact.2.2 v

theorem atomic_hessian_pos_of_location_ne_zero_of_contacts (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (hcontact : ∀i : Fin (r+1),firstVariation Ξ (atomicMeasure z hz) (atomicLocation z i)=0)
    (hprime : ∀i : Fin r,deriv (firstVariation Ξ (atomicMeasure z hz)) (z.1 i)=0)
    (hcurv : ∀i : Fin r,closedJet 1 2 (firstVariation Ξ (atomicMeasure z hz)) (z.1 i)<0)
    (v : AtomicPoint r) (hv : v.1≠0) :
    0<(fderiv ℝ (fderiv ℝ (atomicFunctionalExtension Ξ r)) z v) v := by
  have hq (i : Fin r) : z.1 i∈Ioo (0:ℝ) 1 :=
    ⟨by simpa only [atomicLocation_zero,atomicLocation_succ] using hz.1 (Fin.succ_pos i),
      (hz.1.monotone (Fin.le_last i.succ)).trans_lt hz.2.1⟩
  have hneg (i : Fin r) : deriv (deriv (firstVariation Ξ (atomicMeasure z hz))) (z.1 i)<0 := by
    simpa only [closedJet_two_eq_deriv_of_mem_Ioo _ (hq i)] using hcurv i
  have hcoef (i : Fin r) : 0 < -(atomicWeight z i.succ*
      deriv (deriv (firstVariation Ξ (atomicMeasure z hz))) (z.1 i)) :=
    neg_pos.mpr (mul_neg_of_pos_of_neg (hz.2.2 i.succ) (hneg i))
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hv
  have hsum : 0<∑i : Fin r,-(atomicWeight z i.succ*
      deriv (deriv (firstVariation Ξ (atomicMeasure z hz))) (z.1 i))*(v.1 i)^2 := by
    apply Finset.sum_pos'
    · intro j _
      exact mul_nonneg (hcoef j).le (sq_nonneg _)
    · exact ⟨i,Finset.mem_univ i,mul_pos (hcoef i) (sq_pos_of_ne_zero hi)⟩
  have hbound := atomic_hessian_location_lower_bound_of_contacts Ξ z hz hcontact hprime v
  have he : -(∑i : Fin r,atomicWeight z i.succ*
      deriv (deriv (firstVariation Ξ (atomicMeasure z hz))) (z.1 i)*(v.1 i)^2)=
      ∑i : Fin r,-(atomicWeight z i.succ*
        deriv (deriv (firstVariation Ξ (atomicMeasure z hz))) (z.1 i))*(v.1 i)^2 := by
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he] at hbound
  exact hsum.trans_le hbound

theorem atomic_hessian_pos_of_location_ne_zero (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (hmin : IsParisiMinimizer Ξ (atomicMeasure z hz))
    (hcurv : ∀i : Fin r,closedJet 1 2 (firstVariation Ξ (atomicMeasure z hz)) (z.1 i)<0)
    (v : AtomicPoint r) (hv : v.1≠0) :
    0<(fderiv ℝ (fderiv ℝ (atomicFunctionalExtension Ξ r)) z v) v := by
  have hcontact := atomic_minimizer_contacts Ξ z hz hmin
  exact atomic_hessian_pos_of_location_ne_zero_of_contacts Ξ z hz
    hcontact.2.1 hcontact.2.2 hcurv v hv

theorem atomic_hessian_pos_of_pure_mass (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (v : AtomicPoint r) (hv : v.1=0) (hv₀ : v≠0) :
    0<(fderiv ℝ (fderiv ℝ (atomicFunctionalExtension Ξ r)) z v) v := by
  have hvalid : ∀ᶠt in 𝓝[>] (0 : ℝ),IsAtomicPoint (z+t • v) :=
    (atomicMassLine_eventually_valid z v hz).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠt in 𝓝[>] (0 : ℝ),0<t := self_mem_nhdsWithin
  obtain ⟨ε,hεz,hεpos⟩ := (hvalid.and hpos).exists
  have hε : ε≠0 := hεpos.ne'
  let μ := atomicMeasure z hz
  let ν := atomicMeasure (z+ε • v) hεz
  have hne : ν≠μ := atomicMassLine_measure_ne z v hz hv hv₀ ε hε hεz
  let F : ℝ → ℝ := fun t => atomicFunctionalExtension Ξ r (z+t • v)
  let G : ℝ → ℝ := fixedControlComparison Ξ μ ν ε
  have hF : ContDiffAt ℝ 2 F 0 := by
    have hb : ContDiffAt ℝ 2 (atomicFunctionalExtension Ξ r) (z+(0 : ℝ) • v) := by
      simpa using (contDiffAt_atomicFunctionalExtension Ξ z hz).of_le (by simp)
    exact hb.comp (0 : ℝ) (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
  have hFG : ∀ᶠt in 𝓝 (0 : ℝ),G t≤F t := by
    filter_upwards [atomicMassLine_eventually_valid z v hz] with t ht
    have hcmp := fixedControlComparison_le Ξ μ ν (atomicMeasure (z+t • v) ht) ε t
      (fun q _=>parisiCDF_atomic_mass_line_affine z v hz hv ε hε hεz t ht q)
      (parisiCDF_mixed_atomic_mass_line_affine Ξ.toEvenMixture z v hz hv ε hε hεz t ht)
    change G t≤atomicFunctionalExtension Ξ r (z+t • v)
    rw [atomicFunctionalExtension_eq Ξ _ ht]
    exact hcmp
  have hGF : G 0=F 0 := by
    rw [show F 0=parisiFunctional Ξ μ by
      simpa only [F,zero_smul,add_zero] using atomicFunctionalExtension_eq Ξ z hz]
    exact fixedControlComparison_zero Ξ μ ν ε
  have hF₂ := hasDerivAt_deriv_affine_line
    ((contDiffAt_atomicFunctionalExtension Ξ z hz).of_le (by simp)) (v:=v)
  have hG₂ := hasDerivAt_deriv_fixedControlComparison Ξ μ ν ε
  have hbound := secondDerivative_le_of_touching hFG hGF
    ((hF.eventually (by norm_num)).mono fun _ ht=>ht.differentiableAt (by norm_num))
    (.of_forall fun t=>differentiableAt_fixedControlComparison Ξ μ ν ε t) hF₂ hG₂
  exact (div_pos (fixedControlCurvature_pos Ξ μ ν hne) (sq_pos_of_ne_zero hε)).trans_le hbound

theorem positiveAtomicHessian_of_contacts_curvature (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (hcontact : ∀i : Fin (r+1),firstVariation Ξ (atomicMeasure z hz) (atomicLocation z i)=0)
    (hprime : ∀i : Fin r,deriv (firstVariation Ξ (atomicMeasure z hz)) (z.1 i)=0)
    (hcurv : ∀i : Fin r,closedJet 1 2 (firstVariation Ξ (atomicMeasure z hz)) (z.1 i)<0) :
    positiveAtomicHessian Ξ z := by
  intro v hv₀
  by_cases hv : v.1=0
  · exact atomic_hessian_pos_of_pure_mass Ξ z hz v hv hv₀
  · exact atomic_hessian_pos_of_location_ne_zero_of_contacts Ξ z hz hcontact hprime hcurv v hv

/-- Positive definiteness is derived from global minimality and negative
contact curvature; it is not assumed in the revised definition. -/
theorem positiveAtomicHessian_of_minimizer_curvature (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (hmin : IsParisiMinimizer Ξ (atomicMeasure z hz))
    (hcurv : ∀i : Fin r,closedJet 1 2 (firstVariation Ξ (atomicMeasure z hz)) (z.1 i)<0) :
    positiveAtomicHessian Ξ z := by
  intro v hv₀
  by_cases hv : v.1=0
  · exact atomic_hessian_pos_of_pure_mass Ξ z hz v hv hv₀
  · exact atomic_hessian_pos_of_location_ne_zero Ξ z hz hmin hcurv v hv

theorem positiveAtomicHessian_of_nondegenerate (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (hND : Nondegenerate Ξ z hz) :
    positiveAtomicHessian Ξ z :=
  positiveAtomicHessian_of_minimizer_curvature Ξ z hz hND.1 hND.2.2

end DepthPaper.RevisedCovariance
