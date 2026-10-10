module

public import DepthPaper.GardnerCandidates

@[expose] public section


/-! Contact geometry and the actual candidate Hessian together give the
manuscript's full nondegeneracy, in the literal atomic coordinates. -/
noncomputable section
open Set MeasureTheory
namespace DepthPaper
set_option maxHeartbeats 1600000

theorem MassOneGardnerGeometry.nondegenerate {r : ℕ} {X : AdmissibleCovariance}
    {z : AtomicPoint r} {hz : IsAtomicPoint z} {Q : Overlap} {critical lam : ℝ}
    (H : MassOneGardnerGeometry X z hz Q critical lam) (hlt : lam<critical)
    (hH : positiveAtomicHessian X z) : Nondegenerate X z hz := by
  obtain ⟨hle,hzero,hcurv⟩:=H.2.1 hlt
  exact nondegenerate_of_geometry X z hz (H.1 hlt.le).1 hle hzero hcurv hH

theorem InteriorGardnerGeometry.nondegenerate {r : ℕ} {X : AdmissibleCovariance}
    {z : AtomicPoint r} {hz : IsAtomicPoint z} {m : ℝ} {Q : Overlap}
    (H : InteriorGardnerGeometry X z hz m Q)
    (hH : positiveAtomicHessian X (twoLevelAtomicCoordinates (z,m,(Q:ℝ)))) :
    Nondegenerate X (twoLevelAtomicCoordinates (z,m,(Q:ℝ)))
      (isAtomicPoint_twoLevelCoordinates z hz m Q H.1 H.2.1 H.2.2.1) := by
  let w:=twoLevelAtomicCoordinates (z,m,(Q:ℝ))
  let hw:=isAtomicPoint_twoLevelCoordinates z hz m Q H.1 H.2.1 H.2.2.1
  have hmeasure : atomicMeasure w hw=twoLevelMeasure z hz m Q:=
    atomicMeasure_twoLevelCoordinates z hz m H.1 Q H.2.1 H.2.2.1
  apply nondegenerate_of_geometry X w hw
  · rw [hmeasure]
    exact H.2.2.2.1
  · rw [hmeasure]
    exact H.2.2.2.2.2.1
  · rw [hmeasure]
    exact H.2.2.2.2.2.2.1
  · intro i
    rw [hmeasure]
    refine Fin.lastCases ?_ (fun j=>?_) i
    · change deriv (deriv (firstVariation X (twoLevelMeasure z hz m Q)))
        ((twoLevelAtomicCoordinates (z,m,(Q:ℝ))).1 (Fin.last r))<0
      rw [twoLevelAtomicCoordinates_location_last]
      exact H.2.2.2.2.2.2.2.2
    · change deriv (deriv (firstVariation X (twoLevelMeasure z hz m Q)))
        ((twoLevelAtomicCoordinates (z,m,(Q:ℝ))).1 j.castSucc)<0
      rw [twoLevelAtomicCoordinates_location_castSucc]
      exact H.2.2.2.2.2.2.2.1 j
  · exact hH

end DepthPaper
