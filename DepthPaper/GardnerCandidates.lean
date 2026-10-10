module

public import DepthPaper.GardnerPhaseGeometry

@[expose] public section


/-! Literal selected candidate measures of Definition 4.6. Their total
extensions agree with the actual valid atomic measures on the parameter
windows proved in the transition theorem. -/
noncomputable section
open Set
namespace DepthPaper

theorem IsFiniteRSB.unique_depth {r s : ℕ} {mu : ParisiMeasure}
    (hr : IsFiniteRSB r mu) (hs : IsFiniteRSB s mu) : r=s := by
  have hcard:=hr.2.symm.trans hs.2
  omega

namespace LimitingStandingData
variable {Ξ : AdmissibleCovariance} {r : ℕ} {seed : AtomicPoint r}

def massOneTop (d : LimitingStandingData Ξ seed) (p : ℕ) (lam : ℝ) : Overlap :=
  distinguishedOverlap Ξ p d.cutoff d.stripRateLower d.stripRateUpper
    (d.stationaryBranch p (lam,1),(1,lam))

def massOneCandidate (d : LimitingStandingData Ξ seed) (p : ℕ) (lam : ℝ) : ParisiMeasure :=
  atomicMeasureExtension r (d.stationaryBranch p (lam,1))

def interiorTop (d : LimitingStandingData Ξ seed) (p : ℕ) (lam : ℝ) : Overlap :=
  distinguishedOverlap Ξ p d.cutoff d.stripRateLower d.stripRateUpper
    (d.stationaryBranch p (lam,d.bifurcatingMass p lam),(d.bifurcatingMass p lam,lam))

def interiorCandidate (d : LimitingStandingData Ξ seed) (p : ℕ) (lam : ℝ) : ParisiMeasure :=
  partialAtomicMeasureExtension r (d.bifurcatingMass p lam) (d.interiorTop p lam)
    (d.stationaryBranch p (lam,d.bifurcatingMass p lam))

theorem massOneCandidate_eq (d : LimitingStandingData Ξ seed) (p : ℕ) (lam : ℝ)
    (hz : IsAtomicPoint (d.stationaryBranch p (lam,1))) :
    d.massOneCandidate p lam=atomicMeasure (d.stationaryBranch p (lam,1)) hz :=
  atomicMeasureExtension_eq _ _

theorem interiorCandidate_eq (d : LimitingStandingData Ξ seed) (p : ℕ) (lam : ℝ)
    (hz : IsAtomicPoint (d.stationaryBranch p (lam,d.bifurcatingMass p lam))) :
    d.interiorCandidate p lam=twoLevelMeasure (d.stationaryBranch p (lam,d.bifurcatingMass p lam))
      hz (d.bifurcatingMass p lam) (d.interiorTop p lam) :=
  partialAtomicMeasureExtension_eq _ _ _ _

theorem criticalCoupling_eq_entropy (d : LimitingStandingData Ξ seed) :
    d.criticalCoupling=2*((scaledThermodynamicPressure Ξ.toEvenMixture) 1-
      deriv (scaledThermodynamicPressure Ξ.toEvenMixture) 1) := by
  simp only [criticalCoupling,pressureEll,pressureEntropy,one_mul,one_pow,div_one]

end LimitingStandingData
end DepthPaper
