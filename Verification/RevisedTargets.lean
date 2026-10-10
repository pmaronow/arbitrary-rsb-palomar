module

public import GeneralDepthPaper.RevisedTransition
public import DepthPaper.RevisedGardnerTransition
public import DepthPaper.RevisedEntropy
public import DepthPaper.RevisedCriticalHessian
public import DepthPaper.RevisedSharpFirstVariation
public import DepthPaper.RevisedLargeVarianceSharp
public import DepthPaper.RevisedDoobComparison

@[expose] public section

/-!
# Complete types of the revised-paper results

The universal results below quantify over the quadratic-inclusive finite
covariance class and spell out the paper's seed condition. Atomic Hessian
positivity and pressure differentiability are proved dependencies, rather
than hypotheses supplied to these declarations. The expanded geometry and
asymptotic statements record the common constants, parameter windows,
physical-pressure normalization, and actual minimizing measures.

The supporting declarations check the six revised geometry/asymptotic
modules. The analytic declarations state the atomic Hessian, entropy, and
Appendix C conclusions directly, without proposition-valued target aliases.
-/

noncomputable section
open Set Filter MeasureTheory Asymptotics
open scoped Topology NNReal ContDiff

namespace Verification.RevisedTargets
open GeneralDepthPaper

/-- Universal transition under exactly paper nondegeneracy and subcriticality. -/
theorem universalTransition_exact (Ξ : AdmissibleCovariance) {r : ℕ}
    (seed : AtomicPoint r) (hz : IsAtomicPoint seed)
    (hsub : Ξ.second 0 < 1)
    (hmin : IsParisiMinimizer Ξ (atomicMeasure seed hz))
    (hcontact : ∀ q ∈ Icc (0 : ℝ) 1,
      firstVariation Ξ (atomicMeasure seed hz) q ≤ 0 ∧
      (firstVariation Ξ (atomicMeasure seed hz) q = 0 ↔
        ∃ i, q = atomicLocation seed i))
    (hcurv : ∀ i : Fin r,
      closedJet 1 2 (firstVariation Ξ (atomicMeasure seed hz)) (seed.1 i) < 0) :
    RevisedGardnerGeometryTarget Ξ seed ∧ RevisedGardnerAsymptoticsTarget Ξ seed :=
  universal_gardner_transition Ξ seed hz hsub ⟨hmin, hcontact, hcurv⟩

/-- Literal revised Theorem 1.2: positive entropy, a unique threshold, and both depth iff's. -/
theorem theorem1_2_exact (Ξ : AdmissibleCovariance) {r : ℕ}
    (seed : AtomicPoint r) (hz : IsAtomicPoint seed)
    (hsub : Ξ.second 0 < 1)
    (hmin : IsParisiMinimizer Ξ (atomicMeasure seed hz))
    (hcontact : ∀ q ∈ Icc (0 : ℝ) 1,
      firstVariation Ξ (atomicMeasure seed hz) q ≤ 0 ∧
      (firstVariation Ξ (atomicMeasure seed hz) q = 0 ↔
        ∃ i, q = atomicLocation seed i))
    (hcurv : ∀ i : Fin r,
      closedJet 1 2 (firstVariation Ξ (atomicMeasure seed hz)) (seed.1 i) < 0) :
    let pressure := scaledThermodynamicPressure Ξ.toEvenMixture
    let s := pressure 1 - deriv pressure 1
    0 < s ∧ ∃ η : ℝ, η ∈ Ioo (0 : ℝ) (2 * s) ∧ ∃ critical : ℕ → ℝ,
      Tendsto critical (atTop ⊓ 𝓟 {p : ℕ | Even p}) (𝓝 (2 * s)) ∧
      ∀ᶠ p : ℕ in atTop, ∀ he : Even p, ∃ hp : 4 ≤ p, ∃ hn : p ∉ Ξ.degrees,
        critical p ∈ Ioo (2 * s - η) (2 * s + η) ∧
        (∀ lam : ℝ, ∀ _hlam : lam ∈ Icc (2 * s - η) (2 * s + η),
          0 < lam ∧ ∀ hpos : 0 < lam,
            let X := Ξ.addHighDegree p hp he hn lam hpos
            (IsFiniteRSB r (parisiMinimizer X) ↔ lam ≤ critical p) ∧
            (IsFiniteRSB (r + 1) (parisiMinimizer X) ↔ critical p < lam)) ∧
        (∀ c ∈ Ioo (2 * s - η) (2 * s + η),
          (∀ lam : ℝ, ∀ _hlam : lam ∈ Icc (2 * s - η) (2 * s + η), ∀ hpos : 0 < lam,
            let X := Ξ.addHighDegree p hp he hn lam hpos
            (IsFiniteRSB r (parisiMinimizer X) ↔ lam ≤ c) ∧
            (IsFiniteRSB (r + 1) (parisiMinimizer X) ↔ c < lam)) → c = critical p) :=
  gardner_transition_theorem_1_2 Ξ seed hz hsub ⟨hmin, hcontact, hcurv⟩

/-- Expanded revised Theorem 4.12: one support cutoff and location constant. -/
theorem geometry_exact (Ξ : AdmissibleCovariance) {r : ℕ}
    (seed : AtomicPoint r) (hz : IsAtomicPoint seed)
    (hsub : Ξ.second 0 < 1)
    (hmin : IsParisiMinimizer Ξ (atomicMeasure seed hz))
    (hcontact : ∀ q ∈ Icc (0 : ℝ) 1,
      firstVariation Ξ (atomicMeasure seed hz) q ≤ 0 ∧
      (firstVariation Ξ (atomicMeasure seed hz) q = 0 ↔
        ∃ i, q = atomicLocation seed i))
    (hcurv : ∀ i : Fin r,
      closedJet 1 2 (firstVariation Ξ (atomicMeasure seed hz)) (seed.1 i) < 0) :
    ∃ d : LimitingStandingData Ξ seed,
      d.couplingMargin ∈ Ioo (0 : ℝ) d.criticalCoupling ∧
      d.cutoff ∈ Ioo (0 : ℝ) 1 ∧
      d.criticalCoupling = 2 * (scaledThermodynamicPressure Ξ.toEvenMixture 1 -
        deriv (scaledThermodynamicPressure Ξ.toEvenMixture) 1) ∧
      Tendsto (fun p : ℕ => d.couplingCurve p 1)
        (atTop ⊓ 𝓟 {p : ℕ | Even p}) (𝓝 d.criticalCoupling) ∧
      ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ p : ℕ in atTop, 4 ≤ p ∧ ∀ he : Even p,
        ∃ hp : 4 ≤ p, ∃ hn : p ∉ Ξ.degrees,
          d.couplingCurve p 1 ∈ Ioo (d.criticalCoupling - d.couplingMargin)
            (d.criticalCoupling + d.couplingMargin) ∧
          ∀ lam : ℝ, ∀ hlam : lam ∈ d.transitionWindow,
            let X := Ξ.addHighDegree p hp he hn lam (d.transition_coupling_pos hlam)
            let critical := d.couplingCurve p 1
            ((lam ≤ critical → d.massOneCandidate p lam = parisiMinimizer X ∧
              IsFiniteRSB r (parisiMinimizer X)) ∧
            (lam < critical →
              {q ∈ Icc (0 : ℝ) 1 | firstVariation X (d.massOneCandidate p lam) q = 0} =
                FRSB.parisiSupport (d.massOneCandidate p lam)) ∧
            (lam = critical →
              {q ∈ Icc (0 : ℝ) 1 | firstVariation X (d.massOneCandidate p lam) q = 0} =
                FRSB.parisiSupport (d.massOneCandidate p lam) ∪ {(d.massOneTop p lam : ℝ)} ∧
              (d.massOneCandidate p lam : Measure Overlap) {d.massOneTop p lam} = 0) ∧
            (critical < lam → d.interiorCandidate p lam = parisiMinimizer X ∧
              IsFiniteRSB (r + 1) (parisiMinimizer X)) ∧
            (IsFiniteRSB r (parisiMinimizer X) ↔ lam ≤ critical) ∧
            (IsFiniteRSB (r + 1) (parisiMinimizer X) ↔ critical < lam)) ∧
            ((lam < critical →
              ∃ hz' : IsAtomicPoint (d.stationaryBranch p (lam, 1)),
                Nondegenerate X (d.stationaryBranch p (lam, 1)) hz') ∧
            (critical < lam →
              ∃ hw : IsAtomicPoint (twoLevelAtomicCoordinates
                (d.stationaryBranch p (lam, d.bifurcatingMass p lam),
                  d.bifurcatingMass p lam, (d.interiorTop p lam : ℝ))),
                Nondegenerate X (twoLevelAtomicCoordinates
                  (d.stationaryBranch p (lam, d.bifurcatingMass p lam),
                    d.bifurcatingMass p lam, (d.interiorTop p lam : ℝ))) hw)) ∧
            (lam ≤ critical →
              FRSB.parisiSupport (parisiMinimizer X) ⊆ Icc (0 : ℝ) d.cutoff ∧
              (d.massOneTop p lam : ℝ) ∈ Ioo d.cutoff 1 ∧
              C⁻¹ * (p : ℝ) ^ (-(1 / 2 : ℝ)) *
                Real.exp (-(1 : ℝ) ^ 2 * lam * (p : ℝ) / 2) ≤
                  1 - (d.massOneTop p lam : ℝ) ∧
              1 - (d.massOneTop p lam : ℝ) ≤ C * (p : ℝ) ^ (-(1 / 2 : ℝ)) *
                Real.exp (-(1 : ℝ) ^ 2 * lam * (p : ℝ) / 2)) ∧
            (lam = critical →
              (∀ q ∈ Icc (0 : ℝ) 1, firstVariation X (parisiMinimizer X) q ≤ 0) ∧
              {q ∈ Icc (0 : ℝ) 1 | firstVariation X (parisiMinimizer X) q = 0} =
                FRSB.parisiSupport (parisiMinimizer X) ∪ {(d.massOneTop p lam : ℝ)} ∧
              (d.massOneTop p lam : ℝ) ∉ FRSB.parisiSupport (parisiMinimizer X) ∧
              (parisiMinimizer X : Measure Overlap) {d.massOneTop p lam} = 0) ∧
            (critical < lam →
              ∃ hz' : IsAtomicPoint (d.stationaryBranch p (lam, d.bifurcatingMass p lam)),
                let z := d.stationaryBranch p (lam, d.bifurcatingMass p lam)
                let m := d.bifurcatingMass p lam
                parisiMinimizer X = twoLevelMeasure z hz' m (d.interiorTop p lam) ∧
                m ∈ Ioo (0 : ℝ) 1 ∧
                IsFiniteRSB r (atomicMeasure z hz') ∧
                FRSB.parisiSupport (atomicMeasure z hz') ⊆ Icc (0 : ℝ) d.cutoff ∧
                (d.interiorTop p lam : ℝ) ∈ Ioo d.cutoff 1 ∧
                C⁻¹ * (p : ℝ) ^ (-(1 / 2 : ℝ)) *
                  Real.exp (-m ^ 2 * lam * (p : ℝ) / 2) ≤
                    1 - (d.interiorTop p lam : ℝ) ∧
                1 - (d.interiorTop p lam : ℝ) ≤ C * (p : ℝ) ^ (-(1 / 2 : ℝ)) *
                  Real.exp (-m ^ 2 * lam * (p : ℝ) / 2)) :=
  revised_gardner_geometry_of_paper_nondegenerate Ξ seed hz hsub ⟨hmin, hcontact, hcurv⟩

/-- Expanded revised Corollary 5.2, including the diagonal small-o law. -/
theorem asymptotics_exact (Ξ : AdmissibleCovariance) {r : ℕ}
    (seed : AtomicPoint r) (hz : IsAtomicPoint seed)
    (hsub : Ξ.second 0 < 1)
    (hmin : IsParisiMinimizer Ξ (atomicMeasure seed hz))
    (hcontact : ∀ q ∈ Icc (0 : ℝ) 1,
      firstVariation Ξ (atomicMeasure seed hz) q ≤ 0 ∧
      (firstVariation Ξ (atomicMeasure seed hz) q = 0 ↔
        ∃ i, q = atomicLocation seed i))
    (hcurv : ∀ i : Fin r,
      closedJet 1 2 (firstVariation Ξ (atomicMeasure seed hz)) (seed.1 i) < 0) :
    ∃ d : LimitingStandingData Ξ seed,
      d.couplingMargin ∈ Ioo (0 : ℝ) d.criticalCoupling ∧
      0 < pressureKappa (scaledThermodynamicPressure Ξ.toEvenMixture) ∧
      (∀ᶠ p : ℕ in atTop, ∀ _he : Even p, ∀ theta ∈ d.parameterWindow,
        HasDerivAt (fun m => d.revisedScalarObjective p (theta.1, m))
          (d.stationaryMassFunction p theta) theta.2) ∧
      Tendsto d.revisedBifurcationKappa (atTop ⊓ 𝓟 {p : ℕ | Even p})
        (𝓝 (pressureKappa (scaledThermodynamicPressure Ξ.toEvenMixture))) ∧
      ∃ C : ℝ, 1 ≤ C ∧
        (∀ᶠ p : ℕ in atTop, 4 ≤ p ∧ ∀ he : Even p,
          ∃ hp : 4 ≤ p, ∃ hn : p ∉ Ξ.degrees,
            |d.couplingCurve p 1 - d.criticalCoupling| < d.couplingMargin / 2 ∧
            0 < d.revisedCriticalCouplingPartial p ∧
            0 < d.revisedCriticalMassPartial p ∧
            0 < d.revisedBifurcationKappa p ∧
            ∀ δ ∈ Ioc (0 : ℝ) (d.couplingMargin / 2),
              let lam := d.couplingCurve p 1 + δ
              ∃ hlam : lam ∈ d.transitionWindow,
                let X := Ξ.addHighDegree p hp he hn lam (d.transition_coupling_pos hlam)
                d.interiorCandidate p lam = parisiMinimizer X ∧
                d.newAtomMass p lam = 1 - d.bifurcatingMass p lam ∧
                |d.newAtomMass p lam - δ / (2 * d.revisedBifurcationKappa p)| ≤ C * δ ^ 2 ∧
                |Real.log (1 / (1 - (d.interiorTop p lam : ℝ))) -
                  d.bifurcatingMass p lam ^ 2 * lam * (p : ℝ) / 2 -
                  (1 / 2 : ℝ) * Real.log (p : ℝ)| ≤ C) ∧
        (∀ p : ℕ → ℕ, ∀ δ : ℕ → ℝ, Tendsto p atTop atTop →
          (∀ᶠ j in atTop, Even (p j)) → Tendsto δ atTop (𝓝 0) →
          (∀ᶠ j in atTop, 0 < δ j) →
          (fun j => d.newAtomMass (p j) (d.couplingCurve (p j) 1 + δ j) -
            δ j / (2 * pressureKappa (scaledThermodynamicPressure Ξ.toEvenMixture)))
              =o[atTop] δ) :=
  revised_gardner_asymptotics_of_paper_nondegenerate Ξ seed hz hsub ⟨hmin, hcontact, hcurv⟩

/-- The finite-mixture interface presents precisely the same universal result. -/
theorem finiteMixtureTransition_exact (Ξ : DepthPaper.RevisedCovariance) {r : ℕ}
    (seed : DepthPaper.AtomicPoint r) (hz : DepthPaper.IsAtomicPoint seed)
    (hsub : Ξ.second 0 < 1)
    (hnd : DepthPaper.RevisedCovariance.Nondegenerate Ξ seed hz) :
    RevisedGardnerGeometryTarget Ξ.toGeneralCovariance seed ∧
      RevisedGardnerAsymptoticsTarget Ξ.toGeneralCovariance seed :=
  DepthPaper.RevisedCovariance.universal_gardner_transition Ξ seed hz hsub hnd

/-- Revised derivative-ratio normalization and positivity. -/
theorem criticalPartials_exact {Ξ : AdmissibleCovariance} {r : ℕ}
    {seed : AtomicPoint r} (d : LimitingStandingData Ξ seed) :
    ∀ᶠ p : ℕ in atTop, ∀ _he : Even p,
      0 < d.revisedCriticalCouplingPartial p ∧
      0 < d.revisedCriticalMassPartial p ∧
      d.revisedBifurcationKappa p = d.bifurcationKappa p :=
  d.revisedCriticalPartials_eventually

/-- Exact scalar-objective envelope derivative, rather than a stipulated derivative. -/
theorem massDerivative_exact {Ξ : AdmissibleCovariance} {r : ℕ}
    {seed : AtomicPoint r} (d : LimitingStandingData Ξ seed) :
    ∀ᶠ p : ℕ in atTop, ∀ _he : Even p, ∀ theta ∈ d.parameterWindow,
      HasDerivAt (fun m => d.revisedScalarObjective p (theta.1, m))
        (d.stationaryMassFunction p theta) theta.2 :=
  d.revisedScalarObjective_massDerivative_eventually

/-- Exact common candidate support cutoff and endpoint scale. -/
theorem candidateLocation_exact {Ξ : AdmissibleCovariance} {r : ℕ}
    {seed : AtomicPoint r} (d : LimitingStandingData Ξ seed) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ p : ℕ in atTop, ∀ _he : Even p,
      ∀ theta ∈ d.parameterWindow, ∀ hz : IsAtomicPoint (d.stationaryBranch p theta),
        let z := d.stationaryBranch p theta
        let Q := distinguishedOverlap Ξ p d.cutoff d.stripRateLower d.stripRateUpper
          (z, (theta.2, theta.1))
        FRSB.parisiSupport (atomicMeasure z hz) ⊆ Icc (0 : ℝ) d.cutoff ∧
        (Q : ℝ) ∈ Ioo d.cutoff 1 ∧
        C⁻¹ * (p : ℝ) ^ (-(1 / 2 : ℝ)) *
          Real.exp (-theta.2 ^ 2 * theta.1 * (p : ℝ) / 2) ≤ 1 - (Q : ℝ) ∧
        1 - (Q : ℝ) ≤ C * (p : ℝ) ^ (-(1 / 2 : ℝ)) *
          Real.exp (-theta.2 ^ 2 * theta.1 * (p : ℝ) / 2) :=
  d.revisedCandidateLocation_eventually

/-- Exact logarithmic conversion of the two endpoint bounds. -/
theorem logarithmicLocation_exact {p x E C : ℝ} (hp : 0 < p) (hC : 1 ≤ C)
    (hlower : C⁻¹ * p ^ (-(1 / 2 : ℝ)) * Real.exp (-E) ≤ x)
    (hupper : x ≤ C * p ^ (-(1 / 2 : ℝ)) * Real.exp (-E)) :
    |Real.log (1 / x) - E - (1 / 2 : ℝ) * Real.log p| ≤ C :=
  logarithmic_location_of_two_sided hp hC hlower hupper

end Verification.RevisedTargets

namespace Verification.RevisedTargets
open DepthPaper

/-- Revised Lemma 2.6: chart criticality, contact curvature, actual Hessian. -/
theorem atomicHessian_exact (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (hs : fderiv ℝ (RevisedCovariance.atomicFunctionalExtension Ξ r) z = 0)
    (hcurv : ∀ i : Fin r,
      closedJet 1 2 (RevisedCovariance.firstVariation Ξ (atomicMeasure z hz)) (z.1 i) < 0) :
    ∀ v : AtomicPoint r, v ≠ 0 →
      0 < (fderiv ℝ (fun y => fderiv ℝ (RevisedCovariance.atomicFunctionalExtension Ξ r) y)
        z v) v :=
  RevisedCovariance.atomic_hessian Ξ z hz hs hcurv

/-- Revised Lemma 3.2: the actual temperature quotient is smooth on positive temperatures. -/
theorem entropySmooth_exact (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) :
    ContDiffOn ℝ ∞ (fun m : ℝ => m⁻¹ * RevisedCovariance.parisiFunctional
      ((RevisedCovariance.temperatureCovarianceFamily Ξ).covariance m) (atomicMeasure z hz))
        (Ioi (0 : ℝ)) :=
  RevisedCovariance.contDiffOn_entropyTemperatureFunctional Ξ z hz

/-- Revised Lemma 3.2: exact first variation and terminal spin-entropy identity. -/
theorem entropyIdentity_exact (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) :
    HasDerivAt (fun m : ℝ => m⁻¹ * RevisedCovariance.parisiFunctional
      ((RevisedCovariance.temperatureCovarianceFamily Ξ).covariance m) (atomicMeasure z hz))
      (RevisedCovariance.firstVariation Ξ (atomicMeasure z hz) 1 -
        (∫ q : Overlap, RevisedCovariance.firstVariation Ξ (atomicMeasure z hz) q
          ∂(atomicMeasure z hz : Measure Overlap)) -
        ∫ sample, revisedSpinEntropy
          (RevisedCovariance.optimalState Ξ (atomicMeasure z hz) sample 1)
            ∂Paper.canonicalBrownianMeasure) 1 :=
  RevisedCovariance.hasDerivAt_entropyTemperatureFunctional Ξ z hz

/-- Revised Corollary 3.3: physical entropy equals the diffusion formula and is positive. -/
theorem positiveEntropy_exact (Ξ : RevisedCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (hsub : Ξ.second 0 < 1)
    (hmin : RevisedCovariance.IsParisiMinimizer Ξ (atomicMeasure z hz))
    (hcontact : ∀ q ∈ Icc (0 : ℝ) 1,
      RevisedCovariance.firstVariation Ξ (atomicMeasure z hz) q ≤ 0 ∧
      (RevisedCovariance.firstVariation Ξ (atomicMeasure z hz) q = 0 ↔
        ∃ i, q = atomicLocation z i))
    (hcurv : ∀ i : Fin r,
      closedJet 1 2 (RevisedCovariance.firstVariation Ξ (atomicMeasure z hz)) (z.1 i) < 0) :
    thermodynamicEntropy Ξ.toEvenMixture =
      (∫ sample, revisedSpinEntropy
        (RevisedCovariance.optimalState Ξ (atomicMeasure z hz) sample 1)
          ∂Paper.canonicalBrownianMeasure) -
        RevisedCovariance.firstVariation Ξ (atomicMeasure z hz) 1 ∧
      0 < thermodynamicEntropy Ξ.toEvenMixture := by
  rw [← RevisedCovariance.diffusionEntropy_eq_thermodynamicEntropy]
  exact RevisedCovariance.diffusion_entropy Ξ hsub z hz ⟨hmin, hcontact, hcurv⟩

/-- Revised Appendix C.1: the exact mixed derivative order and exponential rate. -/
theorem largeVariance_exact (I : Set ℝ) (hI : IsCompact I) (hne : I.Nonempty)
    (hsub : I ⊆ Ioc (0 : ℝ) 1) :
    ∃ Vbar : ℝ, 1 ≤ Vbar ∧
      (∀ m ∈ I, ∀ V : ℝ≥0, ∀ x : ℝ,
        ColeHopfFoundation.ProbabilityTheory.coleHopf m V
            (fun y => Real.log (Real.cosh y)) x =
          m * (V : ℝ) / 2 + (1 / m - 1) * Real.log 2 +
            (1 / m) * Real.log (Real.cosh (m * x)) + largeVarianceError m V x) ∧
      ∀ ell : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ m ∈ I, ∀ V : ℝ, Vbar ≤ V →
        ∀ x : ℝ, ∀ i j k : ℕ, i + j + k ≤ ell →
          ‖iteratedDeriv i (fun y => iteratedDeriv j (fun m' => iteratedDeriv k
            (fun v => largeVarianceError m' v.toNNReal y) V) m) x‖ ≤
              C * V ^ ell * Real.exp (-((sInf I) ^ 2 / 2) * V) :=
  large_variance_sharp I hI hne hsub

/-- Revised Appendix C.2: the monotone tanh comparison, including zero variance. -/
theorem tanhComparison_exact {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) (V : ℝ≥0) (x : ℝ) :
    Real.tanh (m * |x|) ≤ |deriv
      (ColeHopfFoundation.ProbabilityTheory.coleHopf m V
        (fun w => Real.log (Real.cosh w))) x| :=
  revised_coleHopf_gradient_tanh_lower hm hm1 V x

/-- Revised Appendix C.2: the corresponding sech-square upper bound. -/
theorem sechComparison_exact {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) (V : ℝ≥0) (x : ℝ) :
    1 - (deriv (ColeHopfFoundation.ProbabilityTheory.coleHopf m V
      (fun w => Real.log (Real.cosh w))) x) ^ 2 ≤ Paper.sech (m * x) ^ 2 :=
  revised_coleHopf_gradient_sech_upper hm hm1 V x

/-- Revised Appendix A.6: the actual original-clock drift and log-cosh remainder.
The statement is proved for all probability measures, including atomic measures. -/
theorem sharpFirstVariation_exact (Ξ : RevisedCovariance) (μ ν : ParisiMeasure) :
    let I := fun sample : Paper.BrownianSample =>
      ∫ q in (0 : ℝ)..1, Ξ.second q * (Paper.parisiCDF ν q - Paper.parisiCDF μ q) *
        RevisedCovariance.gradient Ξ μ q (RevisedCovariance.optimalState Ξ μ sample q)
    let R := fun sample : Paper.BrownianSample =>
      Real.log (Real.cosh (RevisedCovariance.optimalState Ξ μ sample 1 + I sample)) -
        Real.log (Real.cosh (RevisedCovariance.optimalState Ξ μ sample 1)) -
        Real.tanh (RevisedCovariance.optimalState Ξ μ sample 1) * I sample
    Integrable R Paper.canonicalBrownianMeasure ∧
      (-((∫ q : Overlap, RevisedCovariance.firstVariation Ξ μ q ∂(ν : Measure Overlap)) -
        (∫ q : Overlap, RevisedCovariance.firstVariation Ξ μ q ∂(μ : Measure Overlap))) +
        (∫ sample, R sample ∂Paper.canonicalBrownianMeasure) ≤
          RevisedCovariance.parisiFunctional Ξ ν - RevisedCovariance.parisiFunctional Ξ μ) ∧
      0 ≤ ∫ sample, R sample ∂Paper.canonicalBrownianMeasure := by
  dsimp only
  exact ⟨RevisedCovariance.integrable_sharpFirstVariationRemainder Ξ μ ν,
    RevisedCovariance.sharp_first_variation Ξ μ ν⟩

end Verification.RevisedTargets
