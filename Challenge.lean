module
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
Theorem 1.1 of Aronow--Lopatto, in the finite-step variational formulation.
All finite depths are allowed as competitors. Gaussian variances are increments
of the effective covariance derivative. The additive normalization is `log 2`.
The order parameter is a probability measure with exactly `k+1` support points.
-/

public section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators Topology
namespace ArbitraryRSB

abbrev Overlap := Set.Icc (0 : ℝ) 1

/-- The effective zero-field mixed even-spin covariance. -/
@[expose] def covariance {k : ℕ} (p : Fin (k+1) → ℕ)
    (c : Fin (k+1) → ℝ) (q : ℝ) : ℝ := ∑ i, c i * q ^ p i

@[expose] def covarianceDerivative {k : ℕ} (p : Fin (k+1) → ℕ)
    (c : Fin (k+1) → ℝ) (q : ℝ) : ℝ :=
  ∑ i, c i * (p i : ℝ) * q ^ (p i - 1)

@[expose] def correctionPrimitive {k : ℕ} (p : Fin (k+1) → ℕ)
    (c : Fin (k+1) → ℝ) (q : ℝ) : ℝ :=
  q * covarianceDerivative p c q - covariance p c q

/-- Gaussian Cole--Hopf step, including the mass-zero expectation. -/
@[expose] def gaussianStep (m v : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if m = 0 then ∫ z, f (x+z) ∂gaussianReal 0 v.toNNReal
  else (1/m) * Real.log (∫ z, Real.exp (m*f (x+z)) ∂gaussianReal 0 v.toNNReal)

/-- A chronological finite list of mass levels and Gaussian variances. -/
@[expose] def gaussianRecursion : (n : ℕ) → (Fin n → ℝ × ℝ) → (ℝ → ℝ) → ℝ → ℝ
  | 0, _, f => f
  | n+1, d, f => gaussianStep (d 0).1 (d 0).2
      (gaussianRecursion n (fun i => d i.succ) f)

@[expose] def atomicLaw {n : ℕ} (q : Fin (n+1) → Overlap)
    (w : Fin (n+1) → ℝ) : Measure Overlap :=
  ∑ i, ENNReal.ofReal (w i) • Measure.dirac (q i)

@[expose] def atomicData {k n : ℕ} (p : Fin (k+1) → ℕ) (c : Fin (k+1) → ℝ)
    (q : Fin (n+1) → Overlap) (w : Fin (n+1) → ℝ) : Fin (n+1) → ℝ × ℝ :=
  let node : Fin (n+2) → ℝ := Fin.lastCases 1 (fun i => (q i : ℝ))
  fun i => (∑ j, if j ≤ i then w j else 0,
    covarianceDerivative p c (node i.succ) - covarianceDerivative p c (node i.castSucc))

/-- The functional of atoms starting at zero; weights are actual atom masses. -/
@[expose] def atomicFunctional {k n : ℕ} (p : Fin (k+1) → ℕ) (c : Fin (k+1) → ℝ)
    (q : Fin (n+1) → Overlap) (w : Fin (n+1) → ℝ) : ℝ :=
  Real.log 2 + gaussianRecursion (n+1) (atomicData p c q w)
    (fun x => Real.log (Real.cosh x)) 0 - (1/2 : ℝ) *
      ∑ i, w i * (correctionPrimitive p c 1 - correctionPrimitive p c (q i))

/-- Competitors include repeated nodes, zero masses, and atoms at either endpoint. -/
structure FiniteScheme (n : ℕ) where
  m : ℕ → ℝ
  q : ℕ → ℝ
  m_zero : m 0 = 0
  m_top : m (n+1) = 1
  m_mono : ∀ j, j ≤ n → m j ≤ m (j+1)
  q_zero : q 0 = 0
  q_top : q (n+2) = 1
  q_mono : ∀ j, j ≤ n+1 → q j ≤ q (j+1)

/-- Reverse evaluation of the finite Gaussian recursion, including the initial
mass-zero step when the first atom lies strictly above zero. -/
@[expose] def schemePotential {k n : ℕ} (p : Fin (k+1) → ℕ) (c : Fin (k+1) → ℝ)
    (s : FiniteScheme n) : ℕ → ℝ → ℝ
  | 0 => fun x => Real.log (Real.cosh x)
  | j+1 => gaussianStep (s.m (n+1-j))
      (covarianceDerivative p c (s.q (n+2-j)) - covarianceDerivative p c (s.q (n+1-j)))
      (schemePotential p c s j)

/-- The Parisi correction written as atom weights times covariance tails.
This equals one half of the integral of `q ξ''(q) μ([0,q])` on `[0,1]`. -/
@[expose] def schemeFunctional {k n : ℕ} (p : Fin (k+1) → ℕ) (c : Fin (k+1) → ℝ)
    (s : FiniteScheme n) : ℝ :=
  Real.log 2 + schemePotential p c s (n+2) 0 - (1/2 : ℝ) *
    ∑ i : Fin (n+1), (s.m (i+1)-s.m i) *
      (correctionPrimitive p c 1 - correctionPrimitive p c (s.q (i+1)))

/-- A nonempty open family with a globally optimizing exact finite-depth law.
The comparison ranges over all finite schemes, of every competing depth. -/
theorem arbitrary_finite_depth_open_set (k : ℕ) :
    ∃ p : Fin (k+1) → ℕ, StrictMono p ∧ p 0 = 4 ∧ (∀ i, 4 ≤ p i ∧ Even (p i)) ∧
      ∃ O : Set (Fin (k+1) → ℝ), IsOpen O ∧ O.Nonempty ∧ (∀ c ∈ O, ∀ i, 0 < c i) ∧
        ∀ c ∈ O, ∃ q : Fin (k+1) → Overlap, ∃ w : Fin (k+1) → ℝ,
          StrictMono (fun i => (q i : ℝ)) ∧ (q 0 : ℝ) = 0 ∧ (q (Fin.last k) : ℝ) < 1 ∧
          (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧ IsProbabilityMeasure (atomicLaw q w) ∧
          (atomicLaw q w).support = Set.range q ∧ (atomicLaw q w).support.ncard = k+1 ∧
          ∀ n : ℕ, ∀ s : FiniteScheme n, atomicFunctional p c q w ≤ schemeFunctional p c s := by
  sorry

/-- A finite polynomial; inactive coefficients have no mathematical effect. -/
structure FinitePolynomial where
  degrees : Finset ℕ
  coefficient : ℕ → ℝ

@[expose] def polynomialValue (Ξ : FinitePolynomial) (q : ℝ) : ℝ :=
  ∑ p ∈ Ξ.degrees, Ξ.coefficient p * q ^ p

@[expose] def polynomialDerivative (Ξ : FinitePolynomial) (q : ℝ) : ℝ :=
  ∑ p ∈ Ξ.degrees, Ξ.coefficient p * (p : ℝ) * q ^ (p-1)

@[expose] def polynomialSecondDerivative (Ξ : FinitePolynomial) (q : ℝ) : ℝ :=
  ∑ p ∈ Ξ.degrees, Ξ.coefficient p * (p : ℝ) * ((p-1 : ℕ) : ℝ) * q ^ (p-2)

@[expose] def polynomialCorrection (Ξ : FinitePolynomial) (q : ℝ) : ℝ :=
  q * polynomialDerivative Ξ q - polynomialValue Ξ q

/-- Admissibility permits a quadratic interaction and requires ξ''(0)<1. -/
@[expose] def IsAdmissible (Ξ : FinitePolynomial) : Prop :=
  Ξ.degrees.Nonempty ∧
    (∀ p ∈ Ξ.degrees, 0 < Ξ.coefficient p ∧ 2 ≤ p ∧ Even p) ∧
    polynomialSecondDerivative Ξ 0 < 1

@[expose] def addInteraction (Ξ : FinitePolynomial) (p : ℕ) (lam : ℝ) : FinitePolynomial :=
  ⟨insert p Ξ.degrees, fun j => if j=p then lam else Ξ.coefficient j⟩

@[expose] def scalePolynomial (Ξ : FinitePolynomial) (b : ℝ) : FinitePolynomial :=
  ⟨Ξ.degrees, fun p => b^2 * Ξ.coefficient p⟩

@[expose] def polynomialSchemePotential {n : ℕ} (Ξ : FinitePolynomial)
    (s : FiniteScheme n) : ℕ → ℝ → ℝ
  | 0 => fun x => Real.log (Real.cosh x)
  | j+1 => gaussianStep (s.m (n+1-j))
      (polynomialDerivative Ξ (s.q (n+2-j)) - polynomialDerivative Ξ (s.q (n+1-j)))
      (polynomialSchemePotential Ξ s j)

@[expose] def polynomialSchemeFunctional {n : ℕ} (Ξ : FinitePolynomial)
    (s : FiniteScheme n) : ℝ :=
  Real.log 2 + polynomialSchemePotential Ξ s (n+2) 0 - (1/2 : ℝ) *
    ∑ i : Fin (n+1), (s.m (i+1)-s.m i) *
      (polynomialCorrection Ξ 1 - polynomialCorrection Ξ (s.q (i+1)))

@[expose] def clippedOverlap (q : ℝ) : Overlap :=
  ⟨max 0 (min 1 q), le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- The probability law represented by a cumulative-mass scheme. -/
@[expose] def schemeLaw {n : ℕ} (s : FiniteScheme n) : Measure Overlap :=
  atomicLaw (fun i : Fin (n+1) => clippedOverlap (s.q (i+1))) (fun i => s.m (i+1)-s.m i)

/-- The intrinsic Gaussian-recursion value of a finite atomic probability
law. All representations have the same value; existence and identification
with the unrestricted Parisi functional are proved in Solution. -/
@[expose] def finiteFunctional (Ξ : FinitePolynomial) (μ : Measure Overlap) : ℝ :=
  sInf {v : ℝ | ∃ n : ℕ, ∃ s : FiniteScheme n,
    schemeLaw s = μ ∧ v = polynomialSchemeFunctional Ξ s}

/-- This compares against every finite probability law, at every depth.
Continuity and finite grid approximations identify it with global minimality. -/
@[expose] def FiniteLawMinimizes (Ξ : FinitePolynomial) (μ : Measure Overlap) : Prop :=
  ∀ n : ℕ, ∀ s : FiniteScheme n, finiteFunctional Ξ μ ≤ polynomialSchemeFunctional Ξ s

/-- The true scaled physical pressure. At nonzero temperature it is the
infimum over all finite Gaussian hierarchies; at zero it equals log 2. -/
@[expose] def temperaturePressure (Ξ : FinitePolynomial) (b : ℝ) : ℝ :=
  if b=0 then Real.log 2 else
    sInf {v : ℝ | ∃ n : ℕ, ∃ s : FiniteScheme n,
      v = polynomialSchemeFunctional (scalePolynomial Ξ b) s}

@[expose] def diracMixture (μ : Measure Overlap) (q : Overlap) (t : ℝ) : Measure Overlap :=
  ENNReal.ofReal (1-t) • μ + ENNReal.ofReal t • Measure.dirac q

/-- Right derivative in the direction of a Dirac probability law. -/
@[expose] def diracDirectionalDerivative (Ξ : FinitePolynomial) (μ : Measure Overlap)
    (q : ℝ) : ℝ :=
  derivWithin (fun t => finiteFunctional Ξ (diracMixture μ (clippedOverlap q) t)) (Ioi 0) 0

/-- The paper's first variation, anchored by f(0)=0. For an actual finite
law the identity is D₀−Dq=f(q), with no rescaling of the paper's normalization. -/
@[expose] def finiteFirstVariation (Ξ : FinitePolynomial) (μ : Measure Overlap) (q : ℝ) : ℝ :=
  diracDirectionalDerivative Ξ μ 0 - diracDirectionalDerivative Ξ μ q

@[expose] def AtomicParameters {r : ℕ} (q : Fin (r+1) → Overlap)
    (w : Fin (r+1) → ℝ) : Prop :=
  StrictMono (fun i => (q i : ℝ)) ∧ (q 0 : ℝ)=0 ∧ (q (Fin.last r) : ℝ)<1 ∧
    (∀ i, 0<w i) ∧ (∑ i, w i)=1

/-- The revised paper's seed hypotheses, without a Hessian assumption. -/
@[expose] def NondegenerateSeed (Ξ : FinitePolynomial) {r : ℕ}
    (q : Fin (r+1) → Overlap) (w : Fin (r+1) → ℝ) : Prop :=
  AtomicParameters q w ∧ FiniteLawMinimizes Ξ (atomicLaw q w) ∧
    (∀ u ∈ Icc (0 : ℝ) 1, finiteFirstVariation Ξ (atomicLaw q w) u ≤ 0 ∧
      (finiteFirstVariation Ξ (atomicLaw q w) u=0 ↔ ∃ i, u=(q i : ℝ))) ∧
    (∀ i : Fin r, deriv (deriv (finiteFirstVariation Ξ (atomicLaw q w))) (q i.succ) < 0)

/-- Exact r-RSB means that a globally minimizing probability law has
finite support consisting of exactly r+1 points. -/
@[expose] def ExactFiniteDepth (Ξ : FinitePolynomial) (r : ℕ) : Prop :=
  ∃ μ : Measure Overlap, IsProbabilityMeasure μ ∧ μ.support.Finite ∧
    μ.support.ncard = r+1 ∧ FiniteLawMinimizes Ξ μ

/-- Literal Theorem 1.2: a unique high-degree transition from exact r-RSB
to exact (r+1)-RSB, with positive physical entropy and its limiting critical
coefficient. Both phases concern the unrestricted probability-measure minimum. -/
theorem universal_gardner_transition (Ξ : FinitePolynomial) (hΞ : IsAdmissible Ξ)
    {r : ℕ} (q : Fin (r+1) → Overlap) (w : Fin (r+1) → ℝ)
    (hND : NondegenerateSeed Ξ q w) :
    let pressure := temperaturePressure Ξ
    let entropy := pressure 1 - deriv pressure 1
    0 < entropy ∧ ∃ eta : ℝ, eta ∈ Ioo (0 : ℝ) (2*entropy) ∧
      ∃ critical : ℕ → ℝ,
        Filter.Tendsto critical (Filter.atTop ⊓ Filter.principal {p : ℕ | Even p})
          (𝓝 (2*entropy)) ∧
        ∀ᶠ p : ℕ in Filter.atTop, ∀ _he : Even p,
          4 ≤ p ∧ p ∉ Ξ.degrees ∧ critical p ∈ Ioo (2*entropy-eta) (2*entropy+eta) ∧
          (∀ lam ∈ Icc (2*entropy-eta) (2*entropy+eta),
            (ExactFiniteDepth (addInteraction Ξ p lam) r ↔ lam ≤ critical p) ∧
            (ExactFiniteDepth (addInteraction Ξ p lam) (r+1) ↔ critical p < lam)) ∧
          (∀ c ∈ Ioo (2*entropy-eta) (2*entropy+eta),
            (∀ lam ∈ Icc (2*entropy-eta) (2*entropy+eta),
              (ExactFiniteDepth (addInteraction Ξ p lam) r ↔ lam ≤ c) ∧
              (ExactFiniteDepth (addInteraction Ξ p lam) (r+1) ↔ c < lam)) → c=critical p) := by
  sorry

end ArbitraryRSB
