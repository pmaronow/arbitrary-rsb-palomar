module
public import DepthPaper.MainTheorems
public import DepthPaper.AtomicPotentialRegularity
public import FourPapersCommon.MixedScheme
public import GeneralDepthPaper.RevisedTransition
public import Verification.PhysicalStochasticTargets
public import DepthPaper.RevisedFiniteSchemeSorting
public import FRSB.GridMeasureIdentification
public import FRSB.ParisiGridTopology
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
Theorems 1.1 and 1.2 of Aronow--Lopatto, with a concrete finite-step
variational interface. Every finite depth is allowed as a competitor;
continuity and finite-grid density recover the unrestricted probability-measure
minimum. Gaussian variances are increments of the effective covariance derivative,
and the additive normalization is `log 2`. The universal transition uses positive
even degrees at least two, ξ''(0)<1, and the paper's seed nondegeneracy condition.
The positive Hessian is derived in the proof development.
-/

public section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace ArbitraryRSB
set_option maxHeartbeats 1000000

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
private def FiniteScheme.toOriginal {n : ℕ} (s : FiniteScheme n) :
    SpinGlass.Targets.RSBScheme n where
  m := s.m
  q := s.q
  m_zero := s.m_zero
  m_top := s.m_top
  m_mono := s.m_mono
  q_zero := s.q_zero
  q_top := s.q_top
  q_mono := s.q_mono

private theorem indexedDerivative {k : ℕ} (p : Fin (k+1) → ℕ)
    (hp : ∀ i, 4 ≤ p i) (he : ∀ i, Even (p i)) (hi : Function.Injective p)
    (c : Fin (k+1) → ℝ) (hc : c ∈ DepthPaper.positiveCoefficientDomain k) (q : ℝ) :
    (DepthPaper.indexedCovariance p hp he c hc).first q = covarianceDerivative p c q := by
  unfold DepthPaper.AdmissibleCovariance.first DepthPaper.indexedCovariance covarianceDerivative
  simp only
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i _
    rw [Function.leftInverse_invFun hi i]
  · exact fun i _ j _ hij => hi hij

private theorem indexedCorrection {k : ℕ} (p : Fin (k+1) → ℕ)
    (hp : ∀ i, 4 ≤ p i) (he : ∀ i, Even (p i)) (hi : Function.Injective p)
    (c : Fin (k+1) → ℝ) (hc : c ∈ DepthPaper.positiveCoefficientDomain k) (q : ℝ) :
    DepthPaper.covarianceCorrectionPrimitive (DepthPaper.indexedCovariance p hp he c hc) q =
      correctionPrimitive p c q := by
  unfold DepthPaper.covarianceCorrectionPrimitive correctionPrimitive
  rw [indexedDerivative p hp he hi c hc q,
    DepthPaper.indexedCovariance_value p hp he hi c hc q]
  rfl

private theorem gaussianRecursion_eq (n : ℕ) (d : Fin n → ℝ × ℝ)
    (g : DepthPaper.TerminalSpace) (hv : ∀ i, 0 < (d i).2) (x : ℝ) :
    gaussianRecursion n d (DepthPaper.terminalValue g) x =
      DepthPaper.terminalValue (DepthPaper.coleHopfRecursion n (d,g)) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [DepthPaper.coleHopfRecursion, DepthPaper.terminalValue_coleHopfTerminal _ (hv 0)]
    change gaussianStep (d 0).1 (d 0).2
      (gaussianRecursion n (fun i => d i.succ) (DepthPaper.terminalValue g)) x = _
    have htail := funext (ih (fun i => d i.succ) (fun i => hv i.succ))
    rw [htail]
    rfl

private theorem candidateFunctional_eq {k n : ℕ} (p : Fin (k+1) → ℕ)
    (hp : ∀ i, 4 ≤ p i) (he : ∀ i, Even (p i)) (hi : Function.Injective p)
    (c : Fin (k+1) → ℝ) (hc : c ∈ DepthPaper.positiveCoefficientDomain k)
    (z : DepthPaper.AtomicPoint n) (hz : DepthPaper.IsAtomicPoint z) :
    atomicFunctional p c (DepthPaper.atomicOverlap z hz) (DepthPaper.atomicWeight z) =
      DepthPaper.parisiFunctional (DepthPaper.indexedCovariance p hp he c hc)
        (DepthPaper.atomicMeasure z hz) := by
  let X := DepthPaper.indexedCovariance p hp he c hc
  have hdata : atomicData p c (DepthPaper.atomicOverlap z hz) (DepthPaper.atomicWeight z) =
      DepthPaper.atomicRecursionData X z := by
    funext i
    simp only [atomicData, DepthPaper.atomicRecursionData, DepthPaper.atomicLevel]
    rw [indexedDerivative p hp he hi c hc, indexedDerivative p hp he hi c hc]
    rfl
  rw [DepthPaper.atomicFunctional_eq_recursion X z hz]
  unfold atomicFunctional DepthPaper.atomicFunctionalRecursion DepthPaper.atomicPotentialRecursion
  rw [hdata]
  have hg : (fun x => Real.log (Real.cosh x)) = DepthPaper.terminalValue DepthPaper.logCoshTerminal :=
    funext (fun x => (DepthPaper.terminalValue_logCoshTerminal x).symm)
  rw [hg, gaussianRecursion_eq _ _ _ (DepthPaper.atomicRecursionData_variance_pos X z hz)]
  congr 2
  unfold DepthPaper.atomicCorrection
  apply Finset.sum_congr rfl
  intro i _
  rw [indexedCorrection p hp he hi c hc, indexedCorrection p hp he hi c hc]
  rfl

private theorem schemePotential_eq {k n : ℕ} (p : Fin (k+1) → ℕ)
    (hp : ∀ i, 4 ≤ p i) (he : ∀ i, Even (p i)) (hi : Function.Injective p)
    (c : Fin (k+1) → ℝ) (hc : c ∈ DepthPaper.positiveCoefficientDomain k)
    (s : FiniteScheme n) (j : ℕ) (hj : j ≤ n+2) :
    schemePotential p c s j = SpinGlass.Targets.parisiF
      (FourPapersCommon.mixedClockScheme (DepthPaper.indexedCovariance p hp he c hc).toEvenMixture
        s.toOriginal) (FourPapersCommon.mixedBeta (DepthPaper.indexedCovariance p hp he c hc).toEvenMixture) j := by
  let X := DepthPaper.indexedCovariance p hp he c hc
  let S := FourPapersCommon.mixedClockScheme X.toEvenMixture s.toOriginal
  let β := FourPapersCommon.mixedBeta X.toEvenMixture
  induction j with
  | zero => rfl
  | succ j ih =>
    have hj' : j ≤ n+2 := by omega
    rw [schemePotential, ih hj', SpinGlass.Targets.parisiF]
    funext x
    have hjn : n+2-j = (n+1-j)+1 := by omega
    rw [hjn, FourPapersCommon.mixedClockScheme_variance]
    simp only [FourPapersCommon.mixedClockScheme_m, FiniteScheme.toOriginal,
      DepthPaper.AdmissibleCovariance.toEvenMixture_first]
    rw [indexedDerivative p hp he hi c hc, indexedDerivative p hp he hi c hc]
    have hv : 0 ≤ X.first (s.q ((n+1-j)+1)) - X.first (s.q (n+1-j)) := by
      apply sub_nonneg.mpr
      apply X.first_strictMonoOn.monotoneOn
      · exact s.toOriginal.q_nonneg (by omega)
      · exact s.toOriginal.q_nonneg (by omega)
      · exact s.q_mono _ (by omega)
    have H := Paper.parisiStep_eq_coleHopf (s.m (n+1-j))
      (X.first (s.q ((n+1-j)+1)) - X.first (s.q (n+1-j))).toNNReal
      (SpinGlass.Targets.parisiF_measurable S β j) x
    rw [Real.coe_toNNReal _ hv, indexedDerivative p hp he hi c hc,
      indexedDerivative p hp he hi c hc] at H
    exact H.symm

private theorem competitorFunctional_eq {k n : ℕ} (p : Fin (k+1) → ℕ)
    (hp : ∀ i, 4 ≤ p i) (he : ∀ i, Even (p i)) (hi : Function.Injective p)
    (c : Fin (k+1) → ℝ) (hc : c ∈ DepthPaper.positiveCoefficientDomain k)
    (s : FiniteScheme n) : schemeFunctional p c s =
      DepthPaper.parisiFunctional (DepthPaper.indexedCovariance p hp he c hc)
        (Paper.parisiSchemeMeasure s.toOriginal) := by
  let X := DepthPaper.indexedCovariance p hp he c hc
  unfold DepthPaper.parisiFunctional
  rw [FourPapersCommon.mixedFunctional, FourPapersCommon.mixedPotential_scheme_initial,
    FourPapersCommon.mixedScheme_correction_integral]
  unfold schemeFunctional
  rw [schemePotential_eq p hp he hi c hc s _ le_rfl]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  simp only [FourPapersCommon.AdmissibleEvenMixture.correction,
    DepthPaper.AdmissibleCovariance.toEvenMixture_first,
    DepthPaper.AdmissibleCovariance.toEvenMixture_value, FiniteScheme.toOriginal]
  rw [indexedDerivative p hp he hi c hc, indexedDerivative p hp he hi c hc,
    DepthPaper.indexedCovariance_value p hp he hi c hc,
    DepthPaper.indexedCovariance_value p hp he hi c hc]
  rfl

/-- Continuity and explicit finite grid approximations identify the unrestricted
probability-measure minimum with comparison against every finite scheme. -/
theorem full_measure_minimizer_iff_finite_schemes (X : DepthPaper.AdmissibleCovariance)
    (μ : Paper.ParisiMeasure) :
    DepthPaper.IsParisiMinimizer X μ ↔
      ∀ n : ℕ, ∀ s : SpinGlass.Targets.RSBScheme n,
        DepthPaper.parisiFunctional X μ ≤ DepthPaper.parisiFunctional X (Paper.parisiSchemeMeasure s) := by
  constructor
  · intro h n s
    exact h (Paper.parisiSchemeMeasure s)
  · intro h ν
    have hlim := ((FourPapersCommon.continuous_mixedFunctional X.toEvenMixture 0).tendsto ν).comp
      (FRSB.tendsto_parisiGridMeasure ν)
    apply ge_of_tendsto hlim
    apply Filter.Eventually.of_forall
    intro n
    change DepthPaper.parisiFunctional X μ ≤ DepthPaper.parisiFunctional X (Paper.parisiGridMeasure ν n)
    rw [← FRSB.parisiSchemeMeasure_grid_eq ν n]
    exact h (n+1) (Paper.parisiGridRSBScheme ν n)

theorem arbitrary_finite_depth_open_set (k : ℕ) :
    ∃ p : Fin (k+1) → ℕ, StrictMono p ∧ p 0 = 4 ∧ (∀ i, 4 ≤ p i ∧ Even (p i)) ∧
      ∃ O : Set (Fin (k+1) → ℝ), IsOpen O ∧ O.Nonempty ∧ (∀ c ∈ O, ∀ i, 0 < c i) ∧
        ∀ c ∈ O, ∃ q : Fin (k+1) → Overlap, ∃ w : Fin (k+1) → ℝ,
          StrictMono (fun i => (q i : ℝ)) ∧ (q 0 : ℝ) = 0 ∧ (q (Fin.last k) : ℝ) < 1 ∧
          (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧ IsProbabilityMeasure (atomicLaw q w) ∧
          (atomicLaw q w).support = Set.range q ∧ (atomicLaw q w).support.ncard = k+1 ∧
          ∀ n : ℕ, ∀ s : FiniteScheme n, atomicFunctional p c q w ≤ schemeFunctional p c s := by
  obtain ⟨p,hp,he,hmono,hfirst,O,hO,hne,hpos,hall⟩ := DepthPaper.arbitrary_finite_depth_open_set k
  refine ⟨p,hmono,hfirst,fun i => ⟨hp i,he i⟩,O,hO,hne,fun c hc => hpos hc,?_⟩
  intro c hc
  obtain ⟨hcoeff,hdepth,z,hz,hnd⟩ := hall c hc
  let X := DepthPaper.indexedCovariance p hp he c hcoeff
  refine ⟨DepthPaper.atomicOverlap z hz,DepthPaper.atomicWeight z,hz.1,rfl,hz.2.1,
    hz.2.2,DepthPaper.sum_atomicWeight z,?_,?_,?_,?_⟩
  · change IsProbabilityMeasure (DepthPaper.atomicMeasure z hz : Measure Overlap)
    infer_instance
  · exact DepthPaper.support_atomicMeasure z hz
  · exact (DepthPaper.atomicMeasure_isFiniteRSB z hz).2
  · intro n s
    rw [candidateFunctional_eq p hp he hmono.injective c hcoeff z hz,
      competitorFunctional_eq p hp he hmono.injective c hcoeff s]
    exact hnd.1 (Paper.parisiSchemeMeasure s.toOriginal)

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

private def polynomialModel (Ξ : FinitePolynomial)
    (hne : Ξ.degrees.Nonempty)
    (hp : ∀ p ∈ Ξ.degrees, 0<Ξ.coefficient p ∧ 2≤p ∧ Even p) :
    GeneralDepthPaper.AdmissibleCovariance where
  degrees := Ξ.degrees
  nonempty := hne
  coefficient := Ξ.coefficient
  coefficient_pos p h := (hp p h).1
  degree_ge_two p h := (hp p h).2.1
  degree_even p h := (hp p h).2.2

private def FiniteScheme.fromOriginal {n : ℕ} (s : SpinGlass.Targets.RSBScheme n) :
    FiniteScheme n where
  m := s.m
  q := s.q
  m_zero := s.m_zero
  m_top := s.m_top
  m_mono := s.m_mono
  q_zero := s.q_zero
  q_top := s.q_top
  q_mono := s.q_mono

@[simp] private theorem FiniteScheme.toOriginal_fromOriginal {n : ℕ}
    (s : SpinGlass.Targets.RSBScheme n) : (FiniteScheme.fromOriginal s).toOriginal=s := by
  cases s
  rfl

private theorem clippedOverlap_val {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    (clippedOverlap q : ℝ)=q := by
  simp only [clippedOverlap,min_eq_right hq.2,max_eq_right hq.1]

private theorem schemeLaw_eq {n : ℕ} (s : FiniteScheme n) :
    schemeLaw s=(Paper.parisiSchemeMeasure s.toOriginal : Measure Overlap) := by
  change (∑i : Fin (n+1),ENNReal.ofReal (s.m (i+1)-s.m i) •
    Measure.dirac (clippedOverlap (s.q (i+1))))=
      ∑i : Fin (n+1),ENNReal.ofReal (s.m (i+1)-s.m i) •
        Measure.dirac (Paper.parisiSchemeAtom s.toOriginal i)
  apply Finset.sum_congr rfl
  intro i _
  have hq : clippedOverlap (s.q (i+1))=Paper.parisiSchemeAtom s.toOriginal i := by
    apply Subtype.ext
    exact clippedOverlap_val ⟨s.toOriginal.q_nonneg (by omega),s.toOriginal.q_le_one (by omega)⟩
  rw [hq]

private theorem polynomialSchemePotential_eq {n : ℕ} (Ξ : FinitePolynomial)
    (hne : Ξ.degrees.Nonempty)
    (hp : ∀ p ∈ Ξ.degrees, 0<Ξ.coefficient p ∧ 2≤p ∧ Even p)
    (s : FiniteScheme n) (j : ℕ) (hj : j≤n+2) :
    polynomialSchemePotential Ξ s j = SpinGlass.Targets.parisiF
      (FourPapersCommon.mixedClockScheme (polynomialModel Ξ hne hp).toEvenMixture s.toOriginal)
      (FourPapersCommon.mixedBeta (polynomialModel Ξ hne hp).toEvenMixture) j := by
  let X := polynomialModel Ξ hne hp
  let S := FourPapersCommon.mixedClockScheme X.toEvenMixture s.toOriginal
  let β := FourPapersCommon.mixedBeta X.toEvenMixture
  induction j with
  | zero => rfl
  | succ j ih =>
    have hj' : j≤n+2 := by omega
    rw [polynomialSchemePotential,ih hj',SpinGlass.Targets.parisiF]
    funext x
    have hjn : n+2-j=(n+1-j)+1 := by omega
    rw [hjn,FourPapersCommon.mixedClockScheme_variance]
    simp only [FourPapersCommon.mixedClockScheme_m,FiniteScheme.toOriginal,
      GeneralDepthPaper.AdmissibleCovariance.toEvenMixture_first]
    have hv : 0≤X.first (s.q ((n+1-j)+1))-X.first (s.q (n+1-j)) := by
      apply sub_nonneg.mpr
      apply X.first_strictMonoOn.monotoneOn
      · exact s.toOriginal.q_nonneg (by omega)
      · exact s.toOriginal.q_nonneg (by omega)
      · exact s.q_mono _ (by omega)
    have H := Paper.parisiStep_eq_coleHopf (s.m (n+1-j))
      (X.first (s.q ((n+1-j)+1))-X.first (s.q (n+1-j))).toNNReal
      (SpinGlass.Targets.parisiF_measurable S β j) x
    rw [Real.coe_toNNReal _ hv] at H
    exact H.symm

private theorem polynomialSchemeFunctional_eq {n : ℕ} (Ξ : FinitePolynomial)
    (hne : Ξ.degrees.Nonempty)
    (hp : ∀ p ∈ Ξ.degrees, 0<Ξ.coefficient p ∧ 2≤p ∧ Even p)
    (s : FiniteScheme n) :
    polynomialSchemeFunctional Ξ s=GeneralDepthPaper.parisiFunctional
      (polynomialModel Ξ hne hp) (Paper.parisiSchemeMeasure s.toOriginal) := by
  let X := polynomialModel Ξ hne hp
  unfold GeneralDepthPaper.parisiFunctional
  rw [FourPapersCommon.mixedFunctional,FourPapersCommon.mixedPotential_scheme_initial,
    FourPapersCommon.mixedScheme_correction_integral]
  unfold polynomialSchemeFunctional
  rw [polynomialSchemePotential_eq Ξ hne hp s _ le_rfl]
  simp only [FourPapersCommon.AdmissibleEvenMixture.correction,
    GeneralDepthPaper.AdmissibleCovariance.toEvenMixture_first,
    GeneralDepthPaper.AdmissibleCovariance.toEvenMixture_value,FiniteScheme.toOriginal]
  rfl

private theorem finiteFunctional_eq (Ξ : FinitePolynomial)
    (hne : Ξ.degrees.Nonempty)
    (hp : ∀ p ∈ Ξ.degrees, 0<Ξ.coefficient p ∧ 2≤p ∧ Even p)
    (μ : Paper.ParisiMeasure) (hfin : (μ : Measure Overlap).support.Finite) :
    finiteFunctional Ξ (μ : Measure Overlap)=
      GeneralDepthPaper.parisiFunctional (polynomialModel Ξ hne hp) μ := by
  have hset : {v : ℝ|∃ n : ℕ,∃ s : FiniteScheme n,
      schemeLaw s=(μ : Measure Overlap) ∧ v=polynomialSchemeFunctional Ξ s}=
      {GeneralDepthPaper.parisiFunctional (polynomialModel Ξ hne hp) μ} := by
    ext v
    constructor
    · rintro ⟨n,s,hμ,rfl⟩
      rw [schemeLaw_eq] at hμ
      have hμ' : Paper.parisiSchemeMeasure s.toOriginal=μ := Subtype.ext hμ
      simp only [Set.mem_singleton_iff,polynomialSchemeFunctional_eq Ξ hne hp s,hμ']
    · intro hv
      obtain ⟨n,s,hs⟩ := DepthPaper.RevisedFiniteScheme.finite_support_scheme_representation μ hfin
      refine ⟨n,FiniteScheme.fromOriginal s,?_,?_⟩
      · rw [schemeLaw_eq]
        exact congrArg (fun ν : Paper.ParisiMeasure=>(ν : Measure Overlap)) hs
      · simpa only [Set.mem_singleton_iff,polynomialSchemeFunctional_eq Ξ hne hp,FiniteScheme.toOriginal_fromOriginal,hs] using hv
  rw [finiteFunctional,hset,csInf_singleton]

private theorem global_minimizer_iff_finite_law (Ξ : FinitePolynomial)
    (hne : Ξ.degrees.Nonempty)
    (hp : ∀ p ∈ Ξ.degrees, 0<Ξ.coefficient p ∧ 2≤p ∧ Even p)
    (μ : Paper.ParisiMeasure) (hfin : (μ : Measure Overlap).support.Finite) :
    FiniteLawMinimizes Ξ (μ : Measure Overlap) ↔
      GeneralDepthPaper.IsParisiMinimizer (polynomialModel Ξ hne hp) μ := by
  unfold FiniteLawMinimizes
  rw [finiteFunctional_eq Ξ hne hp μ hfin]
  constructor
  · intro h ν
    have hlim := ((FourPapersCommon.continuous_mixedFunctional
      (polynomialModel Ξ hne hp).toEvenMixture 0).tendsto ν).comp
      (FRSB.tendsto_parisiGridMeasure ν)
    apply ge_of_tendsto hlim
    apply Filter.Eventually.of_forall
    intro n
    change GeneralDepthPaper.parisiFunctional (polynomialModel Ξ hne hp) μ≤
      GeneralDepthPaper.parisiFunctional (polynomialModel Ξ hne hp) (Paper.parisiGridMeasure ν n)
    rw [←FRSB.parisiSchemeMeasure_grid_eq ν n]
    simpa only [polynomialSchemeFunctional_eq Ξ hne hp,FiniteScheme.toOriginal_fromOriginal] using
      h (n+1) (FiniteScheme.fromOriginal (Paper.parisiGridRSBScheme ν n))
  · intro h n s
    rw [polynomialSchemeFunctional_eq Ξ hne hp]
    exact h _

private theorem diracDirectionalDerivative_eq (Ξ : FinitePolynomial)
    (hne : Ξ.degrees.Nonempty)
    (hp : ∀ p ∈ Ξ.degrees, 0<Ξ.coefficient p ∧ 2≤p ∧ Even p)
    (μ : Paper.ParisiMeasure) (hfin : (μ : Measure Overlap).support.Finite) (q : ℝ) :
    diracDirectionalDerivative Ξ (μ : Measure Overlap) q=
      (∫u : Overlap,GeneralDepthPaper.firstVariation (polynomialModel Ξ hne hp) μ u
        ∂(μ : Measure Overlap))-
      GeneralDepthPaper.firstVariation (polynomialModel Ξ hne hp) μ (clippedOverlap q) := by
  let X := polynomialModel Ξ hne hp
  let ν := Paper.diracOverlap (clippedOverlap q) (clippedOverlap q).property
  have hν : (ν : Measure Overlap).support.Finite := by
    rw [Paper.support_diracOverlap]
    exact finite_singleton _
  have hd := GeneralDepthPaper.hasDerivWithinAt_parisiFunctional_mix X μ ν
  have hdirac : (∫u : Overlap,GeneralDepthPaper.firstVariation X μ u
      ∂(ν : Measure Overlap))=GeneralDepthPaper.firstVariation X μ (clippedOverlap q) := by
    exact integral_dirac _ _
  rw [hdirac] at hd
  have hnew : HasDerivWithinAt
      (fun t=>finiteFunctional Ξ (diracMixture (μ : Measure Overlap) (clippedOverlap q) t))
      (-(GeneralDepthPaper.firstVariation X μ (clippedOverlap q)-
        ∫u : Overlap,GeneralDepthPaper.firstVariation X μ u ∂(μ : Measure Overlap)))
      (Ioi (0:ℝ)) 0 := by
    apply hd.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono
          (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)) (a:=0))] with t ht ht1
      have hmix : diracMixture (μ : Measure Overlap) (clippedOverlap q) t=
          (Paper.parisiMix μ ν t : Measure Overlap) := by
        rw [Paper.parisiMix_measure μ ν t ⟨ht.le,ht1.le⟩]
        rfl
      rw [hmix,finiteFunctional_eq Ξ hne hp _
        (DepthPaper.RevisedFiniteScheme.finite_support_parisiMix μ ν hfin hν t)]
    · simp only [diracMixture,sub_zero,ENNReal.ofReal_one,one_smul,
        ENNReal.ofReal_zero,zero_smul,add_zero,Paper.parisiMix_zero]
      exact finiteFunctional_eq Ξ hne hp μ hfin
  unfold diracDirectionalDerivative
  rw [hnew.derivWithin (uniqueDiffWithinAt_Ioi 0)]
  dsimp only [X]
  ring

private theorem finiteFirstVariation_eq (Ξ : FinitePolynomial)
    (hne : Ξ.degrees.Nonempty)
    (hp : ∀ p ∈ Ξ.degrees, 0<Ξ.coefficient p ∧ 2≤p ∧ Even p)
    (μ : Paper.ParisiMeasure) (hfin : (μ : Measure Overlap).support.Finite)
    {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    finiteFirstVariation Ξ (μ : Measure Overlap) q=
      GeneralDepthPaper.firstVariation (polynomialModel Ξ hne hp) μ q := by
  rw [finiteFirstVariation,diracDirectionalDerivative_eq Ξ hne hp μ hfin,
    diracDirectionalDerivative_eq Ξ hne hp μ hfin,
    clippedOverlap_val (by norm_num : (0:ℝ)∈Icc (0:ℝ) 1),clippedOverlap_val hq,
    GeneralDepthPaper.firstVariation_zero]
  ring

private def parametersPoint {r : ℕ} (q : Fin (r+1)→Overlap) (w : Fin (r+1)→ℝ) :
    GeneralDepthPaper.AtomicPoint r := (fun i=>(q i.succ : ℝ),fun i=>w i.castSucc)

private theorem parametersPoint_locations {r : ℕ} (q : Fin (r+1)→Overlap)
    (w : Fin (r+1)→ℝ) (hq : (q 0 : ℝ)=0) :
    GeneralDepthPaper.atomicLocation (parametersPoint q w)=(fun i=>(q i : ℝ)) := by
  funext i
  refine Fin.cases ?_ (fun j=>rfl) i
  exact hq.symm

private theorem parametersPoint_weights {r : ℕ} (q : Fin (r+1)→Overlap)
    (w : Fin (r+1)→ℝ) (hw : (∑i,w i)=1) :
    GeneralDepthPaper.atomicWeight (parametersPoint q w)=w := by
  funext i
  refine Fin.lastCases ?_ (fun j=>by rw [GeneralDepthPaper.atomicWeight_castSucc];rfl) i
  rw [GeneralDepthPaper.atomicWeight_last]
  change 1-(∑j : Fin r,w j.castSucc)=w (Fin.last r)
  rw [Fin.sum_univ_castSucc] at hw
  linarith

private theorem parametersPoint_valid {r : ℕ} (q : Fin (r+1)→Overlap)
    (w : Fin (r+1)→ℝ) (h : AtomicParameters q w) :
    GeneralDepthPaper.IsAtomicPoint (parametersPoint q w) := by
  rw [GeneralDepthPaper.IsAtomicPoint,parametersPoint_locations q w h.2.1,
    parametersPoint_weights q w h.2.2.2.2]
  exact ⟨h.1,h.2.2.1,h.2.2.2.1⟩

private theorem parametersPoint_measure {r : ℕ} (q : Fin (r+1)→Overlap)
    (w : Fin (r+1)→ℝ) (h : AtomicParameters q w) :
    (GeneralDepthPaper.atomicMeasure (parametersPoint q w) (parametersPoint_valid q w h) :
      Measure Overlap)=atomicLaw q w := by
  have hq : GeneralDepthPaper.atomicOverlap (parametersPoint q w)
      (parametersPoint_valid q w h)=q := by
    funext i
    apply Subtype.ext
    exact congrFun (parametersPoint_locations q w h.2.1) i
  change (∑i : Fin (r+1),ENNReal.ofReal
    (GeneralDepthPaper.atomicWeight (parametersPoint q w) i) • Measure.dirac
      (GeneralDepthPaper.atomicOverlap (parametersPoint q w) (parametersPoint_valid q w h) i))=_
  rw [parametersPoint_weights q w h.2.2.2.2,hq]
  rfl

private theorem exactFiniteDepth_iff (Ξ : FinitePolynomial)
    (hne : Ξ.degrees.Nonempty)
    (hp : ∀ p ∈ Ξ.degrees, 0<Ξ.coefficient p ∧ 2≤p ∧ Even p) (r : ℕ) :
    ExactFiniteDepth Ξ r ↔ GeneralDepthPaper.IsFiniteRSB r
      (GeneralDepthPaper.parisiMinimizer (polynomialModel Ξ hne hp)) := by
  constructor
  · rintro ⟨μ,hprob,hfin,hcard,hmin⟩
    let ν : Paper.ParisiMeasure := ⟨μ,hprob⟩
    have hactual := (global_minimizer_iff_finite_law Ξ hne hp ν hfin).mp hmin
    have heq := GeneralDepthPaper.parisiMinimizer_unique (polynomialModel Ξ hne hp) ν hactual
    rw [←heq]
    exact ⟨hfin,hcard⟩
  · intro hdepth
    refine ⟨(GeneralDepthPaper.parisiMinimizer (polynomialModel Ξ hne hp) : Measure Overlap),
      inferInstance,hdepth.1,hdepth.2,?_⟩
    exact (global_minimizer_iff_finite_law Ξ hne hp _ hdepth.1).mpr
      (GeneralDepthPaper.isParisiMinimizer_selected _)

private theorem seed_nondegenerate (Ξ : FinitePolynomial) (hΞ : IsAdmissible Ξ)
    {r : ℕ} (q : Fin (r+1)→Overlap) (w : Fin (r+1)→ℝ)
    (hND : NondegenerateSeed Ξ q w) :
    GeneralDepthPaper.PaperNondegenerate (polynomialModel Ξ hΞ.1 hΞ.2.1)
      (parametersPoint q w) (parametersPoint_valid q w hND.1) := by
  dsimp only [IsAdmissible] at hΞ
  let μ := GeneralDepthPaper.atomicMeasure (parametersPoint q w)
    (parametersPoint_valid q w hND.1)
  have hμ : (μ : Measure Overlap)=atomicLaw q w := parametersPoint_measure q w hND.1
  have hfin : (μ : Measure Overlap).support.Finite := by
    rw [GeneralDepthPaper.support_atomicMeasure]
    exact finite_range _
  have hmin : GeneralDepthPaper.IsParisiMinimizer (polynomialModel Ξ hΞ.1 hΞ.2.1) μ := by
    apply (global_minimizer_iff_finite_law Ξ hΞ.1 hΞ.2.1 μ hfin).mp
    rw [hμ]
    exact hND.2.1
  have hf {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
      finiteFirstVariation Ξ (atomicLaw q w) u=
        GeneralDepthPaper.firstVariation (polynomialModel Ξ hΞ.1 hΞ.2.1) μ u := by
    rw [←hμ]
    exact finiteFirstVariation_eq Ξ hΞ.1 hΞ.2.1 μ hfin hu
  refine ⟨hmin,?_,?_⟩
  · intro u hu
    rw [←hf hu]
    simpa only [parametersPoint_locations q w hND.1.2.1] using hND.2.2.1 u hu
  · intro i
    have hi : (q i.succ : ℝ)∈Ioo (0:ℝ) 1 :=
      ⟨by have H := hND.1.1 (Fin.succ_pos i);change (q 0 : ℝ)<(q i.succ : ℝ) at H
          rw [hND.1.2.1] at H;exact H,
        (hND.1.1.monotone (Fin.le_last i.succ)).trans_lt hND.1.2.2.1⟩
    have he : finiteFirstVariation Ξ (atomicLaw q w)=ᶠ[𝓝 (q i.succ : ℝ)]
        GeneralDepthPaper.firstVariation (polynomialModel Ξ hΞ.1 hΞ.2.1) μ := by
      filter_upwards [isOpen_Ioo.mem_nhds hi] with u hu
      exact hf (Ioo_subset_Icc_self hu)
    change GeneralDepthPaper.closedJet 1 2
      (GeneralDepthPaper.firstVariation (polynomialModel Ξ hΞ.1 hΞ.2.1) μ) (q i.succ)<0
    rw [←GeneralDepthPaper.revised_closedJet,
      DepthPaper.RevisedCovariance.closedJet_two_eq_deriv_of_mem_Ioo _ hi]
    rw [←he.deriv.deriv_eq]
    exact hND.2.2.2 i

private theorem polynomialPressure_eq (Ξ : FinitePolynomial)
    (hne : Ξ.degrees.Nonempty)
    (hp : ∀ p ∈ Ξ.degrees, 0<Ξ.coefficient p ∧ 2≤p ∧ Even p) :
    sInf {v : ℝ | ∃ n : ℕ, ∃ s : FiniteScheme n,
      v=polynomialSchemeFunctional Ξ s}=
      GeneralDepthPaper.parisiPressure (polynomialModel Ξ hne hp) := by
  let X := polynomialModel Ξ hne hp
  let μ := GeneralDepthPaper.parisiMinimizer X
  let values := {v : ℝ | ∃ n : ℕ, ∃ s : FiniteScheme n,
    v=polynomialSchemeFunctional Ξ s}
  have hnonempty : values.Nonempty :=
    ⟨polynomialSchemeFunctional Ξ (FiniteScheme.fromOriginal (Paper.parisiGridRSBScheme μ 0)),
      1,FiniteScheme.fromOriginal (Paper.parisiGridRSBScheme μ 0),rfl⟩
  have hlower : ∀ v∈values,GeneralDepthPaper.parisiPressure X≤v := by
    rintro v ⟨n,s,rfl⟩
    rw [polynomialSchemeFunctional_eq Ξ hne hp,←GeneralDepthPaper.parisiMinimizer_value]
    exact GeneralDepthPaper.isParisiMinimizer_selected X _
  have hbounded : BddBelow values := ⟨GeneralDepthPaper.parisiPressure X,hlower⟩
  change sInf values=GeneralDepthPaper.parisiPressure X
  apply le_antisymm
  · rw [←GeneralDepthPaper.parisiMinimizer_value]
    have hlim := ((FourPapersCommon.continuous_mixedFunctional X.toEvenMixture 0).tendsto μ).comp
      (FRSB.tendsto_parisiGridMeasure μ)
    apply ge_of_tendsto hlim
    apply Filter.Eventually.of_forall
    intro n
    change sInf values≤GeneralDepthPaper.parisiFunctional X (Paper.parisiGridMeasure μ n)
    apply csInf_le hbounded
    refine ⟨n+1,FiniteScheme.fromOriginal (Paper.parisiGridRSBScheme μ n),?_⟩
    rw [polynomialSchemeFunctional_eq Ξ hne hp,FiniteScheme.toOriginal_fromOriginal,
      FRSB.parisiSchemeMeasure_grid_eq]
  · exact le_csInf hnonempty hlower

private theorem temperaturePressure_eq (Ξ : FinitePolynomial)
    (hne : Ξ.degrees.Nonempty)
    (hp : ∀ p ∈ Ξ.degrees, 0<Ξ.coefficient p ∧ 2≤p ∧ Even p) :
    temperaturePressure Ξ=
      GeneralDepthPaper.scaledThermodynamicPressure (polynomialModel Ξ hne hp).toEvenMixture := by
  funext b
  by_cases hb : b=0
  · simp [temperaturePressure,hb,GeneralDepthPaper.scaledThermodynamicPressure]
  · have hpos : ∀ p∈(scalePolynomial Ξ b).degrees,
        0<(scalePolynomial Ξ b).coefficient p ∧ 2≤p ∧ Even p := by
      intro p hmem
      exact ⟨mul_pos (sq_pos_of_ne_zero hb) (hp p hmem).1,(hp p hmem).2⟩
    have hmodel : polynomialModel (scalePolynomial Ξ b) hne hpos=
        (polynomialModel Ξ hne hp).temperatureScale b hb := rfl
    rw [temperaturePressure,ite_eq_right hb,polynomialPressure_eq (scalePolynomial Ξ b) hne hpos,hmodel,
      GeneralDepthPaper.scaledThermodynamicPressure_eq_temperature_parisiPressure _ b hb,
      GeneralDepthPaper.temperatureCovarianceFamily_covariance]

private theorem addInteraction_positive (Ξ : FinitePolynomial)
    (hp : ∀ p ∈ Ξ.degrees, 0<Ξ.coefficient p ∧ 2≤p ∧ Even p)
    (p : ℕ) (hdegree : 4≤p) (he : Even p) (hn : p∉Ξ.degrees)
    (lam : ℝ) (hpos : 0<lam) :
    ∀ j∈(addInteraction Ξ p lam).degrees,
      0<(addInteraction Ξ p lam).coefficient j ∧ 2≤j ∧ Even j := by
  intro j hj
  rcases Finset.mem_insert.mp hj with rfl|hj
  · simp only [addInteraction,ite_true]
    exact ⟨hpos,by omega,he⟩
  · have hne : j≠p := fun h=>hn (h ▸ hj)
    simpa only [addInteraction,ite_eq_right hne] using hp j hj

private theorem addInteraction_model (Ξ : FinitePolynomial)
    (hne : Ξ.degrees.Nonempty)
    (hp : ∀ p ∈ Ξ.degrees, 0<Ξ.coefficient p ∧ 2≤p ∧ Even p)
    (p : ℕ) (hdegree : 4≤p) (he : Even p) (hn : p∉Ξ.degrees)
    (lam : ℝ) (hpos : 0<lam) :
    polynomialModel (addInteraction Ξ p lam) (Finset.insert_nonempty _ _)
      (addInteraction_positive Ξ hp p hdegree he hn lam hpos)=
      (polynomialModel Ξ hne hp).addHighDegree p hdegree he hn lam hpos := rfl

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
  dsimp only
  dsimp only [IsAdmissible] at hΞ
  have hsub : (polynomialModel Ξ hΞ.1 hΞ.2.1).IsSubcritical := hΞ.2.2
  have H := GeneralDepthPaper.gardner_transition_theorem_1_2
    (polynomialModel Ξ hΞ.1 hΞ.2.1) (parametersPoint q w)
    (parametersPoint_valid q w hND.1) hsub (seed_nondegenerate Ξ hΞ q w hND)
  rw [←temperaturePressure_eq Ξ hΞ.1 hΞ.2.1] at H
  obtain ⟨hs,eta,heta,critical,hlimit,H⟩ := H
  refine ⟨hs,eta,heta,critical,hlimit,?_⟩
  filter_upwards [H] with p Hp
  intro he
  obtain ⟨hp,hn,hcritical,hphase,hunique⟩ := Hp he
  have hdepth {lam : ℝ} (hpos : 0<lam) (j : ℕ) :
      ExactFiniteDepth (addInteraction Ξ p lam) j ↔
        GeneralDepthPaper.IsFiniteRSB j (GeneralDepthPaper.parisiMinimizer
          ((polynomialModel Ξ hΞ.1 hΞ.2.1).addHighDegree p hp he hn lam hpos)) := by
    rw [exactFiniteDepth_iff (addInteraction Ξ p lam) (Finset.insert_nonempty _ _)
      (addInteraction_positive Ξ hΞ.2.1 p hp he hn lam hpos) j,
      addInteraction_model Ξ hΞ.1 hΞ.2.1 p hp he hn lam hpos]
  refine ⟨hp,hn,hcritical,?_,?_⟩
  · intro lam hlam
    obtain ⟨hpos,Hlam⟩ := hphase lam hlam
    exact ⟨(hdepth hpos r).trans (Hlam hpos).1,
      (hdepth hpos (r+1)).trans (Hlam hpos).2⟩
  · intro c hc Hc
    apply hunique c hc
    intro lam hlam hpos
    exact ⟨(hdepth hpos r).symm.trans (Hc lam hlam).1,
      (hdepth hpos (r+1)).symm.trans (Hc lam hlam).2⟩

end ArbitraryRSB
