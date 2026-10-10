module

public import DepthPaper.RevisedClosedDomainIFT

@[expose] public section

/-! Exact revised Lemma B.4, with its closed-domain regularity convention
and every Euclidean dimension made explicit. -/
noncomputable section
open Set
open scoped ContDiff
namespace Verification.ClosedDomainTargets
open DepthPaper.RevisedClosedIFT

theorem lemmaB4_exact
    {d n : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))}
    {V : Set (EuclideanSpace ℝ (Fin n))}
    {Φ : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {y : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin n)}
    (hUopen : IsOpen U) (hUconvex : Convex ℝ U) (hDcompact : IsCompact (closure U))
    (hVopen : IsOpen V) (hVconvex : Convex ℝ V) (hKcompact : IsCompact (closure V))
    (k : ℕ) (hk : 1 ≤ k)
    (hΦ : ClosedInteriorCk k Φ (closure U ×ˢ closure V))
    (hzero : ∀ θ ∈ closure U, Φ (θ, y θ) = 0)
    (hunique : ∀ θ ∈ closure U, ∀ z ∈ closure V, Φ (θ, z) = 0 → z = y θ)
    (hyInterior : ∀ θ ∈ closure U, y θ ∈ interior (closure V))
    (hinv : ∀ θ ∈ closure U,
      (partialY (fderivWithin ℝ Φ (closure U ×ˢ closure V) (θ, y θ))).IsInvertible) :
    ClosedInteriorCk k y (closure U) ∧
    (∀ θ ∈ closure U, HasFDerivWithinAt y
      (implicitDerivative (fderivWithin ℝ Φ (closure U ×ˢ closure V) (θ, y θ)))
      (closure U) θ) ∧
    (∀ j : ℕ, j ≤ k → ∀ θ ∈ closure U,
      iteratedFDerivWithin ℝ j (fun u => Φ (u, y u)) (closure U) θ = 0) :=
  euclidean_closed_domain_implicit_function hUopen hUconvex hDcompact
    hVopen hVconvex hKcompact k hk hΦ hzero hunique hyInterior hinv

end Verification.ClosedDomainTargets
