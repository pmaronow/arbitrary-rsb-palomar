module

public import GeneralDepthPaper.RevisedNondegeneracyBridge
public import GeneralDepthPaper.NondegenerateStability

@[expose] public section

/-! Exact revised Propositions 2.5 and 2.8 on the positive coefficient domain
of an arbitrary nonempty finite even exponent set, including degree two.
Subcriticality is part of the actual open coefficient domain. The persistence
proof derives the atomic Hessian invariant from the paper's nondegeneracy
conditions, rather than adding it to the hypotheses. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 64

def sectionTwoCoefficientDomain (P : Finset ℕ) : Set (P → ℝ) :=
  {c | (∀ i : P, 0 < c i) ∧
    (∑ i : P, c i * (i.val : ℝ) * ((i.val - 1 : ℕ) : ℝ) * (0 : ℝ) ^ (i.val - 2)) < 1}

theorem isOpen_sectionTwoCoefficientDomain (P : Finset ℕ) :
    IsOpen (sectionTwoCoefficientDomain P) := by
  have hp : IsOpen {c : P → ℝ | ∀ i : P, 0 < c i} := by
    have he : {c : P → ℝ | ∀ i : P, 0 < c i} =
        ⋂ i : P, {c : P → ℝ | 0 < c i} := by ext c; simp
    rw [he]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (continuous_apply i))
  have hs : IsOpen {c : P → ℝ |
      (∑ i : P, c i * (i.val : ℝ) * ((i.val - 1 : ℕ) : ℝ) * (0 : ℝ) ^ (i.val - 2)) < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  exact hp.inter hs

def sectionTwoCovariance (P : Finset ℕ) (hP : P.Nonempty)
    (hp : ∀ p ∈ P, 2 ≤ p) (he : ∀ p ∈ P, Even p)
    (c : P → ℝ) (hc : ∀ i : P, 0 < c i) : AdmissibleCovariance where
  degrees := P
  nonempty := hP
  coefficient p := if h : p ∈ P then c ⟨p, h⟩ else 0
  coefficient_pos p h := by simpa only [dite_eq_left h] using hc ⟨p, h⟩
  degree_ge_two := hp
  degree_even := he

theorem sectionTwoCovariance_sum (P : Finset ℕ) (hP : P.Nonempty)
    (hp : ∀ p ∈ P, 2 ≤ p) (he : ∀ p ∈ P, Even p)
    (c : P → ℝ) (hc : ∀ i : P, 0 < c i) (f : ℕ → ℝ) :
    (∑ p ∈ P, (sectionTwoCovariance P hP hp he c hc).coefficient p * f p) =
      ∑ i : P, c i * f i := by
  rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [sectionTwoCovariance, dite_eq_left i.property]

theorem sectionTwoCovariance_value (P : Finset ℕ) (hP : P.Nonempty)
    (hp : ∀ p ∈ P, 2 ≤ p) (he : ∀ p ∈ P, Even p)
    (c : P → ℝ) (hc : ∀ i : P, 0 < c i) (q : ℝ) :
    (sectionTwoCovariance P hP hp he c hc).value q = ∑ i : P, c i * q ^ i.val :=
  sectionTwoCovariance_sum P hP hp he c hc (fun p => q ^ p)

theorem sectionTwoCovariance_second_zero (P : Finset ℕ) (hP : P.Nonempty)
    (hp : ∀ p ∈ P, 2 ≤ p) (he : ∀ p ∈ P, Even p)
    (c : P → ℝ) (hc : ∀ i : P, 0 < c i) :
    (sectionTwoCovariance P hP hp he c hc).second 0 =
      ∑ i : P, c i * (i.val : ℝ) * ((i.val - 1 : ℕ) : ℝ) * (0 : ℝ) ^ (i.val - 2) := by
  simpa only [AdmissibleCovariance.second, sectionTwoCovariance, mul_assoc] using
    sectionTwoCovariance_sum P hP hp he c hc
    (fun p => (p : ℝ) * ((p - 1 : ℕ) : ℝ) * (0 : ℝ) ^ (p - 2))

def sectionTwoCoefficientFamily (P : Finset ℕ) (hP : P.Nonempty)
    (hp : ∀ p ∈ P, 2 ≤ p) (he : ∀ p ∈ P, Even p) :
    SmoothCovarianceFamily (P → ℝ) where
  domain := sectionTwoCoefficientDomain P
  isOpen_domain := isOpen_sectionTwoCoefficientDomain P
  covariance c := @dite AdmissibleCovariance (c ∈ sectionTwoCoefficientDomain P)
    (Classical.propDecidable _)
    (fun hc => sectionTwoCovariance P hP hp he c hc.1)
    (fun _ => sectionTwoCovariance P hP hp he (fun _ => 1) (by intro i; norm_num))
  degrees := P
  degrees_eq c hc := by rw [dite_eq_left hc]; rfl
  smooth_coefficient p hpm := by
    intro c hc
    have H : ∀ᶠ u in 𝓝 c, u ∈ sectionTwoCoefficientDomain P :=
      (isOpen_sectionTwoCoefficientDomain P).mem_nhds hc
    apply ContDiffAt.contDiffWithinAt
    apply (contDiffAt_apply ℝ ℝ (⟨p, hpm⟩ : P) c).congr_of_eventuallyEq
    filter_upwards [H] with u hu
    simp only [dite_eq_left hu, sectionTwoCovariance, dite_eq_left hpm]

@[simp] theorem sectionTwoCoefficientFamily_covariance (P : Finset ℕ) (hP : P.Nonempty)
    (hp : ∀ p ∈ P, 2 ≤ p) (he : ∀ p ∈ P, Even p)
    (c : P → ℝ) (hc : c ∈ sectionTwoCoefficientDomain P) :
    (sectionTwoCoefficientFamily P hP hp he).covariance c =
      sectionTwoCovariance P hP hp he c hc.1 := by
  simp only [sectionTwoCoefficientFamily, dite_eq_left hc]

theorem sectionTwoCoefficientFamily_subcritical (P : Finset ℕ) (hP : P.Nonempty)
    (hp : ∀ p ∈ P, 2 ≤ p) (he : ∀ p ∈ P, Even p)
    (c : P → ℝ) (hc : c ∈ sectionTwoCoefficientDomain P) :
    ((sectionTwoCoefficientFamily P hP hp he).covariance c).IsSubcritical := by
  rw [sectionTwoCoefficientFamily_covariance P hP hp he c hc]
  change (sectionTwoCovariance P hP hp he c hc.1).second 0 < 1
  rw [sectionTwoCovariance_second_zero]
  exact hc.2

/-- Literal revised Proposition 2.5: the actual atomic Parisi functional is
C∞ jointly in all positive subcritical coefficients and all valid atom
coordinates. The finite exponent set may contain two. -/
theorem revised_proposition_2_5 (P : Finset ℕ) (hP : P.Nonempty)
    (hp : ∀ p ∈ P, 2 ≤ p) (he : ∀ p ∈ P, Even p) (r : ℕ) :
    ContDiffOn ℝ ∞
      (fun p : (P → ℝ) × AtomicPoint r =>
        atomicFunctionalExtension ((sectionTwoCoefficientFamily P hP hp he).covariance p.1) r p.2)
      (sectionTwoCoefficientDomain P ×ˢ {z : AtomicPoint r | IsAtomicPoint z}) :=
  (sectionTwoCoefficientFamily P hP hp he).finite_step_regularity r

/-- Literal revised Proposition 2.8. Its hypothesis is paper nondegeneracy,
and its conclusion is a smooth family of actual unique, finite-depth Parisi
measures retaining that same paper nondegeneracy. -/
theorem revised_proposition_2_8 (P : Finset ℕ) (hP : P.Nonempty)
    (hp : ∀ p ∈ P, 2 ≤ p) (he : ∀ p ∈ P, Even p)
    (c : P → ℝ) (hc : c ∈ sectionTwoCoefficientDomain P) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (hND : PaperNondegenerate ((sectionTwoCoefficientFamily P hP hp he).covariance c) z hz) :
    ∃ V : Set (P → ℝ), IsOpen V ∧ c ∈ V ∧ V ⊆ sectionTwoCoefficientDomain P ∧
      ∃ zF : (P → ℝ) → AtomicPoint r,
        zF c = z ∧ ContDiffOn ℝ ∞ zF V ∧
        ∀ u ∈ V, ∃ hu : IsAtomicPoint (zF u),
          PaperNondegenerate ((sectionTwoCoefficientFamily P hP hp he).covariance u) (zF u) hu ∧
          atomicMeasure (zF u) hu = parisiMinimizer
            ((sectionTwoCoefficientFamily P hP hp he).covariance u) ∧
          IsFiniteRSB r (parisiMinimizer
            ((sectionTwoCoefficientFamily P hP hp he).covariance u)) := by
  let F := sectionTwoCoefficientFamily P hP hp he
  have hsub : (F.covariance c).IsSubcritical :=
    sectionTwoCoefficientFamily_subcritical P hP hp he c hc
  have hstrong := nondegenerate_of_paperNondegenerate (F.covariance c) z hz hND hsub
  obtain ⟨V, hV, hcV, hVD, zF, hvalue, hsmooth, hdata⟩ :=
    F.nondegenerate_stability hc z hz hstrong
  refine ⟨V, hV, hcV, hVD, zF, hvalue, hsmooth, ?_⟩
  intro u hu
  obtain ⟨hzu, hN⟩ := hdata u hu
  have heq : atomicMeasure (zF u) hzu = parisiMinimizer (F.covariance u) :=
    parisiMinimizer_unique _ _ hN.1
  refine ⟨hzu, ⟨hN.1, hN.2.1, hN.2.2.1⟩, heq, ?_⟩
  rw [← heq]
  exact atomicMeasure_isFiniteRSB (zF u) hzu

end GeneralDepthPaper
