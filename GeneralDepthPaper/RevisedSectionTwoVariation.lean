module

public import GeneralDepthPaper.FirstVariationCriterion
public import GeneralDepthPaper.AtomicGradient
public import GeneralDepthPaper.RevisedNondegeneracyBridge
public import DepthPaper.RevisedCriticalHessian

@[expose] public section

/-! Expanded revised Proposition 2.1 and Corollary 2.4, with the actual
functional, actual probability-measure curves and all lower-mass factors.
The general covariance datatype permits every positive finite even mixture
including quadratic terms. The derivative conclusions hold for arbitrary
probability measures, strengthening their atomic source scope. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem hasDerivWithinAt_newPoint_mass (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) (Q : Overlap) :
    HasDerivWithinAt
      (fun m => parisiFunctional Ξ
        (Paper.parisiMix μ (Measure.dirac Q).toProbabilityMeasure (1 - m)))
      (firstVariation Ξ μ Q - ∫ q : Overlap, firstVariation Ξ μ q ∂(μ : Measure Overlap))
      (Iio (1 : ℝ)) 1 := by
  have hd := hasDerivWithinAt_parisiFunctional_mix Ξ μ (Measure.dirac Q).toProbabilityMeasure
  have ha : HasDerivWithinAt (fun m : ℝ => 1 - m) (-1) (Iio (1 : ℝ)) 1 := by
    convert! ((hasDerivAt_const (1 : ℝ) (1 : ℝ)).sub
      (hasDerivAt_id (1 : ℝ))).hasDerivWithinAt using 1
    norm_num
  have hmap : MapsTo (fun m : ℝ => 1 - m) (Iio (1 : ℝ)) (Ioi (0 : ℝ)) := by
    intro m hm
    change 0 < 1 - m
    change m < 1 at hm
    linarith
  have hc := hd.comp_of_eq (1 : ℝ) ha hmap (by norm_num)

  have hdirac : (∫ q : Overlap, firstVariation Ξ μ q
      ∂((Measure.dirac Q).toProbabilityMeasure : Measure Overlap)) = firstVariation Ξ μ Q := by
    change (∫ q : Overlap, firstVariation Ξ μ q ∂Measure.dirac Q) = _
    exact integral_dirac _ _
  rw [hdirac] at hc
  convert! hc using 1 <;> first | rfl | ring

/-- All four conclusions of revised Proposition 2.1, including the left
mass derivative at one and unique global minimization over all measures. -/
theorem revised_proposition_2_1 (Ξ : AdmissibleCovariance) (_hsub : Ξ.IsSubcritical) :
    (∀ μ ν : ParisiMeasure,
      HasDerivWithinAt (fun t => parisiFunctional Ξ (Paper.parisiMix μ ν t))
        (-((∫ q : Overlap, firstVariation Ξ μ q ∂(ν : Measure Overlap)) -
          (∫ q : Overlap, firstVariation Ξ μ q ∂(μ : Measure Overlap)))) (Ioi (0 : ℝ)) 0) ∧
    (∀ (μ : ParisiMeasure) (Q : Overlap),
      HasDerivWithinAt (fun m => parisiFunctional Ξ
        (Paper.parisiMix μ (Measure.dirac Q).toProbabilityMeasure (1 - m)))
        (firstVariation Ξ μ Q - ∫ q : Overlap, firstVariation Ξ μ q ∂(μ : Measure Overlap))
        (Iio (1 : ℝ)) 1) ∧
    (∀ (μ : ParisiMeasure) (a : Overlap), (a : ℝ) ∈ Ioo (0 : ℝ) 1 →
      HasDerivAt (fun t => parisiFunctional Ξ (moveAtom μ a t))
        (-atomWeight μ a * firstVariationDerivative Ξ μ a) 0) ∧
    (∀ (μ : ParisiMeasure) (a b : Overlap), 0 < atomWeight μ a → 0 < atomWeight μ b →
      HasDerivAt (fun t => parisiFunctional Ξ (transferAtomMass μ a b t))
        (firstVariation Ξ μ b - firstVariation Ξ μ a) 0) ∧
    (∀ μ : ParisiMeasure,
      (∀ q ∈ Icc (0 : ℝ) 1, firstVariation Ξ μ q ≤ 0) →
      (μ : Measure Overlap) {q | firstVariation Ξ μ q = 0} = 1 →
      μ = parisiMinimizer Ξ) :=
  ⟨hasDerivWithinAt_parisiFunctional_mix Ξ,
    hasDerivWithinAt_newPoint_mass Ξ,
    hasDerivAt_parisiFunctional_moveAtom Ξ,
    hasDerivAt_parisiFunctional_transferAtomMass Ξ,
    unique_minimizer_of_firstVariation_criterion Ξ⟩

/-- The source's nondegeneracy definition, expanded without a Hessian
premise. Admissibility's separate subcriticality is not part of this
predicate. The actual measure has exactly `r+1` positive support atoms. -/
theorem revised_definition_2_3 (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) :
    PaperNondegenerate Ξ z hz ↔
      IsParisiMinimizer Ξ (atomicMeasure z hz) ∧
      (∀ q ∈ Icc (0 : ℝ) 1, firstVariation Ξ (atomicMeasure z hz) q ≤ 0 ∧
        (firstVariation Ξ (atomicMeasure z hz) q = 0 ↔ ∃ i, q = atomicLocation z i)) ∧
      (∀ i : Fin r, closedJet 1 2 (firstVariation Ξ (atomicMeasure z hz)) (z.1 i) < 0) :=
  Iff.rfl

/-- Literal revised Corollary 2.4: independent coordinate partials and the
equivalence between zero actual chart derivative and support contact
conditions, including depth zero and lower mass one. -/
theorem revised_corollary_2_4 (Ξ : AdmissibleCovariance) (_hsub : Ξ.IsSubcritical) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m ∈ Ioc (0 : ℝ) 1)
    (Q : Overlap) (hQ : atomicLocation z (Fin.last r) < (Q : ℝ) ∧ (Q : ℝ) < 1) :
    (∀ i : Fin r,
      fderiv ℝ (partialAtomicFunctionalExtension Ξ r m Q) z (atomicLocationDirection i) =
        -(m * atomicWeight z i.succ) *
          firstVariationDerivative Ξ (partialAtomicMeasure z hz m Q) (z.1 i)) ∧
    (∀ i : Fin r,
      fderiv ℝ (partialAtomicFunctionalExtension Ξ r m Q) z (atomicMassDirection i) =
        m * (firstVariation Ξ (partialAtomicMeasure z hz m Q) (atomicLocation z (Fin.last r)) -
          firstVariation Ξ (partialAtomicMeasure z hz m Q) (atomicLocation z i.castSucc))) ∧
    (fderiv ℝ (partialAtomicFunctionalExtension Ξ r m Q) z = 0 ↔
      (∀ q ∈ (atomicMeasure z hz : Measure Overlap).support,
        firstVariation Ξ (partialAtomicMeasure z hz m Q) q = 0) ∧
      (∀ q ∈ (atomicMeasure z hz : Measure Overlap).support, q ≠ ⟨0, by norm_num⟩ →
        firstVariationDerivative Ξ (partialAtomicMeasure z hz m Q) q = 0)) :=
  ⟨fderiv_partialAtomicFunctional_location Ξ z hz m hm Q hQ,
    fderiv_partialAtomicFunctional_mass Ξ z hz m hm Q hQ,
    atomic_gradient_zero_iff Ξ z hz m hm Q hQ⟩

/-- Literal revised Lemma 2.6 for the quadratic-inclusive actual covariance.
The only analytic hypotheses are actual chart criticality and negative
contact curvature; global minimality and Hessian positivity are not inputs. -/
theorem revised_lemma_2_6 (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (hs : fderiv ℝ (atomicFunctionalExtension Ξ r) z=0)
    (hcurv : ∀i : Fin r,closedJet 1 2 (firstVariation Ξ (atomicMeasure z hz)) (z.1 i)<0) :
    ∀v : AtomicPoint r,v≠0 →
      0<(fderiv ℝ (fun y=>fderiv ℝ (atomicFunctionalExtension Ξ r) y) z v) v := by
  have hsR : fderiv ℝ (DepthPaper.RevisedCovariance.atomicFunctionalExtension
      Ξ.toRevisedCovariance r) z=0 := by
    simpa only [revised_atomicFunctionalExtension] using hs
  have hcR : ∀i : Fin r,DepthPaper.closedJet 1 2
      (DepthPaper.RevisedCovariance.firstVariation Ξ.toRevisedCovariance
        (DepthPaper.atomicMeasure z ((revised_isAtomicPoint z).mpr hz))) (z.1 i)<0 := by
    rw [revised_atomicMeasure z hz]
    simpa only [revised_firstVariation,revised_closedJet] using hcurv
  have H:=DepthPaper.RevisedCovariance.atomic_hessian Ξ.toRevisedCovariance z
    ((revised_isAtomicPoint z).mpr hz) hsR hcR
  exact positiveAtomicHessian_of_revised Ξ z H

theorem revised_lemma_2_9 :
    (∀q:ℝ,quarticSeed.value q=q^4/16) ∧ quarticSeed.IsSubcritical ∧
    parisiMinimizer quarticSeed=Paper.diracOverlap 0 (by norm_num) ∧
    PaperNondegenerate quarticSeed (0:AtomicPoint 0) isAtomicPoint_zero_depth ∧
    IsFiniteRSB 0 (parisiMinimizer quarticSeed) ∧
    (∀μ:ParisiMeasure,∀q∈Ioc (0:ℝ) 1,firstVariation quarticSeed μ q<0) := by
  have hND:= (nondegenerate_iff_paperNondegenerate_and_subcritical
    quarticSeed (0:AtomicPoint 0) isAtomicPoint_zero_depth).mp quarticSeed_nondegenerate
  exact ⟨quarticSeed_value,hND.2,quarticSeed_parisiMinimizer,hND.1,
    quarticSeed_zero_RSB,fun μ _ hq=>quarticSeed_firstVariation_neg μ hq⟩

end GeneralDepthPaper
