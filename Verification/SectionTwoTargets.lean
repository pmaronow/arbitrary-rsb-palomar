module

public import GeneralDepthPaper.RevisedSectionTwoVariation
public import GeneralDepthPaper.RevisedSectionTwoCurvature
public import GeneralDepthPaper.RevisedSectionTwoCoefficients
public import GeneralDepthPaper.RevisedSectionTwoPersistence
public import GeneralDepthPaper.RevisedSectionTwoPartition

@[expose] public section

/-! Literal Section 2 and Lemma 3.1 target audit. Every covariance may
include a quadratic interaction. All functionals, derivatives, CDFs,
optimizers, and lower Gaussian recursions are concrete actual objects.
The analytic/martingale target for Lemma 2.2 explicitly excludes its
Hessian stochastic-integral clause. The full printed finite-support target,
including the physical-time Brownian clause, is in
`Verification.PhysicalStochasticTargets`. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ContDiff
namespace Verification.SectionTwoTargets
open GeneralDepthPaper

theorem proposition2_1_exact (Ξ : AdmissibleCovariance) (_hsub : Ξ.IsSubcritical) :
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
      μ = parisiMinimizer Ξ) := by
  simpa only [PaperNondegenerate] using revised_proposition_2_1 Ξ _hsub

theorem lemma2_2_analytic_martingale_exact (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) :
    (∀q∈Icc (0:ℝ) 1,∀x, |gradient Ξ μ q x|≤1 ∧
      0<hessian Ξ μ q x ∧ hessian Ξ μ q x≤1-gradient Ξ μ q x^2) ∧
    Martingale (sectionTwoGradientProcess Ξ μ) (sectionTwoGradientFiltration Ξ)
      Paper.canonicalBrownianMeasure ∧
    (∀sample,sectionTwoGradientProcess Ξ μ ⟨0,by norm_num⟩ sample=0 ∧
      sectionTwoGradientProcess Ξ μ ⟨1,by norm_num⟩ sample=Real.tanh (optimalState Ξ μ sample 1)) ∧
    ContDiffOn ℝ 1 (Gamma Ξ μ) (Icc (0:ℝ) 1) ∧ Gamma Ξ μ 0=0 ∧
    (∀q∈Icc (0:ℝ) 1,
      HasDerivWithinAt (Gamma Ξ μ)
        (Ξ.second q*(∫sample,hessian Ξ μ q (optimalState Ξ μ sample q)^2 ∂Paper.canonicalBrownianMeasure))
        (Icc (0:ℝ) 1) q ∧
      0≤derivWithin (Gamma Ξ μ) (Icc (0:ℝ) 1) q ∧
      derivWithin (Gamma Ξ μ) (Icc (0:ℝ) 1) q≤Ξ.second q*(1-Gamma Ξ μ q) ∧
      Gamma Ξ μ q≤Ξ.first q) := by
  simpa only [PaperNondegenerate] using revised_lemma_2_2_analytic_martingale Ξ μ

theorem definition2_3_exact (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) :
    PaperNondegenerate Ξ z hz ↔
      IsParisiMinimizer Ξ (atomicMeasure z hz) ∧
      (∀ q ∈ Icc (0 : ℝ) 1, firstVariation Ξ (atomicMeasure z hz) q ≤ 0 ∧
        (firstVariation Ξ (atomicMeasure z hz) q = 0 ↔ ∃ i, q = atomicLocation z i)) ∧
      (∀ i : Fin r, closedJet 1 2 (firstVariation Ξ (atomicMeasure z hz)) (z.1 i) < 0) := by
  exact revised_definition_2_3 Ξ z hz

theorem corollary2_4_exact (Ξ : AdmissibleCovariance) (_hsub : Ξ.IsSubcritical) {r : ℕ}
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
        firstVariationDerivative Ξ (partialAtomicMeasure z hz m Q) q = 0)) := by
  simpa only [PaperNondegenerate] using revised_corollary_2_4 Ξ _hsub z hz m hm Q hQ

theorem proposition2_5_exact (P : Finset ℕ) (hP : P.Nonempty)
    (hp : ∀ p ∈ P, 2 ≤ p) (he : ∀ p ∈ P, Even p) (r : ℕ) :
    ContDiffOn ℝ ∞
      (fun p : (P → ℝ) × AtomicPoint r =>
        atomicFunctionalExtension ((sectionTwoCoefficientFamily P hP hp he).covariance p.1) r p.2)
      (sectionTwoCoefficientDomain P ×ˢ {z : AtomicPoint r | IsAtomicPoint z}) := by
  simpa only [PaperNondegenerate] using revised_proposition_2_5 P hP hp he r

theorem lemma2_6_exact (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (hs : fderiv ℝ (atomicFunctionalExtension Ξ r) z=0)
    (hcurv : ∀i : Fin r,closedJet 1 2 (firstVariation Ξ (atomicMeasure z hz)) (z.1 i)<0) :
    ∀v : AtomicPoint r,v≠0 →
      0<(fderiv ℝ (fun y=>fderiv ℝ (atomicFunctionalExtension Ξ r) y) z v) v := by
  simpa only [PaperNondegenerate] using revised_lemma_2_6 Ξ z hz hs hcurv

theorem lemma2_7_exact
    (Ξn : ℕ → AdmissibleCovariance) (Ξ : AdmissibleCovariance)
    (_hsubN : ∀ n, (Ξn n).IsSubcritical) (hsub : Ξ.IsSubcritical) {r : ℕ}
    (zn : ℕ → AtomicPoint r) (hzN : ∀ n, IsAtomicPoint (zn n))
    (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (hΞ : ∀ j : Fin 4, Tendsto (fun n => covarianceJetMap (Ξn n) j) atTop
      (𝓝 (covarianceJetMap Ξ j)))
    (hzlim : Tendsto zn atTop (𝓝 z)) :
    (∀ j ≤ 2, TendstoUniformlyOn
      (fun n => closedJet 1 j (firstVariation (Ξn n) (atomicMeasure (zn n) (hzN n))))
      (closedJet 1 j (firstVariation Ξ (atomicMeasure z hz))) atTop (Icc (0 : ℝ) 1)) ∧
    ((IsParisiMinimizer Ξ (atomicMeasure z hz) ∧
      (∀q∈Icc (0:ℝ) 1,firstVariation Ξ (atomicMeasure z hz) q≤0 ∧
        (firstVariation Ξ (atomicMeasure z hz) q=0 ↔ ∃i,q=atomicLocation z i)) ∧
      (∀i:Fin r,closedJet 1 2 (firstVariation Ξ (atomicMeasure z hz)) (z.1 i)<0)) →
      (∀ n, fderiv ℝ (atomicFunctionalExtension (Ξn n) r) (zn n) = 0) →
      ∀ᶠ n in atTop,
        (IsParisiMinimizer (Ξn n) (atomicMeasure (zn n) (hzN n)) ∧
          (∀q∈Icc (0:ℝ) 1,firstVariation (Ξn n) (atomicMeasure (zn n) (hzN n)) q≤0 ∧
            (firstVariation (Ξn n) (atomicMeasure (zn n) (hzN n)) q=0 ↔
              ∃i,q=atomicLocation (zn n) i)) ∧
          (∀i:Fin r,closedJet 1 2 (firstVariation (Ξn n)
            (atomicMeasure (zn n) (hzN n))) ((zn n).1 i)<0)) ∧
        atomicMeasure (zn n) (hzN n) = parisiMinimizer (Ξn n) ∧
        IsFiniteRSB r (parisiMinimizer (Ξn n))) := by
  simpa only [PaperNondegenerate] using revised_lemma_2_7 Ξn Ξ _hsubN hsub zn hzN z hz hΞ hzlim

theorem proposition2_8_exact (P : Finset ℕ) (hP : P.Nonempty)
    (hp : ∀ p ∈ P, 2 ≤ p) (he : ∀ p ∈ P, Even p)
    (c : P → ℝ) (hc : c ∈ sectionTwoCoefficientDomain P) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (hND : (IsParisiMinimizer ((sectionTwoCoefficientFamily P hP hp he).covariance c) (atomicMeasure z hz) ∧
            (∀q∈Icc (0:ℝ) 1,firstVariation ((sectionTwoCoefficientFamily P hP hp he).covariance c) (atomicMeasure z hz) q≤0 ∧
              (firstVariation ((sectionTwoCoefficientFamily P hP hp he).covariance c) (atomicMeasure z hz) q=0 ↔ ∃i,q=atomicLocation z i)) ∧
            (∀i:Fin r,closedJet 1 2 (firstVariation ((sectionTwoCoefficientFamily P hP hp he).covariance c) (atomicMeasure z hz)) (z.1 i)<0))) :
    ∃ V : Set (P → ℝ), IsOpen V ∧ c ∈ V ∧ V ⊆ sectionTwoCoefficientDomain P ∧
      ∃ zF : (P → ℝ) → AtomicPoint r,
        zF c = z ∧ ContDiffOn ℝ ∞ zF V ∧
        ∀ u ∈ V, ∃ hu : IsAtomicPoint (zF u),
          (IsParisiMinimizer ((sectionTwoCoefficientFamily P hP hp he).covariance u) (atomicMeasure (zF u) hu) ∧
            (∀q∈Icc (0:ℝ) 1,firstVariation ((sectionTwoCoefficientFamily P hP hp he).covariance u) (atomicMeasure (zF u) hu) q≤0 ∧
              (firstVariation ((sectionTwoCoefficientFamily P hP hp he).covariance u) (atomicMeasure (zF u) hu) q=0 ↔ ∃i,q=atomicLocation (zF u) i)) ∧
            (∀i:Fin r,closedJet 1 2 (firstVariation ((sectionTwoCoefficientFamily P hP hp he).covariance u) (atomicMeasure (zF u) hu)) ((zF u).1 i)<0)) ∧
          atomicMeasure (zF u) hu = parisiMinimizer
            ((sectionTwoCoefficientFamily P hP hp he).covariance u) ∧
          IsFiniteRSB r (parisiMinimizer
            ((sectionTwoCoefficientFamily P hP hp he).covariance u)) := by
  simpa only [PaperNondegenerate] using revised_proposition_2_8 P hP hp he c hc z hz hND

theorem lemma2_9_exact :
    (∀q:ℝ,quarticSeed.value q=q^4/16) ∧ quarticSeed.IsSubcritical ∧
    parisiMinimizer quarticSeed=Paper.diracOverlap 0 (by norm_num) ∧
    (IsParisiMinimizer quarticSeed (atomicMeasure (0:AtomicPoint 0) isAtomicPoint_zero_depth) ∧
      (∀q∈Icc (0:ℝ) 1,firstVariation quarticSeed
        (atomicMeasure (0:AtomicPoint 0) isAtomicPoint_zero_depth) q≤0 ∧
        (firstVariation quarticSeed (atomicMeasure (0:AtomicPoint 0) isAtomicPoint_zero_depth) q=0 ↔
          ∃i,q=atomicLocation (0:AtomicPoint 0) i)) ∧
      (∀i:Fin 0,closedJet 1 2 (firstVariation quarticSeed
        (atomicMeasure (0:AtomicPoint 0) isAtomicPoint_zero_depth)) ((0:AtomicPoint 0).1 i)<0)) ∧
    IsFiniteRSB 0 (parisiMinimizer quarticSeed) ∧
    (∀μ:ParisiMeasure,∀q∈Ioc (0:ℝ) 1,firstVariation quarticSeed μ q<0) := by
  simpa only [PaperNondegenerate] using revised_lemma_2_9

theorem lemma3_1_exact (Ξ : AdmissibleCovariance) (ν : ParisiMeasure)
    (hν : (ν:Measure Overlap).support.Finite)
    (m : ℝ) (hm : m∈Ioc (0:ℝ) 1) (qc : ℝ) (hc : qc∈Ioc (0:ℝ) 1)
    (hs : ∀s∈FRSB.parisiSupport ν,s<qc) :
    ∀q∈Icc (0:ℝ) qc,∀x,
      (sectionTwoAtomicLowerData Ξ ν hν m hm qc hc (fun s hs'=> (hs s hs').le)).potential q x=
        m⁻¹*potential (Ξ.temperatureScale m hm.1.ne') ν q (m*x)-
          m/2*(Ξ.first 1-Ξ.first qc) := by
  simpa only [PaperNondegenerate] using revised_lemma_3_1_finite_atomic Ξ ν hν m hm qc hc hs

end Verification.SectionTwoTargets
