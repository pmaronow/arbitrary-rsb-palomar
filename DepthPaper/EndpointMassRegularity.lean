module

public import DepthPaper.EndpointRemainderDerivative
public import DepthPaper.WeakVariationContinuity

@[expose] public section


/-! Actual mass-continuity of the endpoint observable and actual smooth
mixed derivatives of the cutoff remainder. No state-continuity premise is
introduced at the disappearing top atom. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff BigOperators
namespace DepthPaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

def lowerMassDirection {r : ℕ} : CutoffInputParameter r := ((0,0),(1,(0,0)))

def lowerRemainderMassEndpointDerivative (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (qc : ℝ) (x : CutoffInputParameter r) : ℝ :=
  fderiv ℝ (lowerRemainderEndpointDerivative Ξ p qc) x lowerMassDirection

theorem contDiffOn_lowerRemainderEndpointDerivative (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (qc : ℝ) : ContDiffOn ℝ ∞ (lowerRemainderEndpointDerivative (r:=r) Ξ p qc)
      (cutoffInputSmoothDomain Ξ p qc) :=
  ((contDiffOn_lowerRecursionErrorRaw Ξ p qc).fderiv_of_isOpen
    (isOpen_cutoffInputSmoothDomain Ξ p qc) (by simp)).clm_apply contDiffOn_const

theorem contDiffOn_lowerRemainderMassEndpointDerivative (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (qc : ℝ) : ContDiffOn ℝ ∞ (lowerRemainderMassEndpointDerivative (r:=r) Ξ p qc)
      (cutoffInputSmoothDomain Ξ p qc) :=
  ((contDiffOn_lowerRemainderEndpointDerivative Ξ p qc).fderiv_of_isOpen
    (isOpen_cutoffInputSmoothDomain Ξ p qc) (by simp)).clm_apply contDiffOn_const

theorem hasDerivAt_massSection {r : ℕ} {f : CutoffInputParameter r→ℝ}
    (z : AtomicPoint r) (m lam Q : ℝ)
    (hf : DifferentiableAt ℝ f (z,(m,(lam,Q)))) :
    HasDerivAt (fun s:ℝ=>f (z,(s,(lam,Q))))
      (fderiv ℝ f (z,(m,(lam,Q))) lowerMassDirection) m := by
  have hcurve : HasDerivAt (fun s:ℝ=>(z,(s,(lam,Q)))) lowerMassDirection m :=
    (hasDerivAt_const m z).prodMk ((hasDerivAt_id m).prodMk (hasDerivAt_const m (lam,Q)))
  exact hf.hasFDerivAt.comp_hasDerivAt m hcurve

theorem hasDerivAt_lowerRemainderEndpointDerivative_mass (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (z : AtomicPoint r) (hz : IsAtomicPoint z) {m lam Q qc : ℝ}
    (hm : m∈Ioo (0:ℝ) 2) (hc : atomicLocation z (Fin.last r)<qc) (hlam : 0≤lam)
    (hW : 0<endpointVarianceExpression Ξ p qc (lam,Q)) :
    HasDerivAt (fun s:ℝ=>lowerRemainderEndpointDerivative Ξ p qc (z,(s,(lam,Q))))
      (lowerRemainderMassEndpointDerivative Ξ p qc (z,(m,(lam,Q)))) m := by
  have hmem := cutoffInputSmoothDomain_mem Ξ p (z,(m,(lam,Q))) hz hc hm hlam hW
  apply hasDerivAt_massSection
  exact (((contDiffOn_lowerRemainderEndpointDerivative Ξ p qc) _ hmem).contDiffAt
    ((isOpen_cutoffInputSmoothDomain Ξ p qc).mem_nhds hmem)).differentiableAt (by simp)

theorem continuousOn_lowerRemainderMassEndpointDerivative_mass (Ξ : AdmissibleCovariance)
    {r : ℕ} (p : ℕ) (z : AtomicPoint r) (hz : IsAtomicPoint z) {a lam Q qc : ℝ}
    (ha : 0<a) (hc : atomicLocation z (Fin.last r)<qc) (hlam : 0≤lam)
    (hW : 0<endpointVarianceExpression Ξ p qc (lam,Q)) :
    ContinuousOn (fun m:ℝ=>lowerRemainderMassEndpointDerivative Ξ p qc (z,(m,(lam,Q))))
      (Icc a 1) := by
  apply (contDiffOn_lowerRemainderMassEndpointDerivative Ξ p qc).continuousOn.comp
    (show ContinuousOn (fun m:ℝ=>(z,(m,(lam,Q)))) (Icc a 1) by fun_prop)
  intro m hm
  exact cutoffInputSmoothDomain_mem Ξ p _ hz hc
    ⟨ha.trans_le hm.1,hm.2.trans_lt (by norm_num)⟩ hlam hW

theorem continuousOn_twoLevelMeasure_mass {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (Q : Overlap) : ContinuousOn (fun m:ℝ=>twoLevelMeasure z hz m Q) (Icc (0:ℝ) 1) := by
  intro m hm
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have he : ∀s∈Icc (0:ℝ) 1,(∫q,f q ∂(twoLevelMeasure z hz s Q : Measure Overlap))=
      (1-s)*f Q+s*(∫q,f q ∂(atomicMeasure z hz : Measure Overlap)) := by
    intro s hs
    rw [twoLevelMeasure,partialAtomicMeasure,Paper.integral_parisiMix f.continuous _ _ _ hs]
    simp only [Measure.toProbabilityMeasure,ProbabilityMeasure.toMeasure,integral_dirac]
  have ht : Tendsto (fun s:ℝ=>(1-s)*f Q+s*(∫q,f q ∂(atomicMeasure z hz : Measure Overlap)))
      (𝓝[Icc (0:ℝ) 1] m) (𝓝 ((1-m)*f Q+m*(∫q,f q ∂(atomicMeasure z hz : Measure Overlap)))) :=
    (by fun_prop : Continuous _).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [he m hm]
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (he s hs).symm

theorem continuousOn_twoLevelGamma_mass (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (Q : Overlap) :
    ContinuousOn (fun m:ℝ=>Gamma Ξ (twoLevelMeasure z hz m Q) Q) (Icc (0:ℝ) 1) := by
  intro m hm
  have ht := tendsto_GammaMap_of_weak Ξ (fun s:ℝ=>twoLevelMeasure z hz s Q)
    (twoLevelMeasure z hz m Q) (continuousOn_twoLevelMeasure_mass z hz Q m hm)
  exact (continuous_eval_const Q).continuousAt.tendsto.comp ht

end DepthPaper
