module

public import GeneralDepthPaper.LowerRecursionErrorBound
public import GeneralDepthPaper.DirectionalWordJets

@[expose] public section


/-! An actual open smooth domain for the cutoff remainder. This supplies
literal ordered coordinate derivatives, including an open extension past
mass one, rather than merely restricted boundary derivatives. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
namespace GeneralDepthPaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

def cutoffInputSmoothDomain (Ξ : AdmissibleCovariance) {r : ℕ} (p : ℕ) (qc : ℝ) :
    Set (CutoffInputParameter r) :=
  {x | x.2.1∈Ioo (0:ℝ) 2 ∧
    (∀i:Fin (r+1),0<(cutoffRecursionSteps Ξ x.1 x.2.1 qc i).2) ∧
    (∀i:Fin (r+1),0<(cutoffStepsHighDegreeExtension Ξ p qc (cutoffVarianceProjection x) i).2) ∧
    0<endpointVarianceExpression Ξ p qc x.2.2}

theorem contDiff_cutoffFullVariance (Ξ : AdmissibleCovariance) {r : ℕ} (p : ℕ) (qc : ℝ) :
    ContDiff ℝ ∞ (fun x : CutoffInputParameter r => endpointVarianceExpression Ξ p qc x.2.2) := by
  unfold endpointVarianceExpression
  have hQ : ContDiff ℝ ∞ (fun x : CutoffInputParameter r => x.2.2.2) := by fun_prop
  exact ((Ξ.contDiff_first.comp hQ).sub contDiff_const).add
    ((show ContDiff ℝ ∞ (fun x : CutoffInputParameter r => x.2.2.1*(p:ℝ)) by fun_prop).mul
      ((hQ.pow (p-1)).sub contDiff_const))

theorem isOpen_cutoffInputSmoothDomain (Ξ : AdmissibleCovariance) {r : ℕ} (p : ℕ) (qc : ℝ) :
    IsOpen (cutoffInputSmoothDomain (r:=r) Ξ p qc) := by
  have hm : IsOpen {x : CutoffInputParameter r | x.2.1∈Ioo (0:ℝ) 2} :=
    isOpen_Ioo.preimage (by fun_prop)
  have hb : IsOpen {x : CutoffInputParameter r | ∀i:Fin (r+1),
      0<(cutoffRecursionSteps Ξ x.1 x.2.1 qc i).2} := by
    simp_rw [ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    have hh := ((contDiff_cutoffRecursionSteps_parameter (r:=r) Ξ qc).comp
      cutoffVarianceProjection.contDiff).continuous
    exact isOpen_lt continuous_const (continuous_snd.comp ((continuous_apply i).comp hh))
  have ha : IsOpen {x : CutoffInputParameter r | ∀i:Fin (r+1),
      0<(cutoffStepsHighDegreeExtension Ξ p qc (cutoffVarianceProjection x) i).2} := by
    simp_rw [ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    have hh := ((contDiff_cutoffStepsHighDegreeExtension (r:=r) Ξ p qc).comp
      cutoffVarianceProjection.contDiff).continuous
    exact isOpen_lt continuous_const (continuous_snd.comp ((continuous_apply i).comp hh))
  exact hm.inter (hb.inter (ha.inter (isOpen_lt continuous_const
    (contDiff_cutoffFullVariance Ξ p qc).continuous)))

theorem contDiffOn_lowerRecursionErrorRaw (Ξ : AdmissibleCovariance) {r : ℕ} (p : ℕ) (qc : ℝ) :
    ContDiffOn ℝ ∞ (lowerRecursionErrorRaw (r:=r) Ξ p qc) (cutoffInputSmoothDomain Ξ p qc) := by
  intro x hx
  have hg := contDiffAt_cutoffComparisonInput Ξ qc x hx.1
  have ht := (contDiffAt_cutoffTerminal hx.1.1.ne' hx.2.2.2).comp x
    ((show ContDiffAt ℝ ∞ (fun x : CutoffInputParameter r=>x.2.1) x by fun_prop).prodMk
      (contDiff_cutoffFullVariance Ξ p qc).contDiffAt)
  have hf := ((contDiff_cutoffStepsHighDegreeExtension Ξ p qc).contDiffAt.comp x
    cutoffVarianceProjection.contDiff.contDiffAt).prodMk ht
  have hrec := ((contDiffAt_coleHopfRecursion (r+1) (cutoffHighDegreeInput Ξ p qc x)
    hx.2.2.1).comp x hf).sub
      ((contDiffAt_coleHopfRecursion (r+1) (cutoffComparisonInput Ξ qc x)
        hx.2.1).comp x hg)
  have hs := ((terminalEvalCLM 0).contDiff.contDiffAt.comp x hrec).add
    ((contDiff_lowerCovariancePolynomial p qc).contDiffAt.comp x
      cutoffVarianceProjection.contDiff.contDiffAt)
  exact hs.contDiffWithinAt

theorem cutoffInputSmoothDomain_mem (Ξ : AdmissibleCovariance) {r : ℕ} (p : ℕ)
    {qc : ℝ} (x : CutoffInputParameter r) (hz : IsAtomicPoint x.1)
    (hc : atomicLocation x.1 (Fin.last r)<qc) (hm : x.2.1∈Ioo (0:ℝ) 2)
    (hlam : 0≤x.2.2.1) (hW : 0<endpointVarianceExpression Ξ p qc x.2.2) :
    x∈cutoffInputSmoothDomain Ξ p qc := by
  have hb := cutoffRecursionSteps_variance_pos Ξ x.1 hz x.2.1 qc hc
  refine ⟨hm,hb,fun i=>?_,hW⟩
  exact (hb i).trans_le (le_add_of_nonneg_right
    (cutoffVariancePerturbation_nonneg p (cutoffVarianceProjection x) hz hc hlam i))

end GeneralDepthPaper
