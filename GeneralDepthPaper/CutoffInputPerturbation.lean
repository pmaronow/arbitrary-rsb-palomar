module

public import GeneralDepthPaper.CutoffVarianceInputJets
public import GeneralDepthPaper.CutoffEndpointErrorBound

@[expose] public section


/-! The actual full recursion input of the high-degree candidate differs
exponentially from the actual comparison input, in every fixed finite
Fréchet order, uniformly over the full physical parameter window. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff BigOperators
namespace GeneralDepthPaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

abbrev CutoffInputParameter (r : ℕ) := AtomicPoint r × (ℝ × (ℝ × ℝ))

def cutoffVarianceProjection {r : ℕ} : CutoffInputParameter r→L[ℝ] HighDegreeLowerParameter r :=
  LinearMap.mkContinuous
    { toFun := fun x => (x.1,(x.2.1,x.2.2.1))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun x => by
      rw [one_mul,Prod.norm_def,Prod.norm_def]
      exact max_le (norm_fst_le x) (max_le
        ((norm_fst_le x.2).trans (norm_snd_le x))
        ((norm_fst_le x.2.2).trans ((norm_snd_le x.2).trans (norm_snd_le x)))))

@[simp] theorem cutoffVarianceProjection_apply {r : ℕ} (x : CutoffInputParameter r) :
    cutoffVarianceProjection x=(x.1,(x.2.1,x.2.2.1)) := rfl

theorem norm_cutoffVarianceProjection_le_one {r : ℕ} :
    ‖cutoffVarianceProjection (r:=r)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

def cutoffComparisonInput (Ξ : AdmissibleCovariance) {r : ℕ} (qc : ℝ)
    (x : CutoffInputParameter r) : ColeHopfRecursionParameter (r+1) :=
  (cutoffRecursionSteps Ξ x.1 x.2.1 qc,scaledLogCoshTerminal x.2.1)

def cutoffHighDegreeInput (Ξ : AdmissibleCovariance) {r : ℕ} (p : ℕ) (qc : ℝ)
    (x : CutoffInputParameter r) : ColeHopfRecursionParameter (r+1) :=
  (cutoffStepsHighDegreeExtension Ξ p qc (cutoffVarianceProjection x),
    cutoffTerminal x.2.1 (endpointVarianceExpression Ξ p qc x.2.2))

theorem contDiff_cutoffRecursionSteps_parameter (Ξ : AdmissibleCovariance) {r : ℕ} (qc : ℝ) :
    ContDiff ℝ ∞ (fun x : HighDegreeLowerParameter r => cutoffRecursionSteps Ξ x.1 x.2.1 qc) := by
  rw [contDiff_pi]
  intro i
  have hn (k : Fin (r+2)) := (contDiff_cutoffAtomicNode qc k).comp
    (contDiff_fst (E:=AtomicPoint r) (F:=ℝ×ℝ))
  exact ((show ContDiff ℝ ∞ (fun x : HighDegreeLowerParameter r => x.2.1) by fun_prop).mul
    ((contDiff_atomicLevel i).comp contDiff_fst)).prodMk
    ((Ξ.contDiff_first.comp (hn i.succ)).sub (Ξ.contDiff_first.comp (hn i.castSucc)))

theorem contDiff_cutoffStepsHighDegreeExtension (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (qc : ℝ) :
    ContDiff ℝ ∞ (cutoffStepsHighDegreeExtension (r:=r) Ξ p qc) := by
  rw [contDiff_pi]
  intro i
  have hb := (contDiff_apply ℝ (ℝ×ℝ) i).comp (contDiff_cutoffRecursionSteps_parameter Ξ qc)
  exact (contDiff_fst.comp hb).prodMk ((contDiff_snd.comp hb).add
    (contDiff_cutoffVariancePerturbation p qc i))

theorem cutoffInputDifference_eq (Ξ : AdmissibleCovariance) {r : ℕ} (p : ℕ) (qc : ℝ) :
    (fun x : CutoffInputParameter r => cutoffHighDegreeInput Ξ p qc x-cutoffComparisonInput Ξ qc x)=
    (fun x => ((cutoffStepsHighDegreeExtension Ξ p qc (cutoffVarianceProjection x)-
        cutoffRecursionSteps Ξ x.1 x.2.1 qc),cutoffEndpointError Ξ p qc x.2)) := rfl

theorem cutoff_input_low_order_exponential_bound (Ξ : AdmissibleCovariance) {r : ℕ}
    {ε lamlo lamhi qc cQ CQ : ℝ} (hε : 0 < ε) (hlo : 0 < lamlo)
    (hLH : lamlo ≤ lamhi) (hc : qc∈Ioo (0:ℝ) 1) (hcQ : 0 < cQ)
    (B : ℝ) (N : ℕ) :
    ∃C:ℝ,0 < C ∧ ∃A:ℕ,∃c:ℝ,0 < c ∧ ∃p0:ℕ,1 ≤ p0 ∧
      ∀p:ℕ,p0 ≤ p → ∀x:CutoffInputParameter r,
        cutoffVarianceProjection x∈closedBall 0 B →
        (∀i:Fin (r+1),atomicLocation x.1 i∈Icc (0:ℝ) qc) →
        x.2.1∈Icc ε 1 → x.2.2.1∈Icc lamlo lamhi → x.2.2.2∈endpointStrip cQ CQ p →
        1 < endpointVarianceExpression Ξ p qc x.2.2 ∧
        ContDiffAt ℝ ∞ (fun y => cutoffHighDegreeInput Ξ p qc y-cutoffComparisonInput Ξ qc y) x ∧
        ∀j:ℕ,j ≤ N → ‖iteratedFDeriv ℝ j
          (fun y => cutoffHighDegreeInput Ξ p qc y-cutoffComparisonInput Ξ qc y) x‖ ≤
          C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) := by
  obtain ⟨Cv,cv,hCv,hcv,hv⟩ := cutoffStepsDifference_low_order_exponential_bound Ξ hc B N
  obtain ⟨Ct,hCt,At,ct,hct,pt,hpt,ht⟩ :=
    cutoff_endpoint_error_exponential_bound Ξ hε hlo hLH hc hcQ N
  let C : ℝ := Cv+Ct
  let A : ℕ := max (N+1) At
  let c : ℝ := min cv ct
  let P : ℕ := max (N+2) pt
  refine ⟨C,by dsimp only [C];linarith,A,c,lt_min hcv hct,P,by dsimp only [P];omega,?_⟩
  intro p hp x hx hloc hm hlam hQ
  have hpv : N+2 ≤ p := (le_max_left _ _).trans hp
  have hpt' : pt ≤ p := (le_max_right _ _).trans hp
  obtain ⟨hW,hsm,hterm⟩ := ht p hpt' x.2.1 hm x.2.2.1 hlam x.2.2.2 hQ
  have hvsm : ContDiff ℝ ∞ (fun y : HighDegreeLowerParameter r =>
      cutoffStepsHighDegreeExtension Ξ p qc y-cutoffRecursionSteps Ξ y.1 y.2.1 qc) :=
    (contDiff_cutoffStepsHighDegreeExtension Ξ p qc).sub (contDiff_cutoffRecursionSteps_parameter Ξ qc)
  have he : (fun y : CutoffInputParameter r => cutoffHighDegreeInput Ξ p qc y-cutoffComparisonInput Ξ qc y)=
      (fun y => ((fun z : HighDegreeLowerParameter r => cutoffStepsHighDegreeExtension Ξ p qc z-
        cutoffRecursionSteps Ξ z.1 z.2.1 qc) (cutoffVarianceProjection y),
          cutoffEndpointError Ξ p qc ((ContinuousLinearMap.snd ℝ (AtomicPoint r) (ℝ×(ℝ×ℝ))) y))) := rfl
  have hfull : ContDiffAt ℝ ∞
      (fun y : CutoffInputParameter r => cutoffHighDegreeInput Ξ p qc y-cutoffComparisonInput Ξ qc y) x := by
    rw [he]
    exact (hvsm.contDiffAt.comp x cutoffVarianceProjection.contDiff.contDiffAt).prodMk
      (hsm.comp x (ContinuousLinearMap.snd ℝ (AtomicPoint r) (ℝ×(ℝ×ℝ))).contDiff.contDiffAt)
  refine ⟨hW,hfull,fun j hj => ?_⟩
  have hcast : (1:ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hcommon (D d : ℝ) (hD : 0 ≤ D) (hDC : D ≤ C) (hcd : c ≤ d)
      (k : ℕ) (hk : k ≤ A) :
      D*(p:ℝ)^k*Real.exp (-d*(p:ℝ)) ≤ C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) := by
    apply mul_le_mul (mul_le_mul hDC (pow_le_pow_right₀ hcast hk)
      (pow_nonneg (Nat.cast_nonneg _) _) (by dsimp only [C];linarith))
      (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hcd (Nat.cast_nonneg p)]))
      (Real.exp_pos _).le (by dsimp only [C];positivity)
  rw [he]
  apply norm_iteratedFDeriv_prod_le
    (hvsm.contDiffAt.comp x cutoffVarianceProjection.contDiff.contDiffAt)
    (hsm.comp x (ContinuousLinearMap.snd ℝ (AtomicPoint r) (ℝ×(ℝ×ℝ))).contDiff.contDiffAt) j
  · exact ((norm_iteratedFDeriv_comp_CLM_contraction cutoffVarianceProjection
      norm_cutoffVarianceProjection_le_one hvsm.contDiffAt j).trans
        (hv p hpv (cutoffVarianceProjection x) hx hloc j hj)).trans
          (hcommon Cv cv hCv (by dsimp only [C];linarith) (min_le_left _ _)
            (N+1) (le_max_left _ _))
  · exact ((norm_iteratedFDeriv_comp_CLM_contraction
      (ContinuousLinearMap.snd ℝ (AtomicPoint r) (ℝ×(ℝ×ℝ)))
      (ContinuousLinearMap.norm_snd_le ..) hsm j).trans (hterm j hj)).trans
        (hcommon Ct ct hCt.le (by dsimp only [C];linarith) (min_le_right _ _)
          At (le_max_right _ _))

end GeneralDepthPaper
