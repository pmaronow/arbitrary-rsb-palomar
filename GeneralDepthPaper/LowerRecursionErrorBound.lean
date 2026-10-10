module

public import GeneralDepthPaper.CutoffRecursionDifferenceBound
public import GeneralDepthPaper.LowerRemainderRegularity

@[expose] public section


/-! The actual scalar lower remainder of Lemma 4.2. Its finite recursion
and explicit covariance parts both have exponentially small genuine
Fréchet jets on the manuscript's compact parameter window. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff BigOperators
namespace GeneralDepthPaper
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 64

theorem degree_exp_envelope_le {C D c d : ℝ} {A k p : ℕ}
    (hD : 0≤D) (hDC : D≤C) (hcd : c≤d) (hk : k≤A) (hp : 1≤p) :
    D*(p:ℝ)^k*Real.exp (-d*(p:ℝ))≤C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) := by
  have hC : 0≤C := hD.trans hDC
  have hcast : (1:ℝ)≤p := by exact_mod_cast hp
  exact mul_le_mul (mul_le_mul hDC (pow_le_pow_right₀ hcast hk)
      (pow_nonneg (Nat.cast_nonneg _) _) hC)
    (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hcd (Nat.cast_nonneg p)]))
    (Real.exp_pos _).le (mul_nonneg hC (pow_nonneg (Nat.cast_nonneg _) _))

theorem contDiff_lowerCovariancePolynomial {r : ℕ} (p : ℕ) (qc : ℝ) :
    ContDiff ℝ ∞ (lowerCovariancePolynomial (r:=r) p qc) := by
  rw [lowerCovariancePolynomial_sum]
  exact (ContDiff.sum (fun i _ => (contDiff_lowerAtomAmplitude i).mul
    ((atomicLocationLowerCLM i).contDiff.pow p))).const_smul _ |>.sub
      (contDiff_lowerCutoffAmplitude.const_smul _)

theorem lowerCovariancePolynomial_low_order_exponential_bound {r : ℕ} {qc : ℝ}
    (hc : qc∈Ioo (0:ℝ) 1) (B : ℝ) (N : ℕ) :
    ∃C c:ℝ,0≤C ∧ 0<c ∧ ∀p:ℕ,1≤p→N≤p→
      ∀x:HighDegreeLowerParameter r,x∈closedBall 0 B→
      (∀i:Fin (r+1),atomicLocation x.1 i∈Icc (0:ℝ) qc)→∀j:ℕ,j≤N→
      ‖iteratedFDeriv ℝ j (lowerCovariancePolynomial p qc) x‖≤
        C*(p:ℝ)^(N+1)*Real.exp (-c*(p:ℝ)) := by
  classical
  have hh (j : Fin (N+1)) := lowerCovariancePolynomial_mixed_exponential_bound (r:=r) hc B j
  choose C c hC hc' hb using hh
  let D : ℝ := ∑j:Fin (N+1),C j
  let d : ℝ := Finset.univ.inf' Finset.univ_nonempty c
  have hD : 0≤D := Finset.sum_nonneg (fun j _=>hC j)
  have hd : 0<d := (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun j _=>hc' j)
  refine ⟨D,d,hD,hd,?_⟩
  intro p hp hNp x hx hloc j hj
  let i : Fin (N+1) := ⟨j,by omega⟩
  have hCi : C i≤D := Finset.single_le_sum (fun k _=>hC k) (Finset.mem_univ i)
  exact (hb i p hp (hj.trans hNp) x hx hloc).trans
    (degree_exp_envelope_le (hC i) hCi (Finset.inf'_le c (Finset.mem_univ i))
      (show j+1≤N+1 by omega) hp)

def lowerRecursionErrorRaw (Ξ : AdmissibleCovariance) {r : ℕ} (p : ℕ) (qc : ℝ)
    (x : CutoffInputParameter r) : ℝ :=
  terminalEvalCLM 0 (cutoffRecursionDifferenceRaw Ξ p qc x)+
    lowerCovariancePolynomial p qc (cutoffVarianceProjection x)

theorem lowerRecursionErrorRaw_eq_extension (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (hp : 4≤p) (he : Even p) (hn : p∉Ξ.degrees)
    (x : CutoffInputParameter r) (hlam : 0<x.2.2.1) (qc : ℝ) :
    lowerRecursionErrorRaw Ξ p qc x=lowerRecursionRemainderExtension Ξ
      (Ξ.addHighDegree p hp he hn x.2.2.1 hlam) x.1 x.2.1 x.2.2.2 qc := by
  have hs : cutoffStepsHighDegreeExtension Ξ p qc (cutoffVarianceProjection x)=
      cutoffRecursionSteps (Ξ.addHighDegree p hp he hn x.2.2.1 hlam) x.1 x.2.1 qc :=
    cutoffStepsHighDegreeExtension_eq Ξ p hp he hn (cutoffVarianceProjection x) hlam qc
  have hv := endpointVariance_eq_expression Ξ p hp he hn x.2.2.1 hlam qc x.2.2.2
  have hr : lowerCovarianceRemainder Ξ (Ξ.addHighDegree p hp he hn x.2.2.1 hlam) x.1 x.2.1 qc=
      lowerCovariancePolynomial p qc (cutoffVarianceProjection x) :=
    lowerCovariancePolynomial_eq Ξ p hp he hn x.1 x.2.1 qc x.2.2.1 hlam
  unfold lowerRecursionErrorRaw cutoffRecursionDifferenceRaw
  rw [map_sub]
  simp only [cutoffHighDegreeInput,cutoffComparisonInput]
  rw [hs,←hv]
  rw [←hr]
  rfl

theorem norm_terminalEvalCLM_zero_le_one : ‖terminalEvalCLM 0‖≤1 := by
  apply (terminalEvalCLM 0).opNorm_le_bound zero_le_one
  intro g
  simp only [terminalEvalCLM_apply,terminalValue_zero,one_mul]
  exact norm_fst_le g.1

theorem lower_recursion_error_exponential_bound (Ξ : AdmissibleCovariance) {r : ℕ}
    {K : Set (AtomicPoint r)} (hK : IsCompact K) (hvalid : ∀z∈K,IsAtomicPoint z)
    {ε lamlo lamhi qc cQ CQ : ℝ} (hε : 0<ε) (hlo : 0<lamlo)
    (hLH : lamlo≤lamhi) (hc : qc∈Ioo (0:ℝ) 1)
    (hcut : ∀z∈K,atomicLocation z (Fin.last r)<qc) (hcQ : 0<cQ) (N : ℕ) :
    ∃C:ℝ,0<C ∧ ∃A:ℕ,∃c:ℝ,0<c ∧ ∃p0:ℕ,1≤p0 ∧
      ∀p:ℕ,p0≤p→∀x:CutoffInputParameter r,x.1∈K→
        x.2.1∈Icc ε 1→x.2.2.1∈Icc lamlo lamhi→x.2.2.2∈endpointStrip cQ CQ p→
        ContDiffAt ℝ ∞ (lowerRecursionErrorRaw Ξ p qc) x ∧
        ∀j:ℕ,j≤N→‖iteratedFDeriv ℝ j (lowerRecursionErrorRaw Ξ p qc) x‖≤
          C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) := by
  obtain ⟨C1,hC1,A1,c1,hc1,p1,hp1,h1⟩ :=
    cutoff_recursion_difference_exponential_bound Ξ hK hvalid hε hlo hLH hc hcut hcQ N
  obtain ⟨B,hB⟩ := (isCompact_cutoffParameterWindow hK ε lamlo lamhi).exists_bound_of_continuousOn
    cutoffVarianceProjection.continuous.continuousOn
  obtain ⟨C2,c2,hC2,hc2,h2⟩ := lowerCovariancePolynomial_low_order_exponential_bound (r:=r) hc B N
  let C : ℝ := C1+C2
  let A : ℕ := max A1 (N+1)
  let c : ℝ := min c1 c2
  refine ⟨C,by dsimp only [C];linarith,A,c,lt_min hc1 hc2,max p1 N,
    hp1.trans (le_max_left _ _),?_⟩
  intro p hp x hx hm hlam hQ
  obtain ⟨hr,hrj⟩ := h1 p ((le_max_left _ _).trans hp) x hx hm hlam hQ
  have hw : x∈cutoffParameterWindow K ε lamlo lamhi :=
    ⟨hx,hm,hlam,(endpointStrip_mem_unit hcQ p hQ).1,(endpointStrip_mem_unit hcQ p hQ).2.le⟩
  have hcore : cutoffVarianceProjection x∈closedBall 0 B := by
    simpa only [mem_closedBall,dist_zero_right] using hB x hw
  have hloc : ∀i:Fin (r+1),atomicLocation x.1 i∈Icc (0:ℝ) qc := fun i =>
    ⟨(atomicLocation_mem_unit (hvalid _ hx) i).1,
      ((hvalid _ hx).1.monotone (Fin.le_last i)).trans (hcut _ hx).le⟩
  have hg : ContDiffAt ℝ ∞ (fun y : CutoffInputParameter r =>
      lowerCovariancePolynomial p qc (cutoffVarianceProjection y)) x :=
    (contDiff_lowerCovariancePolynomial p qc).contDiffAt.comp x
      cutoffVarianceProjection.contDiff.contDiffAt
  have hv : ContDiffAt ℝ ∞ (fun y=>terminalEvalCLM 0 (cutoffRecursionDifferenceRaw Ξ p qc y)) x :=
    (terminalEvalCLM 0).contDiff.contDiffAt.comp x hr
  refine ⟨hv.add hg,fun j hj=>?_⟩
  have hp0 : 1≤p := hp1.trans ((le_max_left _ _).trans hp)
  have hval := ((terminalEvalCLM 0).norm_iteratedFDeriv_comp_left hr
    (show (j:ℕ∞ω)≤∞ by simp)).trans
      ((mul_le_mul_of_nonneg_right norm_terminalEvalCLM_zero_le_one (norm_nonneg _)).trans
        (by simpa only [one_mul] using hrj j hj))
  have hpol := (norm_iteratedFDeriv_comp_CLM_contraction cutoffVarianceProjection
    norm_cutoffVarianceProjection_le_one (contDiff_lowerCovariancePolynomial p qc).contDiffAt j).trans
      (h2 p hp0 ((le_max_right _ _).trans hp) (cutoffVarianceProjection x) hcore hloc j hj)
  have hval' := hval.trans (degree_exp_envelope_le hC1.le le_rfl
    (min_le_left c1 c2) (le_max_left A1 (N+1)) hp0)
  have hpol' := hpol.trans (degree_exp_envelope_le hC2 le_rfl
    (min_le_right c1 c2) (le_max_right A1 (N+1)) hp0)
  change ‖iteratedFDeriv ℝ j (fun y=>terminalEvalCLM 0 (cutoffRecursionDifferenceRaw Ξ p qc y)+
    lowerCovariancePolynomial p qc (cutoffVarianceProjection y)) x‖≤_
  rw [fun_iteratedFDeriv_add_apply (hv.of_le (by simp)) (hg.of_le (by simp))]
  exact (norm_add_le _ _).trans ((add_le_add hval' hpol').trans_eq (by
    dsimp only [C,A,c]
    ring))

end GeneralDepthPaper
