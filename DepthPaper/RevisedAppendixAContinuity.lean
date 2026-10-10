module

public import DepthPaper.CutoffClosedVariationJets

@[expose] public section

/-! Exact closed-interval observable convergence and eventual contact
persistence for Appendix A.3 and A.4. Terminal constants do not enter the
hypotheses. Zero and coincident mass levels are permitted. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 1000000

/-- Lemma A.3: convergence of both actual diffusion moments and all intrinsic
closed-interval derivatives of the actual first variation through order two. -/
theorem revised_observable_continuity {r : ℕ} {qc : ℝ}
    (d : ℕ → TruncatedParisiData r qc) (d0 : TruncatedParisiData r qc)
    (h : TruncatedDataConvergence d d0) :
    TendstoUniformlyOn (fun n => (d n).Gamma) d0.Gamma atTop (Icc (0:ℝ) qc) ∧
    TendstoUniformlyOn (fun n => (d n).Gamma2) d0.Gamma2 atTop (Icc (0:ℝ) qc) ∧
    (∀ j ≤ 2, TendstoUniformlyOn (fun n => closedJet qc j (d n).firstVariation)
      (closedJet qc j d0.firstVariation) atTop (Icc (0:ℝ) qc)) ∧
    ContDiffOn ℝ 2 d0.firstVariation (Icc (0:ℝ) qc) ∧
    (∀ n, ContDiffOn ℝ 2 (d n).firstVariation (Icc (0:ℝ) qc)) := by
  exact ⟨h.Gamma, h.Gamma2,
    closedVariationJets_uniform_convergence d d0 h (fun n => (d n).firstVariation)
      d0.firstVariation (fun _ _ _ => rfl) (fun _ _ => rfl),
    d0.contDiffOn_firstVariation, fun n => (d n).contDiffOn_firstVariation⟩

/-- A strict origin sign follows from the paper's relative moment margin
and strict positivity of the covariance rate away from zero. -/
theorem revised_truncated_origin_negative {r : ℕ} {qc ε : ℝ}
    (d : TruncatedParisiData r qc) (hε : 0 < ε) (hεc : ε ≤ qc)
    (hcov : ∀ q ∈ Ioc (0:ℝ) qc, 0 < d.covarianceField 2 q)
    (hmargin : ∀ q ∈ Icc (0:ℝ) ε, d.Gamma q ≤ (1-ε)*q)
    {q : ℝ} (hq : q ∈ Ioc (0:ℝ) ε) : d.firstVariation q < 0 := by
  have hm : StrictAntiOn d.firstVariation (Icc (0:ℝ) ε) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (continuous_iff_continuousAt.mpr (fun q =>
        (d.hasDerivAt_firstVariation q).continuousAt)).continuousOn
    intro s hs
    rw [interior_Icc] at hs
    rw [(d.hasDerivAt_firstVariation s).deriv]
    change (1/2:ℝ)*d.covarianceField 2 s*(d.Gamma s-s) < 0
    have hb := hmargin s ⟨hs.1.le, hs.2.le⟩
    exact mul_neg_of_pos_of_neg (mul_pos (by norm_num)
      (hcov s ⟨hs.1, hs.2.le.trans hεc⟩)) (by have hp := mul_pos hε hs.1; nlinarith)
  have he : d.firstVariation 0 = 0 := by
    simp [TruncatedParisiData.firstVariation]
  simpa only [he] using hm ⟨le_rfl,hε.le⟩ ⟨hq.1.le,hq.2⟩ hq.1

/-- Lemma A.4. The origin margin and the two contact equations need hold
only eventually. The conclusion concerns the exact moving contacts and
actual second derivative, including the closed interval's intrinsic jets. -/
theorem revised_contact_persistence {r : ℕ} {qc : ℝ}
    (d : ℕ → TruncatedParisiData r qc) (d0 : TruncatedParisiData r qc)
    (hqc : qc ≤ 1) (h : TruncatedDataConvergence d d0)
    (hcov : ∀ n q, q ∈ Ioc (0:ℝ) qc → 0 < (d n).covarianceField 2 q)
    (hFle : ∀ q ∈ Icc (0:ℝ) qc, d0.firstVariation q ≤ 0)
    (hFzero : ∀ q ∈ Icc (0:ℝ) qc, d0.firstVariation q = 0 ↔
      q = 0 ∨ ∃ i : Fin r, (d0.node i.castSucc.succ : ℝ) = q)
    (hFneg : ∀ i : Fin r, d0.firstVariationSecond (d0.node i.castSucc.succ) < 0)
    (horigin : ∃ ε > 0, ∀ᶠ n in atTop, ∀ q ∈ Icc (0:ℝ) ε,
      (d n).Gamma q ≤ (1-ε)*q)
    (hcontact : ∀ᶠ n in atTop, ∀ i : Fin r,
      (d n).firstVariation ((d n).node i.castSucc.succ) = 0 ∧
      (d n).firstVariationPrime ((d n).node i.castSucc.succ) = 0) :
    ∀ᶠ n in atTop,
      (∀ q ∈ Icc (0:ℝ) qc, (d n).firstVariation q ≤ 0) ∧
      (∀ q ∈ Icc (0:ℝ) qc, (d n).firstVariation q = 0 ↔
        q = 0 ∨ ∃ i : Fin r, q = ((d n).node i.castSucc.succ : ℝ)) ∧
      (∀ i : Fin r, (d n).firstVariationSecond ((d n).node i.castSucc.succ) < 0) := by
  obtain ⟨ε,hε,hmargin⟩ := horigin
  obtain ⟨N,hN⟩ := (hmargin.and hcontact).exists_forall_of_atTop
  let δ := min ε qc
  have hδ : 0 < δ := lt_min hε d0.qc_pos
  have hδc : δ ≤ qc := min_le_right _ _
  have hδe : δ ≤ ε := min_le_left _ _
  let dn n := d (n+N)
  have hd : TruncatedDataConvergence dn d0 :=
    ⟨fun j => (h.covariance j).comp (tendsto_add_atTop_nat N),
      h.node.comp (tendsto_add_atTop_nat N),
      h.level.comp (tendsto_add_atTop_nat N),
      fun j => (h.terminal j).comp (tendsto_add_atTop_nat N)⟩
  have hpos (i : Fin r) : (d0.node i.castSucc.succ : ℝ) ∈ Ioo (0:ℝ) qc := by
    constructor
    · have ht : (d0.node 0 : ℝ) < (d0.node i.castSucc.succ : ℝ) :=
        d0.node_strictMono (Fin.succ_pos i.castSucc)
      simpa only [d0.node_zero] using ht
    · have ht : (d0.node i.castSucc.succ : ℝ) < (d0.node (Fin.last (r+1)) : ℝ) :=
        d0.node_strictMono (show i.castSucc.succ < Fin.last (r+1) by
        exact Fin.succ_lt_succ_iff.mpr (Fin.castSucc_lt_last i))
      simpa only [d0.node_last] using ht
  have hneg (i : Fin r) : closedJet qc 2 d0.firstVariation (d0.node i.castSucc.succ) < 0 := by
    have he := closedJet_eq_truncatedVariationJets d0 d0.firstVariation (fun _ _ => rfl)
      (2:Fin 3) _ (d0.node i.castSucc.succ).property
    norm_num [TruncatedParisiData.firstVariationJets] at he
    rw [he]
    exact hFneg i
  have hcore := contact_perturbation_closed_C2 d0.firstVariation
    (fun n => (dn n).firstVariation) (fun i : Fin r => (d0.node i.castSucc.succ : ℝ))
    (fun (n : ℕ) (i : Fin r) => ((dn n).node i.castSucc.succ : ℝ)) d0.qc_pos hqc hδ
    d0.contDiffOn_firstVariation (fun n => (dn n).contDiffOn_firstVariation)
    hFle hFzero hpos hneg
    (closedVariationJets_uniform_convergence dn d0 hd (fun n => (dn n).firstVariation)
      d0.firstVariation (fun _ _ _ => rfl) (fun _ _ => rfl))
    (fun i => by
      have hc : Continuous (fun f : Fin (r+2) → TruncatedClockDomain qc =>
          (f i.castSucc.succ : ℝ)) := continuous_subtype_val.comp (continuous_apply _)
      simpa only [Function.comp_def] using hc.continuousAt.tendsto.comp hd.node)
    (fun n => by simp [TruncatedParisiData.firstVariation])
    (fun n q hq => revised_truncated_origin_negative (dn n) hδ hδc
      (hcov (n+N)) (fun s hs => by
        have hm := (hN (n+N) (by omega)).1 s ⟨hs.1,hs.2.trans hδe⟩
        have hs0 := hs.1
        have hde := hδe
        nlinarith) hq)
    (fun n i => (hN (n+N) (by omega)).2 i |>.1)
    (fun n i => by
      rw [((dn n).hasDerivAt_firstVariation _).deriv]
      exact (hN (n+N) (by omega)).2 i |>.2)
  have hout : ∀ᶠ n in atTop,
      (∀ q ∈ Icc (0:ℝ) qc, (dn n).firstVariation q ≤ 0) ∧
      (∀ q ∈ Icc (0:ℝ) qc, (dn n).firstVariation q = 0 ↔
        q = 0 ∨ ∃ i : Fin r, q = ((dn n).node i.castSucc.succ : ℝ)) ∧
      (∀ i : Fin r, (dn n).firstVariationSecond ((dn n).node i.castSucc.succ) < 0) := by
    filter_upwards [hcore] with n hn
    refine ⟨hn.1,hn.2.1,?_⟩
    intro i
    have he := closedJet_eq_truncatedVariationJets (dn n) (dn n).firstVariation
      (fun _ _ => rfl) (2:Fin 3) _ ((dn n).node i.castSucc.succ).property
    norm_num [TruncatedParisiData.firstVariationJets] at he
    have hi := hn.2.2 i
    rwa [he] at hi
  have hm : ∀ᶠ n in Filter.map (fun n : ℕ => n+N) atTop,
      (∀ q ∈ Icc (0:ℝ) qc, (d n).firstVariation q ≤ 0) ∧
      (∀ q ∈ Icc (0:ℝ) qc, (d n).firstVariation q = 0 ↔
        q = 0 ∨ ∃ i : Fin r, q = ((d n).node i.castSucc.succ : ℝ)) ∧
      (∀ i : Fin r, (d n).firstVariationSecond ((d n).node i.castSucc.succ) < 0) :=
    Filter.eventually_map.mpr hout
  rwa [Filter.map_add_atTop_eq_nat N] at hm

end DepthPaper
