module

public import GeneralDepthPaper.AtomicContactStability
public import GeneralDepthPaper.RevisedNondegeneracyBridge

@[expose] public section

/-! The revised manuscript's Lemma 2.7 for genuinely arbitrary sequences of
finite positive even covariances. The exponent sets need not be fixed. C³
convergence is convergence of the actual four compatible covariance jets on
the compact overlap interval; the output is uniform convergence of the
actual first variation and its first two closed-interval derivatives. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 64

theorem atomicTruncatedData_convergence_of_covariance_C3
    (Ξn : ℕ → AdmissibleCovariance) (Ξ : AdmissibleCovariance) {r : ℕ}
    (zn : ℕ → AtomicPoint r) (hzN : ∀ n, IsAtomicPoint (zn n))
    (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (hΞ : ∀ j : Fin 4, Tendsto (fun n => covarianceJetMap (Ξn n) j) atTop
      (𝓝 (covarianceJetMap Ξ j)))
    (hzlim : Tendsto zn atTop (𝓝 z)) :
    TruncatedDataConvergence (fun n => atomicTruncatedData (Ξn n) (zn n) (hzN n))
      (atomicTruncatedData Ξ z hz) := by
  constructor
  · exact hΞ
  · apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_subtype_rng.mpr
    exact (contDiff_atomicNode i).continuous.continuousAt.tendsto.comp hzlim
  · apply tendsto_pi_nhds.mpr
    intro i
    exact (contDiff_atomicLevel i).continuous.continuousAt.tendsto.comp hzlim
  · intro j
    exact tendsto_const_nhds

theorem first_variation_C2_of_covariance_C3
    (Ξn : ℕ → AdmissibleCovariance) (Ξ : AdmissibleCovariance) {r : ℕ}
    (zn : ℕ → AtomicPoint r) (hzN : ∀ n, IsAtomicPoint (zn n))
    (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (hΞ : ∀ j : Fin 4, Tendsto (fun n => covarianceJetMap (Ξn n) j) atTop
      (𝓝 (covarianceJetMap Ξ j)))
    (hzlim : Tendsto zn atTop (𝓝 z)) :
    ∀ j ≤ 2, TendstoUniformlyOn
      (fun n => closedJet 1 j (firstVariation (Ξn n) (atomicMeasure (zn n) (hzN n))))
      (closedJet 1 j (firstVariation Ξ (atomicMeasure z hz))) atTop (Icc (0 : ℝ) 1) := by
  have hc := atomicTruncatedData_convergence_of_covariance_C3 Ξn Ξ zn hzN z hz hΞ hzlim
  have ht := hc.firstVariation_C2
  intro j hj
  let jj : Fin 3 := ⟨j, by omega⟩
  have hJ := (tendsto_pi_nhds.mp ht) jj
  have hn : Tendsto (fun n =>
      ‖(atomicTruncatedData (Ξn n) (zn n) (hzN n)).firstVariationJets jj -
        (atomicTruncatedData Ξ z hz).firstVariationJets jj‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      (hJ.sub (tendsto_const_nhds
        (x := (atomicTruncatedData Ξ z hz).firstVariationJets jj))).norm
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hn.eventually (eventually_lt_nhds hε)] with n hne
  intro q hq
  rw [Real.dist_eq, ← Real.norm_eq_abs]
  rw [show j = (jj : ℕ) from rfl,
    closedJet_firstVariation_atomicMeasure _ (zn n) (hzN n) jj q hq,
    closedJet_firstVariation_atomicMeasure _ z hz jj q hq]
  rw [norm_sub_rev]
  exact (ContinuousMap.norm_coe_le_norm
    ((atomicTruncatedData (Ξn n) (zn n) (hzN n)).firstVariationJets jj -
      (atomicTruncatedData Ξ z hz).firstVariationJets jj) ⟨q, hq⟩).trans_lt hne

private theorem stationary_contact_geometry_covariance_C3_uniform
    (Ξn : ℕ → AdmissibleCovariance) (Ξ : AdmissibleCovariance) {r : ℕ}
    (zn : ℕ → AtomicPoint r) (hzN : ∀ n, IsAtomicPoint (zn n))
    (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (hbase : AtomicContactGeometry Ξ z hz)
    (a : ℝ) (ha : a < 1) (haN : ∀ n, (Ξn n).second 0 ≤ a)
    (hΞ : ∀ j : Fin 4, Tendsto (fun n => covarianceJetMap (Ξn n) j) atTop
      (𝓝 (covarianceJetMap Ξ j)))
    (hzlim : Tendsto zn atTop (𝓝 z))
    (hstationary : ∀ n, fderiv ℝ (atomicFunctionalExtension (Ξn n) r) (zn n) = 0) :
    ∀ᶠ n in atTop, AtomicContactGeometry (Ξn n) (zn n) (hzN n) := by
  have hfirst : Tendsto (fun n => (Ξn n).first (1 / 2)) atTop (𝓝 (Ξ.first (1 / 2))) := by
    have he := (continuous_eval_const (⟨1 / 2, by norm_num⟩ :
      TruncatedClockDomain 1)).continuousAt.tendsto.comp (hΞ 1)
    simpa only [Function.comp_def, covarianceJetMap_one] using he
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ hfirst).exists_norm_le
  have hC' (n : ℕ) : (Ξn n).first (1 / 2) ≤ C := (le_abs_self _).trans (hC _ ⟨n, rfl⟩)
  have hCp : 0 < C := ((Ξn 0).first_pos (by norm_num)).trans_le (hC' 0)
  have hcontacts (n : ℕ) := atomic_stationary_contacts _ (zn n) (hzN n) (hstationary n)
  have hpos (i : Fin r) : z.1 i ∈ Ioo (0 : ℝ) 1 :=
    ⟨by simpa only [atomicLocation_zero, atomicLocation_succ] using hz.1 (Fin.succ_pos i),
      (hz.1.monotone (Fin.le_last i.succ)).trans_lt hz.2.1⟩
  have hzero : ∀ q ∈ Icc (0 : ℝ) 1, firstVariation Ξ (atomicMeasure z hz) q = 0 ↔
      q = 0 ∨ ∃ i : Fin r, z.1 i = q := by
    intro q hq
    rw [(hbase.1 q hq).2]
    constructor
    · rintro ⟨i, hi⟩
      cases i using Fin.cases with
      | zero => exact Or.inl hi
      | succ j => exact Or.inr ⟨j, hi.symm⟩
    · rintro (rfl | ⟨i, hi⟩)
      · exact ⟨0, rfl⟩
      · exact ⟨i.succ, hi.symm⟩
  have hn := contact_perturbation_closed_C2
    (firstVariation Ξ (atomicMeasure z hz))
    (fun n => firstVariation (Ξn n) (atomicMeasure (zn n) (hzN n)))
    z.1 (fun n => (zn n).1) (by norm_num) le_rfl (originRadius_pos ha hCp)
    (contDiffOn_firstVariation_atomicMeasure Ξ z hz)
    (fun n => contDiffOn_firstVariation_atomicMeasure _ (zn n) (hzN n))
    (fun q hq => (hbase.1 q hq).1) hzero hpos hbase.2
    (first_variation_C2_of_covariance_C3 Ξn Ξ zn hzN z hz hΞ hzlim)
    (fun i => ((continuous_apply i).comp continuous_fst).continuousAt.tendsto.comp hzlim)
    (fun n => firstVariation_zero _ _)
    (fun n q hq => firstVariation_neg_near_origin _ _ (haN n) ha (hC' n) hq)
    (fun n i => by simpa only [atomicLocation_succ] using (hcontacts n).1 i.succ)
    (fun n i => (hcontacts n).2 i)
  filter_upwards [hn] with n hn
  refine ⟨?_, hn.2.2⟩
  intro q hq
  refine ⟨hn.1 q hq, ?_⟩
  rw [hn.2.1 q hq]
  constructor
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨i.succ, rfl⟩
  · rintro ⟨i, rfl⟩
    cases i using Fin.cases with
    | zero => exact Or.inl rfl
    | succ j => exact Or.inr ⟨j, rfl⟩

/-- Literal Lemma 2.7. Every covariance in the sequence may have its own
finite even exponent set, including degree two. Nondegeneracy is the paper
predicate, and stationarity is the actual Fréchet derivative equation. -/
theorem revised_lemma_2_7
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
    (PaperNondegenerate Ξ z hz →
      (∀ n, fderiv ℝ (atomicFunctionalExtension (Ξn n) r) (zn n) = 0) →
      ∀ᶠ n in atTop,
        PaperNondegenerate (Ξn n) (zn n) (hzN n) ∧
        atomicMeasure (zn n) (hzN n) = parisiMinimizer (Ξn n) ∧
        IsFiniteRSB r (parisiMinimizer (Ξn n))) := by
  refine ⟨first_variation_C2_of_covariance_C3 Ξn Ξ zn hzN z hz hΞ hzlim, ?_⟩
  intro hND hstationary
  let a : ℝ := (Ξ.second 0 + 1) / 2
  have ha : a < 1 := by dsimp only [a]; change Ξ.second 0 < 1 at hsub; linarith
  have hsa : Ξ.second 0 < a := by dsimp only [a]; change Ξ.second 0 < 1 at hsub; linarith
  have ht : Tendsto (fun n => (Ξn n).second 0) atTop (𝓝 (Ξ.second 0)) := by
    have he := (continuous_eval_const (⟨0, by norm_num⟩ :
      TruncatedClockDomain 1)).continuousAt.tendsto.comp (hΞ 2)
    simpa only [Function.comp_def, covarianceJetMap_two] using he
  have he : ∀ᶠ n in atTop, (Ξn n).second 0 ≤ a :=
    (ht.eventually (eventually_lt_nhds hsa)).mono (fun _ h => h.le)
  obtain ⟨N, hN⟩ := he.exists_forall_of_atTop
  have hc := stationary_contact_geometry_covariance_C3_uniform
    (fun n => Ξn (n + N)) Ξ (fun n => zn (n + N)) (fun n => hzN (n + N))
    z hz ⟨hND.2.1, hND.2.2⟩ a ha (fun n => hN (n + N) (by omega))
    (fun j => (hΞ j).comp (tendsto_add_atTop_nat N))
    (hzlim.comp (tendsto_add_atTop_nat N)) (fun n => hstationary (n + N))
  have hm : ∀ᶠ n in Filter.map (fun n : ℕ => n + N) atTop,
      AtomicContactGeometry (Ξn n) (zn n) (hzN n) := Filter.eventually_map.mpr hc
  rw [Filter.map_add_atTop_eq_nat N] at hm
  filter_upwards [hm] with n hn
  have hmin := hn.isMinimizer
  have heq : atomicMeasure (zn n) (hzN n) = parisiMinimizer (Ξn n) :=
    parisiMinimizer_unique _ _ hmin
  refine ⟨⟨hmin, hn.1, hn.2⟩, heq, ?_⟩
  rw [← heq]
  exact atomicMeasure_isFiniteRSB (zn n) (hzN n)

end GeneralDepthPaper
