module

public import GeneralDepthPaper.LimitingCutoffGeometry
public import GeneralDepthPaper.HighDegreeOriginBound

@[expose] public section


/-! The genuine sequential contact transfer for Lemma 4.9. All moment
convergence is derived from the actual high-degree cutoff data; the only
stationarity inputs are the exact contacts subsequently supplied by 4.6. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 64
namespace LimitingStandingData
variable {Ξ : AdmissibleCovariance} {r : ℕ} {seed : AtomicPoint r}

theorem lower_geometry_sequence (d : LimitingStandingData Ξ seed)
    {gamma : ℝ} (hg : 0<gamma)
    (hmargin : ∀m:d.MassInterval,d.limitingVariation m d.cutoff≤ -4*gamma)
    (p : ℕ→ℕ) (hp : ∀n,4≤p n) (he : ∀n,Even (p n))
    (hn : ∀n,p n∉Ξ.degrees) (hpt : Tendsto p atTop atTop)
    (m lam : ℕ→ℝ) (hm : ∀n,m n∈Icc d.massLower 1)
    (hl : ∀n,lam n∈Icc d.couplingLower d.couplingUpper)
    (Q : ℕ→Overlap) (hQ : ∀n,(Q n:ℝ)∈endpointStrip d.stripRateLower d.stripRateUpper (p n))
    (hqcQ : ∀n,d.cutoff≤(Q n:ℝ))
    (z : ℕ→AtomicPoint r) (hz : ∀n,IsAtomicPoint (z n))
    (hzc : ∀n,atomicLocation (z n) (Fin.last r)<d.cutoff)
    (m0 : d.MassInterval) (hzt : Tendsto z atTop (𝓝 (d.branch m0)))
    (hmt : Tendsto m atTop (𝓝 (m0:ℝ)))
    (hcontact : ∀n:ℕ,∀i:Fin r,
      firstVariation (Ξ.addHighDegree (p n) (hp n) (he n) (hn n) (lam n)
        (d.couplingLower_pos.trans_le (hl n).1))
        (twoLevelMeasure (z n) (hz n) (m n) (Q n)) ((z n).1 i)=0)
    (hcritical : ∀n:ℕ,∀i:Fin r,
      deriv (firstVariation (Ξ.addHighDegree (p n) (hp n) (he n) (hn n) (lam n)
        (d.couplingLower_pos.trans_le (hl n).1))
        (twoLevelMeasure (z n) (hz n) (m n) (Q n))) ((z n).1 i)=0) :
    ∀ᶠn in atTop,
      let X:=Ξ.addHighDegree (p n) (hp n) (he n) (hn n) (lam n)
        (d.couplingLower_pos.trans_le (hl n).1)
      let f:=firstVariation X (twoLevelMeasure (z n) (hz n) (m n) (Q n))
      (∀q∈Icc (0:ℝ) d.cutoff,f q≤0) ∧
      (∀q∈Icc (0:ℝ) d.cutoff,f q=0↔q=0∨∃i:Fin r,q=(z n).1 i) ∧
      (∀i:Fin r,closedJet d.cutoff 2 f ((z n).1 i)<0) ∧ f d.cutoff≤ -3*gamma := by
  let X n:=Ξ.addHighDegree (p n) (hp n) (he n) (hn n) (lam n)
    (d.couplingLower_pos.trans_le (hl n).1)
  let f n:=firstVariation (X n) (twoLevelMeasure (z n) (hz n) (m n) (Q n))
  let dn n:=cutoffCandidateData (X n) (z n) (hz n) (m n)
    ⟨d.massLower_mem.1.le.trans (hm n).1,(hm n).2⟩ (Q n) d.cutoff (hzc n) (hqcQ n)
  have hzc0:atomicLocation (d.branch m0) (Fin.last r)<d.cutoff:=by
    apply d.ball_below_cutoff
    rw [mem_closedBall]
    exact (d.branch_close m0 m0.property).le.trans (by linarith [d.radius_pos])
  have hd : TruncatedDataConvergence dn (d.cutoffLimitData m0):=
    cutoffCandidateData_highDegree_convergence Ξ d.massLower_mem.1 d.couplingLower_pos
      d.couplingLower_le_upper d.cutoff_mem d.strip_rates.1 p hp he hn hpt m lam hm hl Q hQ hqcQ
      z hz hzc (d.branch m0) (d.branch_nondegenerate m0 m0.property).choose hzc0
      m0.property hzt hmt
  have heq : ∀n,EqOn (f n) (dn n).firstVariation (Icc (0:ℝ) d.cutoff):=by
    intro n q hq
    exact firstVariation_twoLevelMeasure_eq_cutoff (X n) (z n) (hz n) (m n)
      ⟨d.massLower_mem.1.le.trans (hm n).1,(hm n).2⟩ (Q n) d.cutoff (hzc n) (hqcQ n)
      q hq
  let F:ℝ→ℝ:=(d.cutoffLimitData m0).firstVariation
  have hconv:=closedVariationJets_uniform_convergence dn (d.cutoffLimitData m0) hd f F heq
    (fun _ _=>rfl)
  have hgeom:=d.limiting_cutoff_geometry m0
  have hC:0<highDegreeOriginBound Ξ d.couplingUpper:=
    highDegreeOriginBound_pos Ξ (d.couplingLower_pos.le.trans d.couplingLower_le_upper)
  have ha : Ξ.second 0 < 1 := d.isSubcritical
  have horigin : ∀n,∀q∈Ioc (0:ℝ) (originRadius (Ξ.second 0) (highDegreeOriginBound Ξ d.couplingUpper)),
      f n q<0:=by
    intro n q hq
    exact firstVariation_neg_near_origin (X n) _
      (by dsimp only [X]; rw [AdmissibleCovariance.addHighDegree_second_zero]) ha
      (highDegree_first_half_le Ξ (p n) (hp n) (he n) (hn n) (lam n)
        (d.couplingLower_pos.trans_le (hl n).1) (hl n).2) hq
  have hcore:=contact_perturbation_closed_C2 F f (d.branch m0).1 (fun n=>(z n).1)
    d.cutoff_mem.1 d.cutoff_mem.2.le (originRadius_pos ha hC)
    (d.cutoffLimitData m0).contDiffOn_firstVariation
    (fun n=>(contDiffOn_firstVariation_two (X n) _).mono
      (Icc_subset_Icc_right d.cutoff_mem.2.le))
    hgeom.1 hgeom.2.1 hgeom.2.2.1 hgeom.2.2.2 hconv
    (fun i=>((continuous_apply i).comp continuous_fst).continuousAt.tendsto.comp hzt)
    (fun n=>firstVariation_zero (X n) _) horigin hcontact hcritical
  have hcut : Tendsto (fun n=>f n d.cutoff) atTop (𝓝 (F d.cutoff)) := by
    have H:=(hconv 0 (by omega)).tendsto_at
      (show d.cutoff∈Icc (0:ℝ) d.cutoff from ⟨d.cutoff_mem.1.le,le_rfl⟩)
    simpa only [closedJet,Function.iterate_zero_apply] using H
  have hFc : F d.cutoff≤ -4*gamma:=by
    dsimp only [F]
    rw [d.cutoffLimitData_firstVariation m0 ⟨d.cutoff_mem.1.le,le_rfl⟩]
    exact hmargin m0
  have htail : ∀ᶠn in atTop,f n d.cutoff≤ -3*gamma :=
    (hcut.eventually (eventually_lt_nhds (show F d.cutoff < -3*gamma by linarith))).mono
      (fun _ hh=>hh.le)
  filter_upwards [hcore,htail] with n hcore htail
  exact ⟨hcore.1,hcore.2.1,hcore.2.2,htail⟩

end LimitingStandingData
end GeneralDepthPaper
