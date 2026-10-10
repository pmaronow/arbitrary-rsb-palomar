module

public import GeneralDepthPaper.StationaryBranchProposition
public import GeneralDepthPaper.CutoffClosedVariationJets

@[expose] public section


/-! The actual lower stationary configurations converge along every
convergent physical parameter sequence, and the ψ-cutoff limit retains
the precise nondegenerate contact geometry of the temperature model. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 64
namespace LimitingStandingData
variable {Ξ : AdmissibleCovariance} {r : ℕ} {seed : AtomicPoint r}

theorem stationaryBranch_sequence_converges (d : LimitingStandingData Ξ seed)
    (p : ℕ→ℕ) (he : ∀n,Even (p n)) (hpt : Tendsto p atTop atTop)
    (theta : ℕ→ℝ×ℝ) (ht : ∀n,theta n∈d.parameterWindow)
    (theta0 : ℝ×ℝ) (ht0 : theta0∈d.parameterWindow)
    (htt : Tendsto theta atTop (𝓝 theta0)) :
    Tendsto (fun n=>d.stationaryBranch (p n) (theta n)) atTop
      (𝓝 (d.branch theta0.2)) := by
  obtain ⟨C,hC,A,c,hc,H⟩:=d.stationaryBranch_eventually
  have hb : ∀ᶠn in atTop,
      ‖d.stationaryBranch (p n) (theta n)-d.branch (theta n).2‖≤
        C*(p n:ℝ)^A*Real.exp (-c*(p n:ℝ)) :=
    (hpt.eventually H).mono (fun n hn=>(hn (he n) (theta n) (ht n)).2.2.2.1)
  have hzero : Tendsto (fun n=>d.stationaryBranch (p n) (theta n)-d.branch (theta n).2)
      atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (.of_forall fun n=>norm_nonneg _) hb
      ((tendsto_nat_polynomial_exp C c A hc).comp hpt))
  have hbranch := ((d.branch_smooth.contDiffAt
    (d.massDomain_open.mem_nhds (d.massWindow_subset ht0.2))).continuousAt.tendsto).comp
      ((continuous_snd.tendsto theta0).comp htt)
  simpa only [sub_add_cancel,zero_add,Function.comp_def] using hzero.add hbranch

def cutoffLimitData (d : LimitingStandingData Ξ seed) (m : d.MassInterval) :
    TruncatedParisiData r d.cutoff :=
  cutoffComparisonData Ξ (d.branch m) (d.branch_nondegenerate m m.property).choose
    m ⟨d.massLower_mem.1.le.trans m.property.1,m.property.2⟩ d.cutoff
    (d.ball_below_cutoff _ (by
      rw [mem_closedBall]
      exact (d.branch_close m m.property).le.trans (by linarith [d.radius_pos])))

theorem cutoffLimitData_firstVariation (d : LimitingStandingData Ξ seed)
    (m : d.MassInterval) :
    EqOn (d.cutoffLimitData m).firstVariation (d.limitingVariation m)
      (Icc (0:ℝ) d.cutoff) := by
  intro q hq
  rw [d.limitingVariation_eq_actual m q ⟨hq.1,hq.2.trans d.cutoff_mem.2.le⟩]
  unfold cutoffLimitData
  rw [firstVariation_cutoffComparisonData Ξ _ _ _
    ⟨d.massLower_mem.1.trans_le m.property.1,m.property.2⟩ _ _ d.cutoff_mem.2.le q hq]
  simp only [inv_pow]

end LimitingStandingData
end GeneralDepthPaper
