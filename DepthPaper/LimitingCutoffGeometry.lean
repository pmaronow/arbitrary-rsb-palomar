module

public import DepthPaper.StationaryCutoffSequence

@[expose] public section


/-! The actual ψ-comparison first variation satisfies the limiting
contact hypotheses on the chosen cutoff interval. This follows from the
nondegeneracy of the constructed temperature branch. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 1200000
namespace LimitingStandingData
variable {Ξ : AdmissibleCovariance} {r : ℕ} {seed : AtomicPoint r}

theorem limiting_cutoff_geometry (d : LimitingStandingData Ξ seed) (m : d.MassInterval) :
    (∀q∈Icc (0:ℝ) d.cutoff,(d.cutoffLimitData m).firstVariation q≤0) ∧
    (∀q∈Icc (0:ℝ) d.cutoff,(d.cutoffLimitData m).firstVariation q=0↔
      q=0 ∨ ∃i:Fin r,(d.branch m).1 i=q) ∧
    (∀i:Fin r,(d.branch m).1 i∈Ioo (0:ℝ) d.cutoff) ∧
    (∀i:Fin r,closedJet d.cutoff 2 (d.cutoffLimitData m).firstVariation
      ((d.branch m).1 i)<0) := by
  let z:=d.branch m
  let hz: IsAtomicPoint z:=(d.branch_nondegenerate m m.property).choose
  have hnd:Nondegenerate ((temperatureCovarianceFamily Ξ).covariance m) z hz:=
    (d.branch_nondegenerate m m.property).choose_spec
  have hmp : 0<(m:ℝ):=d.massLower_mem.1.trans_le m.property.1
  let a:ℝ:=(m:ℝ)⁻¹^2
  have ha : 0<a:=sq_pos_of_pos (inv_pos.mpr hmp)
  let f:=firstVariation ((temperatureCovarianceFamily Ξ).covariance m) (atomicMeasure z hz)
  have he : EqOn (d.cutoffLimitData m).firstVariation (fun q=>a*f q) (Icc (0:ℝ) d.cutoff) := by
    intro q hq
    rw [d.cutoffLimitData_firstVariation m hq,
      d.limitingVariation_eq_actual m q ⟨hq.1,hq.2.trans d.cutoff_mem.2.le⟩]
  have hlast : atomicLocation z (Fin.last r)<d.cutoff := by
    apply d.ball_below_cutoff
    rw [mem_closedBall]
    exact (d.branch_close m m.property).le.trans (by linarith [d.radius_pos])
  have hi (i:Fin r) : z.1 i∈Ioo (0:ℝ) d.cutoff := by
    refine ⟨?_,?_⟩
    · simpa only [atomicLocation_zero,atomicLocation_succ] using
        hz.1 (show (0:Fin (r+1)) < i.succ from Fin.succ_pos i)
    · exact (hz.1.monotone (Fin.le_last i.succ)).trans_lt hlast
  refine ⟨?_,?_,hi,?_⟩
  · intro q hq
    rw [he hq]
    exact mul_nonpos_of_nonneg_of_nonpos ha.le
      (hnd.2.1 q ⟨hq.1,hq.2.trans d.cutoff_mem.2.le⟩).1
  · intro q hq
    rw [he hq,mul_eq_zero,or_iff_right ha.ne',
      (hnd.2.1 q ⟨hq.1,hq.2.trans d.cutoff_mem.2.le⟩).2]
    constructor
    · rintro ⟨i,hi⟩
      rcases Fin.eq_zero_or_eq_succ i with rfl|⟨j,rfl⟩
      · exact Or.inl hi
      · exact Or.inr ⟨j,hi.symm⟩
    · rintro (rfl|⟨i,hi⟩)
      · exact ⟨0,rfl⟩
      · exact ⟨i.succ,hi.symm⟩
  · intro i
    rw [closedJet_congr_interval he 2 (Ioo_subset_Icc_self (hi i)),closedJet_const_mul]
    have hEq : closedJet d.cutoff 2 f (z.1 i)=closedJet 1 2 f (z.1 i) := by
      rw [closedJet_two_of_mem_Ioo f (hi i),
        closedJet_two_of_mem_Ioo f ⟨(hi i).1,(hi i).2.trans d.cutoff_mem.2⟩]
    dsimp only
    rw [hEq]
    exact mul_neg_of_pos_of_neg ha (hnd.2.2.1 i)

end LimitingStandingData
end DepthPaper
