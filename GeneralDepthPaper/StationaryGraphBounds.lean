module

public import GeneralDepthPaper.StationaryLowerC2

@[expose] public section


/-! Sup-norm control of the genuine stationary graphs. The common
parameter coordinate cancels exactly in their difference. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 1600000
variable {Θ E:Type} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_stationary_graph_difference_jet_le {q r:Θ→E} {θ:Θ}
    (hq:ContDiffAt ℝ ∞ q θ) (hr:ContDiffAt ℝ ∞ r θ) (j:ℕ) :
    ‖iteratedFDeriv ℝ j (fun u:Θ=>(u,q u)-(u,r u)) θ‖ ≤
      ‖iteratedFDeriv ℝ j (fun u=>q u-r u) θ‖ := by
  let L:=ContinuousLinearMap.inr ℝ Θ E
  have hL:‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    simp only [L,ContinuousLinearMap.inr_apply,Prod.norm_def,norm_zero,one_mul]
    exact max_le (norm_nonneg _) le_rfl
  have he:(fun u:Θ=>(u,q u)-(u,r u))=L∘(fun u=>q u-r u) := by
    ext u <;> simp [L]
  rw [he]
  exact (L.norm_iteratedFDeriv_comp_left (hq.sub hr) (show (j:ℕ∞ω) ≤ ∞ by simp)).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hL (norm_nonneg _))

theorem bounded_smooth_finite_jet_bound {f:Θ→E} {s:Set Θ}
    (hf:BoundedSmoothOn f s) (n:ℕ) :
    ∃D:ℝ,1 ≤ D ∧ ∀x∈s,∀j:ℕ,j ≤ n→‖iteratedFDeriv ℝ j f x‖ ≤ D := by
  classical
  choose C hC hB using hf.bound
  let D:ℝ:=1+∑i∈Finset.range (n+1),C i
  have hs:0 ≤ ∑i∈Finset.range (n+1),C i := Finset.sum_nonneg (fun i _=>hC i)
  refine ⟨D,by dsimp only [D];linarith,?_⟩
  intro x hx j hj
  exact (hB j x hx).trans ((Finset.single_le_sum (s:=Finset.range (n+1)) (a:=j) (fun i _=>hC i)
    (Finset.mem_range.mpr (by omega))).trans (by dsimp only [D];linarith))

namespace LimitingStandingData
variable {Ξ:AdmissibleCovariance} {r:ℕ} {seed:AtomicPoint r}

theorem limiting_graph_bounded_smooth (d:LimitingStandingData Ξ seed) :
    BoundedSmoothOn (fun theta:ℝ×ℝ=>(theta,d.branch theta.2)) d.parameterWindow := by
  have hid:BoundedSmoothOn (fun theta:ℝ×ℝ=>theta) d.parameterWindow :=
    BoundedSmoothOn.of_compact (isCompact_Icc.prod isCompact_Icc) (fun _ _=>contDiffAt_id)
  exact hid.prodMk d.limiting_branch_bounded_smooth

end LimitingStandingData
end GeneralDepthPaper
