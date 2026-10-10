module

public import GeneralDepthPaper.CoincidentCompositionBounds
public import GeneralDepthPaper.ImplicitRootThirdJetBounds

@[expose] public section


/-! A quantitative C³ elimination bound. A graph whose positive-order
jets are small is compared at the same point with the frozen endpoint
graph, using only actual outer jets and actual chain rules. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 64
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem implicit_graph_jet_bound_through_three {q:E→ℝ} {theta:E} {D ε:ℝ}
    (hD:1 ≤ D) (hε:ε ≤ 1) (hq:ContDiffAt ℝ ∞ q theta)
    (htheta:‖theta‖ ≤ D) (hvalue:‖q theta‖ ≤ D)
    (hb:∀i:ℕ,1 ≤ i→i ≤ 3→‖iteratedFDeriv ℝ i q theta‖ ≤ ε) :
    ∀i:ℕ,i ≤ 3→‖iteratedFDeriv ℝ i (fun u=>(u,q u)) theta‖ ≤ D := by
  intro i hi
  interval_cases i
  · rw [norm_iteratedFDeriv_zero,Prod.norm_def]
    exact max_le htheta hvalue
  · rw [norm_iteratedFDeriv_one]
    apply (implicit_graph_first_norm_le hq).trans
    exact max_le hD (by simpa only [norm_iteratedFDeriv_one] using
      (hb 1 le_rfl (by omega)).trans (hε.trans hD))
  · rw [implicit_graph_second_norm_eq hq]
    exact (hb 2 (by omega) (by omega)).trans (hε.trans hD)
  · rw [implicit_graph_third_norm_eq hq]
    exact (hb 3 (by omega) le_rfl).trans (hε.trans hD)

theorem implicit_graph_difference_jet_bound_through_three {q:E→ℝ} {theta:E} {ε:ℝ}
    (hε:0 ≤ ε) (hq:ContDiffAt ℝ ∞ q theta)
    (hb:∀i:ℕ,1 ≤ i→i ≤ 3→‖iteratedFDeriv ℝ i q theta‖ ≤ ε) :
    ∀i:ℕ,i ≤ 3→‖iteratedFDeriv ℝ i
      (fun u=>(u,q u)-(u,q theta)) theta‖ ≤ ε := by
  intro i hi
  by_cases hi0:i=0
  · subst i
    simpa only [norm_iteratedFDeriv_zero,sub_self,norm_zero] using hε
  · have heq:(fun u=>(u,q u)-(u,q theta))=(fun u:E=>(0,q u-q theta)) := by
      funext u
      simp only [Prod.mk_sub_mk,sub_self]
    rw [heq,iteratedFDeriv_prodMk (contDiffAt_const (c:=(0:E)))
      (hq.sub contDiffAt_const) (by simp),ContinuousMultilinearMap.opNorm_prod]
    rw [iteratedFDeriv_const_of_ne hi0 (0:E),Pi.zero_apply,norm_zero,
      fun_iteratedFDeriv_sub_apply (hq.of_le (by simp)) (contDiffAt_const (c:=q theta)),
      iteratedFDeriv_const_of_ne hi0 (q theta),Pi.zero_apply,sub_zero,max_eq_right (norm_nonneg _)]
    exact hb i (by omega) hi

theorem reduced_graph_difference_bounds_through_three (D:ℝ) (hD:1 ≤ D) :
    ∃C:ℝ,0 ≤ C ∧ ∀H:E×ℝ→ℝ,∀q:E→ℝ,∀theta:E,∀M ε δ:ℝ,
      0 ≤ M→0 ≤ ε→ε ≤ 1→
      ContDiffAt ℝ ∞ H (theta,q theta)→ContDiffAt ℝ ∞ q theta→
      ‖theta‖ ≤ D→‖q theta‖ ≤ D→
      (∀i:ℕ,i ≤ 3→‖iteratedFDeriv ℝ i H (theta,q theta)‖ ≤ M)→
      (∀i:ℕ,1 ≤ i→i ≤ 3→‖iteratedFDeriv ℝ i q theta‖ ≤ ε)→
      (∀i:ℕ,i ≤ 3→‖iteratedFDeriv ℝ i (fun u=>H (u,q theta)) theta‖ ≤ δ)→
      ∀i:ℕ,i ≤ 3→‖iteratedFDeriv ℝ i (fun u=>H (u,q u)) theta‖ ≤ C*M*ε+δ := by
  obtain ⟨C,hC,HC⟩ := coincident_composition_difference_bounds_up_to
    (E:=E) (F:=E×ℝ) (G:=ℝ) 3 D hD
  refine ⟨C,hC,?_⟩
  intro H q theta M ε δ hM hε hε1 hH hq htheta hvalue hHb hqb hpure i hi
  have hf:ContDiffAt ℝ ∞ (fun u=>(u,q u)) theta := contDiffAt_id.prodMk hq
  have hg:ContDiffAt ℝ ∞ (fun u:E=>(u,q theta)) theta :=
    contDiffAt_id.prodMk contDiffAt_const
  have hconst:∀j:ℕ,1 ≤ j→j ≤ 3→‖iteratedFDeriv ℝ j (fun _:E=>q theta) theta‖ ≤ ε := by
    intro j hj _
    rw [iteratedFDeriv_const_of_ne (by omega) (q theta),Pi.zero_apply,norm_zero]
    exact hε
  have hdiff := HC H (fun u=>(u,q u)) (fun u=>(u,q theta)) theta M ε hM hε hH hf hg rfl hHb
    (implicit_graph_jet_bound_through_three hD hε1 hq htheta hvalue hqb)
    (implicit_graph_jet_bound_through_three hD hε1 contDiffAt_const htheta hvalue hconst)
    (implicit_graph_difference_jet_bound_through_three hε hq hqb) i hi
  have hHf := hH.comp theta hf
  have hHg := hH.comp theta hg
  change ContDiffAt ℝ ∞ (fun u=>H (u,q u)) theta at hHf
  change ContDiffAt ℝ ∞ (fun u=>H (u,q theta)) theta at hHg
  rw [fun_iteratedFDeriv_sub_apply (hHf.of_le (by simp)) (hHg.of_le (by simp))] at hdiff
  have htriangle := norm_add_le
    (iteratedFDeriv ℝ i (fun u=>H (u,q u)) theta-
      iteratedFDeriv ℝ i (fun u=>H (u,q theta)) theta)
    (iteratedFDeriv ℝ i (fun u=>H (u,q theta)) theta)
  rw [sub_add_cancel] at htriangle
  exact htriangle.trans (add_le_add hdiff (hpure i hi))

end GeneralDepthPaper
