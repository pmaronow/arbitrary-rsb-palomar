module

public import DepthPaper.DirectionalResponseComparison
public import DepthPaper.StationaryMassLocalIdentity

@[expose] public section


/-! The true mass stationarity function converges in C² to the literal
pressure envelope, uniformly over the whole physical parameter window. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 64

namespace LimitingStandingData
variable {Ξ:AdmissibleCovariance} {r:ℕ} {seed:AtomicPoint r}

theorem stationaryMassFunction_C2_exponential_error (d:LimitingStandingData Ξ seed) :
    ∃C:ℝ,0 < C ∧ ∃A:ℕ,∃c:ℝ,0 < c ∧
      ∀ᶠp:ℕ in atTop,∀heven:Even p,∀theta∈d.parameterWindow,
        ContDiffAt ℝ ∞ (d.stationaryMassFunction p) theta ∧
        ∀j:ℕ,j ≤ 2→‖iteratedFDeriv ℝ j (fun u:ℝ×ℝ=>d.stationaryMassFunction p u-
          (u.1-pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) u.2)/2) theta‖ ≤
            C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) := by
  obtain ⟨Cf,hCf,Af,cf,hcf,Hf⟩:=d.stationaryBranch_regular_error_eventually
  obtain ⟨Cz,hCz,Az,cz,hcz,Hz⟩:=d.stationaryBranch_C2_exponential_error
  obtain ⟨_,_,_,_,_,Hs⟩:=d.stationaryBranch_eventually
  obtain ⟨D0,hD0,HD0⟩:=bounded_smooth_finite_jet_bound d.limiting_graph_bounded_smooth 2
  let D:ℝ:=D0+1
  have hD:1 ≤ D := by dsimp [D];linarith
  have haxis:‖(((0,1),0):(ℝ×ℝ)×AtomicPoint r)‖ ≤ 1 := by simp [Prod.norm_def]
  obtain ⟨K,hK,HK⟩:=directional_response_C2_comparison (E:=ℝ×ℝ)
    (stationaryLimitingObjective Ξ) (((0,1),0):(ℝ×ℝ)×AtomicPoint r) haxis
    d.stationaryInputWindow d.boundedSmoothOn_limitingMassJetField
    d.stationaryInputWindow_convex D hD
  obtain ⟨C,hC,A,c,hc,Hsum⟩:=three_degree_exp_envelope
    (C1:=K*Cf) (C2:=K*Cz) (C3:=0) (A1:=Af) (A2:=Az) (A3:=0)
    (by positivity) (by positivity) (by norm_num) hcf hcz (show (0:ℝ)<1 by norm_num)
  have Hsmall:∀ᶠp:ℕ in atTop,Cz*(p:ℝ)^Az*Real.exp (-cz*(p:ℝ)) ≤ 1 :=
    (tendsto_nat_polynomial_exp Cz cz Az hcz).eventually
      (eventually_le_nhds (show (0:ℝ) < 1 by norm_num))
  refine ⟨C,hC,A,c,hc,?_⟩
  filter_upwards [Hf,Hz,Hs,Hsmall,eventually_ge_atTop 1] with p hf hz hs hsmall hp1
  intro heven theta ht
  let a:ℝ×ℝ→(ℝ×ℝ)×AtomicPoint r:=fun u=>(u,d.stationaryBranch p u)
  let b:ℝ×ℝ→(ℝ×ℝ)×AtomicPoint r:=fun u=>(u,d.branch u.2)
  let f:=stationaryReducedObjective Ξ (r:=r) p d.cutoff d.stripRateLower d.stripRateUpper
  let g:=stationaryLimitingObjective Ξ (r:=r)
  have hreg:=hf heven theta ht
  have hsel:=hs heven theta ht
  have hq:=hreg.1
  have hr:ContDiffAt ℝ ∞ (fun u:ℝ×ℝ=>d.branch u.2) theta :=
    d.limiting_branch_bounded_smooth.smooth theta ht
  have ha:ContDiffAt ℝ ∞ a theta := contDiffAt_id.prodMk hq
  have hb:ContDiffAt ℝ ∞ b theta := contDiffAt_id.prodMk hr
  have hqs:d.stationaryBranch p theta∈closedBall seed d.radius := ball_subset_closedBall hsel.1
  have hrs:d.branch theta.2∈closedBall seed d.radius := by
    rw [mem_closedBall]
    linarith [d.branch_close theta.2 ht.2,d.radius_pos]
  have hax:a theta∈d.stationaryInputWindow := ⟨ht,hqs⟩
  have hbx:b theta∈d.stationaryInputWindow := ⟨ht,hrs⟩
  have hgraph (i:ℕ) (hi:i ≤ 2):
      ‖iteratedFDeriv ℝ i (fun u=>a u-b u) theta‖ ≤ Cz*(p:ℝ)^Az*Real.exp (-cz*(p:ℝ)) :=
    (norm_stationary_graph_difference_jet_le hq hr i).trans (hz heven theta ht i hi)
  have hbj (i:ℕ) (hi:i ≤ 2):‖iteratedFDeriv ℝ i b theta‖ ≤ D :=
    (HD0 theta ht i hi).trans (by dsimp [D];linarith)
  have haj (i:ℕ) (hi:i ≤ 2):‖iteratedFDeriv ℝ i a theta‖ ≤ D := by
    have hsub:‖iteratedFDeriv ℝ i a theta-iteratedFDeriv ℝ i b theta‖ ≤
        Cz*(p:ℝ)^Az*Real.exp (-cz*(p:ℝ)) := by
      rw [←fun_iteratedFDeriv_sub_apply (ha.of_le (by simp)) (hb.of_le (by simp))]
      exact hgraph i hi
    have htri:=norm_add_le (iteratedFDeriv ℝ i a theta-iteratedFDeriv ℝ i b theta)
      (iteratedFDeriv ℝ i b theta)
    rw [sub_add_cancel] at htri
    exact htri.trans ((add_le_add (hsub.trans hsmall) (HD0 theta ht i hi)).trans_eq (by dsimp [D];ring))
  have hfs:ContDiffAt ℝ ∞ f (a theta) := hreg.2.1 _ hqs
  have hgs:ContDiffAt ℝ ∞ g (a theta) := d.boundedSmoothOn_stationaryLimitingObjective.smooth _ hax
  have hscalar (i:ℕ) (_:1 ≤ i) (hi:i ≤ 3):
      ‖iteratedFDeriv ℝ i (fun u=>f u-g u) (a theta)‖ ≤ Cf*(p:ℝ)^Af*Real.exp (-cf*(p:ℝ)) :=
    hreg.2.2.2.1 _ hqs i hi
  have Herr:=HK f a b theta (Cf*(p:ℝ)^Af*Real.exp (-cf*(p:ℝ)))
    (Cz*(p:ℝ)^Az*Real.exp (-cz*(p:ℝ))) (by positivity) (by positivity)
    ha hb hax hbx hfs hgs haj hbj hgraph hscalar
  refine ⟨d.stationaryMassFunction_smooth_at p theta hq hfs,?_⟩
  intro j hj
  have he:(fun u:ℝ×ℝ=>d.stationaryMassFunction p u-
      (u.1-pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) u.2)/2)=ᶠ[𝓝 theta]
      (fun u=>fderiv ℝ f (a u) ((0,1),0)-fderiv ℝ g (b u) ((0,1),0)) := by
    filter_upwards [d.limitingMassJetField_branch_eventuallyEq theta ht] with u hu
    change fderiv ℝ f (a u) ((0,1),0)-_=fderiv ℝ f (a u) ((0,1),0)-_
    rw [←hu]
    rfl
  rw [(he.iteratedFDeriv (𝕜:=ℝ) j).eq_of_nhds]
  exact (Herr j hj).trans (by
    convert Hsum p hp1 using 1 <;> ring)

end LimitingStandingData
end DepthPaper
