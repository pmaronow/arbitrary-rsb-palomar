module

public import DepthPaper.FrozenEndpointJetBounds
public import DepthPaper.ReducedGraphJetBounds
public import DepthPaper.DistinguishedEndpointJets

@[expose] public section


/-! The actual reduced endpoint functional converges in C³, uniformly
on every physical compact lower chart. All implicit-root, terminal, and
recursion jet estimates are discharged by their proved actual bounds. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 64

theorem three_degree_exp_envelope {C1 C2 C3 c1 c2 c3:ℝ} {A1 A2 A3:ℕ}
    (hC1:0 ≤ C1) (hC2:0 ≤ C2) (hC3:0 ≤ C3)
    (hc1:0 < c1) (hc2:0 < c2) (hc3:0 < c3) :
    ∃C:ℝ,0 < C ∧ ∃A:ℕ,∃c:ℝ,0 < c ∧ ∀p:ℕ,1 ≤ p→
      C1*(p:ℝ)^A1*Real.exp (-c1*(p:ℝ))+
      C2*(p:ℝ)^A2*Real.exp (-c2*(p:ℝ))+
      C3*(p:ℝ)^A3*Real.exp (-c3*(p:ℝ)) ≤ C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) := by
  let A := max (max A1 A2) A3
  let c := min c1 (min c2 c3)
  refine ⟨1+C1+C2+C3,by linarith,A,c,lt_min hc1 (lt_min hc2 hc3),?_⟩
  intro p hp
  have h1 := degree_exp_envelope_le (C:=C1) (A:=A) (c:=c) (d:=c1) hC1 le_rfl
    (min_le_left c1 (min c2 c3)) ((le_max_left A1 A2).trans (le_max_left _ A3)) hp
  have h2 := degree_exp_envelope_le (C:=C2) (A:=A) (c:=c) (d:=c2) hC2 le_rfl
    ((min_le_right c1 (min c2 c3)).trans (min_le_left c2 c3))
    ((le_max_right A1 A2).trans (le_max_left _ A3)) hp
  have h3 := degree_exp_envelope_le (C:=C3) (A:=A) (c:=c) (d:=c3) hC3 le_rfl
    ((min_le_right c1 (min c2 c3)).trans (min_le_right c2 c3))
    (le_max_right (max A1 A2) A3) hp
  have hn : 0 ≤ (p:ℝ)^A*Real.exp (-c*(p:ℝ)) := by positivity
  dsimp only [A,c] at hn ⊢
  nlinarith

theorem endpointStrip_gap_square_le {cQ CQ:ℝ} (hcQ:0 < cQ) (p:ℕ) {Q:ℝ}
    (hQ:Q∈endpointStrip cQ CQ p) : (1-Q)^2 ≤ Real.exp (-2*cQ*(p:ℝ)) := by
  have hunit := endpointStrip_mem_unit hcQ p hQ
  have hg : 1-Q ≤ Real.exp (-cQ*(p:ℝ)) := by linarith [hQ.1]
  have hs : (1-Q)^2 ≤ (Real.exp (-cQ*(p:ℝ)))^2 := by
    nlinarith [sub_nonneg.mpr hunit.2.le,Real.exp_pos (-cQ*(p:ℝ))]
  have he : Real.exp (-2*cQ*(p:ℝ))=(Real.exp (-cQ*(p:ℝ)))^2 := by
    rw [show -2*cQ*(p:ℝ)=(-cQ*(p:ℝ))+(-cQ*(p:ℝ)) by ring,Real.exp_add,pow_two]
  rw [he]
  exact hs

theorem reduced_endpoint_C3_exponential_bound (Ξ:AdmissibleCovariance) {r:ℕ}
    {K:Set (AtomicPoint r)} (hK:IsCompact K) (hvalid:∀z∈K,IsAtomicPoint z)
    {e lo hi qc cQ CQ:ℝ} (he:e∈Ioo (0:ℝ) 1) (hlo:0 < lo) (hLH:lo ≤ hi)
    (hc:qc∈Ioo (0:ℝ) 1) (hcut:∀z∈K,atomicLocation z (Fin.last r) < qc)
    (hcQ:0 < cQ) (hclo:cQ < e^2*lo/2) (hChi:hi/2 < CQ) :
    ∃C:ℝ,0 < C ∧ ∃A:ℕ,∃c:ℝ,0 < c ∧
      ∀ᶠp:ℕ in atTop,∀heven:Even p,∀theta:HighDegreeLowerParameter r,
        theta.1∈K→theta.2.1∈Icc e 1→theta.2.2∈Icc lo hi→
        ∀j:ℕ,j ≤ 3→‖iteratedFDeriv ℝ j
          (fun u=>reducedEndpointFunctional Ξ p qc cQ CQ u-limitingObjectiveCore Ξ u) theta‖ ≤
            C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) := by
  obtain ⟨CE,hCE,HE⟩ := endpointTerm_full_jet_bound (r:=r) Ξ hi 3
  obtain ⟨CP,hCP,HP⟩ := endpointTerm_pure_core_jet_bound (r:=r) Ξ hi 3
  obtain ⟨CR,hCR,AR,cR,hcR,PR,hPR,HR⟩ := lower_recursion_error_exponential_bound
    Ξ hK hvalid he.1 hlo hLH hc hcut hcQ (CQ:=CQ) 3
  obtain ⟨CQjet,hCQjet,AQ,cjet,hcjet,HQjet⟩ := distinguished_endpoint_derivatives_exponential_bound
    Ξ hK hvalid he hlo hLH hc hcut hcQ hclo hChi
  have hcompact:IsCompact (K×ˢ(Icc e 1×ˢIcc lo hi)) :=
    hK.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨B,hB⟩ := hcompact.exists_bound_of_continuousOn (f:=id) continuous_id.continuousOn
  let D := max B 1
  have hD:1 ≤ D := le_max_right _ _
  obtain ⟨CG,hCG,HG⟩ := reduced_graph_difference_bounds_through_three
    (E:=HighDegreeLowerParameter r) D hD
  let AM := max 4 AR
  obtain ⟨C,hC,A,c,hcpos,Hsum⟩ := three_degree_exp_envelope
    (A1:=AM+AQ) (A2:=2) (A3:=AR)
    (show 0 ≤ CG*(CE+CR)*CQjet by positivity) hCP hCR.le hcjet
    (show 0 < 2*cQ by positivity) hcR
  refine ⟨C,hC,A,c,hcpos,?_⟩
  filter_upwards [eventually_ge_atTop (max PR 4),HQjet,
    distinguished_endpoint_smooth_eventually Ξ hK hvalid he hlo hLH hc hcut hcQ hclo hChi,
    (tendsto_nat_polynomial_exp CQjet cjet AQ hcjet).eventually (Iio_mem_nhds zero_lt_one)]
      with p hp hrootjets hs hsmall heven theta hz hm hl j hj
  have hp4:4 ≤ p := (le_max_right _ _).trans hp
  have hp1:1 ≤ p := by omega
  have hcast:(1:ℝ) ≤ p := by exact_mod_cast hp1
  have hroot := hs heven theta hz hm hl
  let q := distinguishedEndpoint (r:=r) Ξ p qc cQ CQ
  have hq:ContDiffAt ℝ ∞ q theta := hroot.2.2.2
  have hqstrip:q theta∈endpointStrip cQ CQ p := Ioo_subset_Icc_self hroot.2.1
  have hqunit:q theta∈Icc (0:ℝ) 1 :=
    ⟨(endpointStrip_mem_unit hcQ p hqstrip).1,(endpointStrip_mem_unit hcQ p hqstrip).2.le⟩
  let w:HighDegreeLowerParameter r×ℝ := (theta,q theta)
  let x:CutoffInputParameter r := cutoffParameterAssembly w
  have hx:x∈cutoffInputSmoothDomain Ξ p qc :=
    (hroot.1.1 _ hqstrip).1.1
  have hR := HR p ((le_max_left _ _).trans hp) x hz hm hl hqstrip
  have hlim:Real.exp (-cR*(p:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have hp0:0 ≤ (p:ℝ) := Nat.cast_nonneg _
    nlinarith)
  have hRb:∀i:ℕ,i ≤ 3→‖iteratedFDeriv ℝ i (lowerRecursionErrorRaw Ξ p qc) x‖ ≤
      CR*(p:ℝ)^AR := by
    intro i hi
    exact (hR.2 i hi).trans ((mul_le_mul_of_nonneg_left hlim (by positivity)).trans_eq (mul_one _))
  have hEb := HE p (by omega) x ⟨he.1.le.trans hm.1,hm.2⟩
    ⟨hlo.le.trans hl.1,hl.2⟩ hqunit
  let M:ℝ := (CE+CR)*(p:ℝ)^AM
  let ε:ℝ := CQjet*(p:ℝ)^AQ*Real.exp (-cjet*(p:ℝ))
  let δ:ℝ := CP*(p:ℝ)^2*Real.exp (-2*cQ*(p:ℝ))+
    CR*(p:ℝ)^AR*Real.exp (-cR*(p:ℝ))
  have hfull:∀i:ℕ,i ≤ 3→‖iteratedFDeriv ℝ i (endpointCorrectionChart Ξ p qc) w‖ ≤ M := by
    intro i hi
    have hb := endpointCorrectionChart_full_jet_bound Ξ p qc hx i (hEb i hi) (hRb i hi)
    have hpowE := pow_le_pow_right₀ hcast (le_max_left 4 AR)
    have hpowR := pow_le_pow_right₀ hcast (le_max_right 4 AR)
    have hbE := mul_le_mul_of_nonneg_left hpowE (zero_le_one.trans hCE)
    have hbR := mul_le_mul_of_nonneg_left hpowR hCR.le
    exact hb.trans (by dsimp only [M,AM];norm_num at hb ⊢;nlinarith [hbE,hbR])
  have hpure:∀i:ℕ,i ≤ 3→‖iteratedFDeriv ℝ i
      (fun u=>endpointCorrectionChart Ξ p qc (u,q theta)) theta‖ ≤ δ := by
    intro i hi
    have hEp := HP p (by omega) (q theta) hqunit theta
      ⟨he.1.le.trans hm.1,hm.2⟩ ⟨hlo.le.trans hl.1,hl.2⟩ i hi
    have hEexp := hEp.trans (mul_le_mul_of_nonneg_left (endpointStrip_gap_square_le hcQ p hqstrip)
      (show 0 ≤ CP*(p:ℝ)^2 by positivity))
    exact endpointCorrectionChart_pure_jet_bound Ξ p qc (q theta) hx i hEexp (hR.2 i hi)
  have htheta:‖theta‖ ≤ D := (hB theta ⟨hz,hm,hl⟩).trans (le_max_left _ _)
  have hvalue:‖q theta‖ ≤ D := by
    rw [Real.norm_of_nonneg hqunit.1]
    exact hqunit.2.trans hD
  have hgraph := HG (endpointCorrectionChart Ξ p qc) q theta M ε δ
    (by dsimp only [M];positivity) (by dsimp only [ε];positivity) hsmall.le
    (contDiffAt_endpointCorrectionChart Ξ p qc hx) hq htheta hvalue hfull
    (fun i hi hj=>hrootjets heven theta hz hm hl i hi hj) hpure j hj
  have heq:(fun u=>reducedEndpointFunctional Ξ p qc cQ CQ u-limitingObjectiveCore Ξ u)=
      (fun u=>endpointCorrectionChart Ξ p qc (u,q u)) := by
    funext u
    rw [reducedEndpointFunctional,endpointFunctionalChart_eq_limiting_add_correction]
    ring
  rw [heq]
  apply hgraph.trans
  have hsump := Hsum p hp1
  have heprod : CG*M*ε+δ=
      CG*(CE+CR)*CQjet*(p:ℝ)^(AM+AQ)*Real.exp (-cjet*(p:ℝ))+
      CP*(p:ℝ)^2*Real.exp (-2*cQ*(p:ℝ))+
      CR*(p:ℝ)^AR*Real.exp (-cR*(p:ℝ)) := by
    dsimp only [M,ε,δ]
    rw [pow_add]
    ring
  rw [heprod]
  simpa only [neg_mul] using hsump

end DepthPaper
