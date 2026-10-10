module

public import DepthPaper.ReducedEndpointLimit
public import DepthPaper.EndpointFunctionalHessian

@[expose] public section


/-! Proposition 4.4 in full: the unique actual contact, root location and
jet bounds, actual reduced value, endpoint Hessian, envelope identity,
and uniform C³ convergence to the limiting atomic objective. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 64

def EndpointRootTarget : Prop :=
  ∀Ξ:AdmissibleCovariance,∀r:ℕ,∀K:Set (AtomicPoint r),IsCompact K→
    ∀hvalid:(∀z∈K,IsAtomicPoint z),∀e lo hi qc cQ CQ:ℝ,
      e∈Ioo (0:ℝ) 1→∀hlo:0 < lo,lo ≤ hi→qc∈Ioo (0:ℝ) 1→
      (∀z∈K,atomicLocation z (Fin.last r) < qc)→0 < cQ→
      cQ < e^2*lo/2→hi/2 < CQ→
      ∃b:ℝ,0 < b ∧ ∃D:ℝ,0 < D ∧
      ∃Cq:ℝ,0 < Cq ∧ ∃Aq:ℕ,∃cq:ℝ,0 < cq ∧
      ∃Cf:ℝ,0 < Cf ∧ ∃Af:ℕ,∃cf:ℝ,0 < cf ∧ ∃P:ℕ,4 ≤ P ∧
        ∀p:ℕ,P ≤ p→∀heven:Even p,∃hp:4 ≤ p,∃hn:p∉Ξ.degrees,
          ∀theta:HighDegreeLowerParameter r,∀hz:theta.1∈K,
            theta.2.1∈Icc e 1→∀hlam:theta.2.2∈Icc lo hi,
            let Ψ := Ξ.addHighDegree p hp heven hn theta.2.2 (hlo.trans_le hlam.1)
            let Q := distinguishedOverlap Ξ p qc cQ CQ theta
            (Q:ℝ)=distinguishedEndpoint Ξ p qc cQ CQ theta ∧
            (Q:ℝ)∈Ioo (1-Real.exp (-cQ*(p:ℝ))) (1-Real.exp (-CQ*(p:ℝ))) ∧
            Gamma Ψ (twoLevelMeasure theta.1 (hvalid _ hz) theta.2.1 Q) Q=(Q:ℝ) ∧
            (∀T:Overlap,(T:ℝ)∈endpointStrip cQ CQ p→
              Gamma Ψ (twoLevelMeasure theta.1 (hvalid _ hz) theta.2.1 T) T=(T:ℝ)→T=Q) ∧
            b*(p:ℝ)^(-(1/2:ℝ))*Real.exp (-theta.2.1^2*theta.2.2*(p:ℝ)/2) ≤ 1-(Q:ℝ) ∧
            1-(Q:ℝ) ≤ D*(p:ℝ)^(-(1/2:ℝ))*Real.exp (-theta.2.1^2*theta.2.2*(p:ℝ)/2) ∧
            ContDiffAt ℝ ∞ (distinguishedEndpoint Ξ p qc cQ CQ) theta ∧
            (∀j:ℕ,1 ≤ j→j ≤ 2→‖iteratedFDeriv ℝ j
              (distinguishedEndpoint Ξ p qc cQ CQ) theta‖ ≤ Cq*(p:ℝ)^Aq*Real.exp (-cq*(p:ℝ))) ∧
            ContDiffAt ℝ ∞ (reducedEndpointFunctional Ξ p qc cQ CQ) theta ∧
            reducedEndpointFunctional Ξ p qc cQ CQ theta=twoLevelFunctional Ψ theta.1
              (hvalid _ hz) theta.2.1 Q ∧
            fderiv ℝ (reducedEndpointFunctional Ξ p qc cQ CQ) theta=
              (fderiv ℝ (endpointFunctionalChart Ξ p qc)
                (theta,distinguishedEndpoint Ξ p qc cQ CQ theta)).comp
                  (ContinuousLinearMap.inl ℝ (HighDegreeLowerParameter r) ℝ) ∧
            (theta.2.1 < 1→0 < deriv (deriv (fun q=>twoLevelFunctional Ψ theta.1 (hvalid _ hz)
              theta.2.1 (projIcc 0 1 zero_le_one q))) Q) ∧
            (∀j:ℕ,j ≤ 3→‖iteratedFDeriv ℝ j
              (fun u=>reducedEndpointFunctional Ξ p qc cQ CQ u-limitingObjectiveCore Ξ u)
                theta‖ ≤ Cf*(p:ℝ)^Af*Real.exp (-cf*(p:ℝ)))

theorem endpoint_root : EndpointRootTarget := by
  intro Ξ r K hK hvalid e lo hi qc cQ CQ he hlo hLH hc hcut hcQ hclo hChi
  obtain ⟨b,hb,D,hD,Hcontact⟩ := distinguished_endpoint_contact_eventually
    Ξ hK hvalid he hlo hLH hc hcut hcQ hclo hChi
  obtain ⟨Cq,hCq,Aq,cq,hcq,Hq⟩ := distinguished_endpoint_derivatives_exponential_bound
    Ξ hK hvalid he hlo hLH hc hcut hcQ hclo hChi
  obtain ⟨Cf,hCf,Af,cf,hcf,Hf⟩ := reduced_endpoint_C3_exponential_bound
    Ξ hK hvalid he hlo hLH hc hcut hcQ hclo hChi
  have hCQ : cQ < CQ := by
    have hp : e^2*lo ≤ hi := by
      have hh := mul_le_mul_of_nonneg_right (show e^2 ≤ 1 by nlinarith [he.1,he.2]) hlo.le
      nlinarith
    linarith
  have H:
      ∀ᶠp:ℕ in atTop,4 ≤ p ∧ ∀heven:Even p,∃hp:4 ≤ p,∃hn:p∉Ξ.degrees,
        ∀theta:HighDegreeLowerParameter r,∀hz:theta.1∈K,
          theta.2.1∈Icc e 1→∀hlam:theta.2.2∈Icc lo hi,
          let Ψ := Ξ.addHighDegree p hp heven hn theta.2.2 (hlo.trans_le hlam.1)
          let Q := distinguishedOverlap Ξ p qc cQ CQ theta
          (Q:ℝ)=distinguishedEndpoint Ξ p qc cQ CQ theta ∧
          (Q:ℝ)∈Ioo (1-Real.exp (-cQ*(p:ℝ))) (1-Real.exp (-CQ*(p:ℝ))) ∧
          Gamma Ψ (twoLevelMeasure theta.1 (hvalid _ hz) theta.2.1 Q) Q=(Q:ℝ) ∧
          (∀T:Overlap,(T:ℝ)∈endpointStrip cQ CQ p→
            Gamma Ψ (twoLevelMeasure theta.1 (hvalid _ hz) theta.2.1 T) T=(T:ℝ)→T=Q) ∧
          b*(p:ℝ)^(-(1/2:ℝ))*Real.exp (-theta.2.1^2*theta.2.2*(p:ℝ)/2) ≤ 1-(Q:ℝ) ∧
          1-(Q:ℝ) ≤ D*(p:ℝ)^(-(1/2:ℝ))*Real.exp (-theta.2.1^2*theta.2.2*(p:ℝ)/2) ∧
          ContDiffAt ℝ ∞ (distinguishedEndpoint Ξ p qc cQ CQ) theta ∧
          (∀j:ℕ,1 ≤ j→j ≤ 2→‖iteratedFDeriv ℝ j
            (distinguishedEndpoint Ξ p qc cQ CQ) theta‖ ≤ Cq*(p:ℝ)^Aq*Real.exp (-cq*(p:ℝ))) ∧
          ContDiffAt ℝ ∞ (reducedEndpointFunctional Ξ p qc cQ CQ) theta ∧
          reducedEndpointFunctional Ξ p qc cQ CQ theta=twoLevelFunctional Ψ theta.1
            (hvalid _ hz) theta.2.1 Q ∧
          fderiv ℝ (reducedEndpointFunctional Ξ p qc cQ CQ) theta=
            (fderiv ℝ (endpointFunctionalChart Ξ p qc)
              (theta,distinguishedEndpoint Ξ p qc cQ CQ theta)).comp
                (ContinuousLinearMap.inl ℝ (HighDegreeLowerParameter r) ℝ) ∧
          (theta.2.1 < 1→0 < deriv (deriv (fun q=>twoLevelFunctional Ψ theta.1 (hvalid _ hz)
            theta.2.1 (projIcc 0 1 zero_le_one q))) Q) ∧
          (∀j:ℕ,j ≤ 3→‖iteratedFDeriv ℝ j
            (fun u=>reducedEndpointFunctional Ξ p qc cQ CQ u-limitingObjectiveCore Ξ u)
              theta‖ ≤ Cf*(p:ℝ)^Af*Real.exp (-cf*(p:ℝ))) := by
    filter_upwards [Hcontact,Hq,Hf,
      endpoint_root_inputs_eventually Ξ hK hvalid he.1 hlo hLH hc hcut hcQ hclo hChi,
      endpointStrip_above_cutoff_eventually (CQ:=CQ) hc.2 hcQ] with p hcon hjet hlim hinput hqc
    refine ⟨hcon.1,?_⟩
    intro heven
    obtain ⟨hp4,hn,hdata⟩ := hcon.2 heven
    obtain ⟨_,_,hinputs⟩ := hinput.2 heven
    refine ⟨hp4,hn,?_⟩
    intro theta hz hm hl
    have hd := hdata theta hz hm hl
    have hin := hinputs theta hz hm hl
    have hdom := distinguishedEndpointDomain_mem_of_inputs Ξ p qc cQ CQ theta
      hin.1 hin.2.1 hin.2.2
    let Q := distinguishedOverlap Ξ p qc cQ CQ theta
    have hstrip:(Q:ℝ)∈endpointStrip cQ CQ p := Ioo_subset_Icc_self hd.2.1
    have hQunit:(Q:ℝ)∈Icc (0:ℝ) 1 := Q.property
    have hqcQ:qc < (Q:ℝ) := hqc Q hstrip
    have hQ1:(Q:ℝ) < 1 := (endpointStrip_mem_unit hcQ p hstrip).2
    have hqunit:distinguishedEndpoint Ξ p qc cQ CQ theta∈Icc (0:ℝ) 1 := by
      rw [←hd.1]
      exact hQunit
    have hrootunit:distinguishedEndpoint Ξ p qc cQ CQ theta∈Ioo qc 1 := by
      rw [←hd.1]
      exact ⟨hqcQ,hQ1⟩
    have hs := distinguishedEndpoint_spec Ξ p qc cQ CQ hCQ (by omega) hdom
    have hm0:0 < theta.2.1 := he.1.trans_le hm.1
    have hms:theta.2.1∈Ioo (0:ℝ) 2 := ⟨hm0,hm.2.trans_lt (by norm_num)⟩
    have hrSmooth := contDiffAt_reducedEndpointFunctional Ξ p qc cQ CQ hCQ (by omega) (hvalid _ hz) hdom
    have hv := reducedEndpointFunctional_eq_actual Ξ p hp4 heven hn qc cQ CQ theta (hvalid _ hz)
      ⟨hm0,hm.2⟩ (hlo.trans_le hl.1) (hcut _ hz) hqunit hrootunit.1.le
    have hen := reducedEndpointFunctional_envelope Ξ p hp4 heven hn qc cQ CQ hCQ
      (hvalid _ hz) hms (hlo.trans_le hl.1) (hcut _ hz) hdom hrootunit
    have hhess:theta.2.1 < 1→0 < deriv (deriv (fun q=>twoLevelFunctional
        (Ξ.addHighDegree p hp4 heven hn theta.2.2 (hlo.trans_le hl.1)) theta.1
        (hvalid _ hz) theta.2.1 (projIcc 0 1 zero_le_one q))) Q := by
      intro hm1
      have hzero:endpointRootEquation Ξ p qc (theta,(Q:ℝ))=0 := by rw [hd.1];exact hs.2.1
      exact actual_endpoint_hessian_pos Ξ p hp4 heven hn theta.1 (hvalid _ hz) ⟨hm0,hm1⟩
        theta.2.2 (hlo.trans_le hl.1) Q (hcut _ hz) hqcQ hQ1 hzero
          ((by norm_num : (0:ℝ) < 1/2).trans_le (hin.1 Q hstrip).2)
    exact ⟨hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1,hd.2.2.2.2.1,hd.2.2.2.2.2.1,
      hd.2.2.2.2.2.2,(fun j hj hj2=>hjet heven theta hz hm hl j hj (by omega)),
      hrSmooth,hv,hen,hhess,hlim heven theta hz hm hl⟩
  obtain ⟨P,hP⟩ := eventually_atTop.mp H
  refine ⟨b,hb,D,hD,Cq,hCq,Aq,cq,hcq,Cf,hCf,Af,cf,hcf,max P 4,le_max_right _ _,?_⟩
  intro p hp
  exact (hP p ((le_max_left _ _).trans hp)).2

end DepthPaper
