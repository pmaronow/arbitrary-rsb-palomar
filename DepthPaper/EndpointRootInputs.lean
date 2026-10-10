module

public import DepthPaper.EndpointRootEquation
public import DepthPaper.EndpointStripSeparation

@[expose] public section


/-! All analytic hypotheses for the endpoint implicit root are discharged
by the literal deficit theorem and the manuscript's strip choices. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 64

theorem endpoint_root_inputs_eventually (Ξ : AdmissibleCovariance) {r : ℕ}
    {K : Set (AtomicPoint r)} (hK : IsCompact K) (hvalid : ∀z∈K,IsAtomicPoint z)
    {e lo hi qc cQ CQ : ℝ} (he : 0 < e) (hlo : 0 < lo) (hLH : lo ≤ hi)
    (hc : qc∈Ioo (0:ℝ) 1) (hcut : ∀z∈K,atomicLocation z (Fin.last r) < qc)
    (hcQ : 0 < cQ) (hclo : cQ < e^2*lo/2) (hChi : hi/2 < CQ) :
    ∀ᶠp:ℕ in atTop,4 ≤ p ∧ ∀heven:Even p,∃hp:4 ≤ p,∃hn:p∉Ξ.degrees,
      ∀theta:HighDegreeLowerParameter r,theta.1∈K→theta.2.1∈Icc e 1→theta.2.2∈Icc lo hi→
        (∀Q∈endpointStrip cQ CQ p,
          (theta,Q)∈endpointRootSmoothDomain Ξ p qc ∧
            1/2 ≤ deriv (fun q=>endpointRootEquation Ξ p qc (theta,q)) Q) ∧
        endpointRootEquation Ξ p qc (theta,1-Real.exp (-cQ*(p:ℝ))) < 0 ∧
        0 < endpointRootEquation Ξ p qc (theta,1-Real.exp (-CQ*(p:ℝ))) := by
  obtain ⟨C,hC,A,c,hcpos,b,hb,D,hD,P,hP,hendpoint⟩ := endpoint_deficit
    Ξ r K hK hvalid e lo hi qc cQ CQ he hlo hLH hc hcut hcQ
  have hjlim := tendsto_nat_polynomial_exp C c A hcpos
  have hsep := deficit_scale_strict_strip_separation he hlo hD.le hb hclo hChi
  filter_upwards [eventually_ge_atTop P,
    endpointStrip_above_cutoff_eventually (CQ:=CQ) hc.2 hcQ,
    hjlim.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1/2)),hsep]
      with p hp hQabove hsmall hsep
  refine ⟨hP.trans hp,?_⟩
  intro heven
  obtain ⟨hp4,hn,hdata⟩ := hendpoint p hp heven
  refine ⟨hp4,hn,?_⟩
  intro theta hz hm hl
  have hm0 : 0 < theta.2.1 := he.trans_le hm.1
  have hmem : ∀Q∈endpointStrip cQ CQ p,(theta,Q)∈endpointRootSmoothDomain Ξ p qc :=
    fun Q hQ=>endpointRootSmoothDomain_mem Ξ p qc theta Q (hvalid _ hz) (hcut _ hz)
      ⟨hm0,hm.2.trans_lt (by norm_num)⟩ (hlo.le.trans hl.1) hc.1.le (hQabove Q hQ)
  have hder : ∀Q∈endpointStrip cQ CQ p,
      1/2 ≤ deriv (fun q=>endpointRootEquation Ξ p qc (theta,q)) Q := by
    intro Q hQ
    let q : Overlap := ⟨Q,⟨(endpointStrip_mem_unit hcQ p hQ).1,
      (endpointStrip_mem_unit hcQ p hQ).2.le⟩⟩
    have H := hdata theta.1 hz theta.2.1 hm theta.2.2 hl q hQ
    have hb1 := (H.2.2.1 1 (by norm_num)).trans hsmall.le
    exact endpointRootEquation_derivative_ge_half Ξ p qc theta Q (hmem Q hQ) hb1
  have hpowm : e^2*lo ≤ hi := by
    have h := mul_le_mul (show e^2 ≤ theta.2.1^2 by nlinarith [hm.1]) hl.1 hlo.le
      (sq_nonneg theta.2.1)
    have h2 := mul_le_mul_of_nonneg_right (show theta.2.1^2 ≤ 1 by nlinarith [hm0,hm.2])
      (hlo.le.trans hl.1)
    nlinarith [hl.2]
  have hcCQ : cQ < CQ := hclo.trans_le (by linarith [hpowm]) |>.trans hChi
  have hlr : 1-Real.exp (-cQ*(p:ℝ)) ≤ 1-Real.exp (-CQ*(p:ℝ)) := by
    have H := Real.exp_le_exp.mpr (show -CQ*(p:ℝ) ≤ -cQ*(p:ℝ) by
      nlinarith [mul_le_mul_of_nonneg_right hcCQ.le (Nat.cast_nonneg p)])
    linarith
  have hleft : 1-Real.exp (-cQ*(p:ℝ))∈endpointStrip cQ CQ p := ⟨le_rfl,hlr⟩
  have hright : 1-Real.exp (-CQ*(p:ℝ))∈endpointStrip cQ CQ p := ⟨hlr,le_rfl⟩
  let leftQ : Overlap := ⟨1-Real.exp (-cQ*(p:ℝ)),
    ⟨(endpointStrip_mem_unit hcQ p hleft).1,(endpointStrip_mem_unit hcQ p hleft).2.le⟩⟩
  let rightQ : Overlap := ⟨1-Real.exp (-CQ*(p:ℝ)),
    ⟨(endpointStrip_mem_unit hcQ p hright).1,(endpointStrip_mem_unit hcQ p hright).2.le⟩⟩
  have Hleft := hdata theta.1 hz theta.2.1 hm theta.2.2 hl leftQ hleft
  have Hright := hdata theta.1 hz theta.2.1 hm theta.2.2 hl rightQ hright
  have hlbound := Hleft.2.2.2.2.2
  have hrbound := Hright.2.2.2.2.1
  rw [Hleft.1] at hlbound
  rw [Hright.1] at hrbound
  have hsepx := hsep.2 theta.2.1 hm theta.2.2 hl
  refine ⟨fun Q hQ=>⟨hmem Q hQ,hder Q hQ⟩,?_,?_⟩ <;>
    dsimp only [endpointRootEquation,cutoffParameterAssembly_apply] <;> linarith

end DepthPaper
