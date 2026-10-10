module

public import GeneralDepthPaper.StationaryCouplingRoot
public import GeneralDepthPaper.ScalarRootPerturbation

@[expose] public section


/-! Actual C² degree-exponential convergence of the smooth coupling
curve to the physical pressure curve. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 2500000
set_option maxSynthPendingDepth 64

namespace LimitingStandingData
variable {Ξ:AdmissibleCovariance} {r:ℕ} {seed:AtomicPoint r}

def couplingMassResidual (d:LimitingStandingData Ξ seed) (p:ℕ) (w:ℝ×ℝ):ℝ:=
  2*(d.stationaryMassFunction p w-
    (w.1-pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) w.2)/2)

theorem couplingCurve_C2_exponential_error (d:LimitingStandingData Ξ seed):
    ∃C:ℝ,0 < C ∧ ∃A:ℕ,∃c:ℝ,0 < c ∧
      ∀ᶠp:ℕ in atTop,∀heven:Even p,∀m∈Icc d.massLower 1,∀j:ℕ,j ≤ 2→
        ‖iteratedFDeriv ℝ j (fun u=>d.couplingCurve p u-
          pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) u) m‖ ≤
            C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) := by
  let ell:=pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture)
  have hT:BoundedSmoothOn (rootShiftMap ell) (Icc d.massLower 1×ˢIcc (0:ℝ) 2):=by
    apply BoundedSmoothOn.of_compact (isCompact_Icc.prod isCompact_Icc)
    intro w hw
    exact ((contDiffAt_snd.sub contDiffAt_const).add
      ((d.ell_smooth w.1 hw.1).comp w contDiffAt_fst)).prodMk contDiffAt_fst
  obtain ⟨D,hD,HD⟩:=bounded_smooth_finite_jet_bound hT 2
  obtain ⟨Cq,hCq,Aq,cq,hcq,Hq⟩:=d.couplingCurve_eventually
  obtain ⟨Cf,hCf,Af,cf,hcf,Hf⟩:=d.stationaryMassFunction_C2_exponential_error
  obtain ⟨C,hC,A,c,hc,Hsum⟩:=three_degree_exp_envelope
    (C1:=Cq) (C2:=Cf) (C3:=0) (A1:=Aq) (A2:=Af) (A3:=0)
    hCq.le hCf.le (by norm_num) hcq hcf (show (0:ℝ)<1 by norm_num)
  have hDpos:0 < D:=zero_lt_one.trans_le hD
  have Hsmall:∀ᶠp:ℕ in atTop,C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) < min 1 (1/(8*D^2)):=
    (tendsto_nat_polynomial_exp C c A hc).eventually
      (eventually_lt_nhds (show (0:ℝ) < min 1 (1/(8*D^2)) by positivity))
  refine ⟨(1+8*D^2)*C,by positivity,A,c,hc,?_⟩
  filter_upwards [Hq,Hf,Hsmall,eventually_ge_atTop 1] with p hq hf hsmall hp1
  intro heven m hm j hj
  let E:ℝ:=C*(p:ℝ)^A*Real.exp (-c*(p:ℝ))
  have hE:0 ≤ E:=by dsimp [E];positivity
  have hEq:Cq*(p:ℝ)^Aq*Real.exp (-cq*(p:ℝ)) ≤ E:=by
    have hh:=Hsum p hp1
    simp only [zero_mul,mul_zero,add_zero] at hh
    have hn:0 ≤ Cf*(p:ℝ)^Af*Real.exp (-cf*(p:ℝ)):=by positivity
    dsimp [E]
    simpa using (le_add_of_nonneg_right hn).trans hh
  have hEf:Cf*(p:ℝ)^Af*Real.exp (-cf*(p:ℝ)) ≤ E:=by
    have hh:=Hsum p hp1
    simp only [zero_mul,mul_zero,add_zero] at hh
    have hn:0 ≤ Cq*(p:ℝ)^Aq*Real.exp (-cq*(p:ℝ)):=by positivity
    dsimp [E]
    simpa using (le_add_of_nonneg_left hn).trans hh
  have hroots:=hq heven m hm
  let q:=d.couplingCurve p
  have htheta:(q m,m)∈d.parameterWindow:=⟨⟨hroots.1.1.le,hroots.1.2.le⟩,hm⟩
  have hmass:=hf heven (q m,m) htheta
  have hvalue:|q m-ell m| ≤ E:=hroots.2.2.2.2.1.trans hEq
  have hE1:E ≤ 1:=(hsmall.trans_le (min_le_left _ _)).le
  have hbase:ContDiffAt ℝ ∞ (fun w:ℝ×ℝ=>(w.1-ell w.2)/2) (q m,m):=
    (contDiffAt_fst.sub ((d.ell_smooth m hm).comp (q m,m) contDiffAt_snd)).div_const 2
  have herr:ContDiffAt ℝ ∞ (fun w:ℝ×ℝ=>d.stationaryMassFunction p w-(w.1-ell w.2)/2)
      (q m,m):=hmass.1.sub hbase
  have hG:ContDiffAt ℝ ∞ (d.couplingMassResidual p) (q m,m):=herr.const_smul (2:ℝ)
  have hGj (i:ℕ) (hi:i ≤ 2):‖iteratedFDeriv ℝ i (d.couplingMassResidual p) (q m,m)‖ ≤ 2*E:=by
    change ‖iteratedFDeriv ℝ i (fun w:ℝ×ℝ=>(2:ℝ) •
      (d.stationaryMassFunction p w-(w.1-ell w.2)/2)) (q m,m)‖ ≤ 2*E
    rw [iteratedFDeriv_const_smul_apply' (herr.of_le (by simp)),norm_smul]
    norm_num only [Real.norm_eq_abs,abs_of_pos (show (0:ℝ) < 2 by norm_num)]
    exact mul_le_mul_of_nonneg_left ((hmass.2 i hi).trans hEf) (by norm_num)
  have hshape:(m,1+q m-ell m)∈Icc d.massLower 1×ˢIcc (0:ℝ) 2:=by
    refine ⟨hm,?_⟩
    have hab:=abs_le.mp (hvalue.trans hE1)
    constructor <;> linarith [hab.1,hab.2]
  have hloc:∀ᶠu in 𝓝 m,q u=ell u-d.couplingMassResidual p (q u,u):=by
    filter_upwards [hroots.2.2.2.1] with u hu
    dsimp only [couplingMassResidual]
    have hz:=hu.2
    change d.stationaryMassFunction p (q u,u)=0 at hz
    rw [hz]
    ring
  have hsm:2*(2*E)*D^2 ≤ 1/2:=by
    have hh:=hsmall.trans_le (min_le_right _ _)
    have hmul: E*(8*D^2) ≤ 1:=(le_div_iff₀ (by positivity : (0:ℝ) < 8*D^2)).mp hh.le
    nlinarith
  have hb:=scalar_root_C2_perturbation (d.ell_smooth m hm) hroots.2.2.1 hG
    (by positivity) hD hsm hloc hGj (fun i hi=>HD _ hshape i hi)
  have hbound:‖iteratedFDeriv ℝ j (fun u=>q u-ell u) m‖ ≤ (1+8*D^2)*E:=by
    interval_cases j
    · simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hvalue.trans
        (by nlinarith [mul_nonneg (show (0:ℝ) ≤ 8*D^2 by positivity) hE])
    · exact hb.1.trans (by nlinarith)
    · exact hb.2.trans (by nlinarith)
  exact hbound.trans_eq (by dsimp [E];ring)

end LimitingStandingData
end GeneralDepthPaper
