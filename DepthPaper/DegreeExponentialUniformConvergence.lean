module

public import DepthPaper.StationaryCouplingC2

@[expose] public section


/-! Turning the verified degree-exponential estimates into literal
uniform convergence along the sufficiently large even degrees. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace DepthPaper
variable {X Y:Type*} [NormedAddCommGroup Y]

theorem tendstoUniformlyOn_of_degree_exponential_bound
    (f:ℕ→X→Y) (s:Set X) (C c:ℝ) (A:ℕ) (hc:0 < c)
    (H:∀ᶠp:ℕ in atTop,∀heven:Even p,∀x∈s,
      ‖f p x‖ ≤ C*(p:ℝ)^A*Real.exp (-c*(p:ℝ))) :
    TendstoUniformlyOn f (fun _=>0) (atTop⊓𝓟 {p:ℕ|Even p}) s := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have Hsmall:∀ᶠp:ℕ in atTop,C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) < ε:=
    (tendsto_nat_polynomial_exp C c A hc).eventually (eventually_lt_nhds hε)
  have H':∀ᶠp:ℕ in atTop⊓𝓟 {p:ℕ|Even p},∀x∈s,
      ‖f p x‖ ≤ C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) := by
    rw [eventually_inf_principal]
    exact H
  filter_upwards [H',Hsmall.filter_mono inf_le_left] with p hp hsmall x hx
  simpa only [dist_eq_norm,zero_sub,norm_neg] using (hp x hx).trans_lt hsmall

namespace LimitingStandingData
variable {Ξ:AdmissibleCovariance} {r:ℕ} {seed:AtomicPoint r}

theorem stationaryBranch_C2_uniform_limit (d:LimitingStandingData Ξ seed) (j:ℕ) (hj:j ≤ 2):
    TendstoUniformlyOn (fun p theta=>iteratedFDeriv ℝ j
      (fun u=>d.stationaryBranch p u-d.branch u.2) theta) (fun _=>0)
      (atTop⊓𝓟 {p:ℕ|Even p}) d.parameterWindow := by
  obtain ⟨C,hC,A,c,hc,H⟩:=d.stationaryBranch_C2_exponential_error
  apply tendstoUniformlyOn_of_degree_exponential_bound _ _ C c A hc
  exact H.mono (fun _ hp heven theta ht=>hp heven theta ht j hj)

theorem stationaryMassFunction_C2_uniform_limit (d:LimitingStandingData Ξ seed) (j:ℕ) (hj:j ≤ 2):
    TendstoUniformlyOn (fun p theta=>iteratedFDeriv ℝ j
      (fun u:ℝ×ℝ=>d.stationaryMassFunction p u-
        (u.1-pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) u.2)/2) theta)
      (fun _=>0) (atTop⊓𝓟 {p:ℕ|Even p}) d.parameterWindow := by
  obtain ⟨C,hC,A,c,hc,H⟩:=d.stationaryMassFunction_C2_exponential_error
  apply tendstoUniformlyOn_of_degree_exponential_bound _ _ C c A hc
  exact H.mono (fun _ hp heven theta ht=>(hp heven theta ht).2 j hj)

theorem couplingCurve_C2_uniform_limit (d:LimitingStandingData Ξ seed) (j:ℕ) (hj:j ≤ 2):
    TendstoUniformlyOn (fun p m=>iteratedFDeriv ℝ j (fun u=>d.couplingCurve p u-
      pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) u) m) (fun _=>0)
      (atTop⊓𝓟 {p:ℕ|Even p}) (Icc d.massLower 1) := by
  obtain ⟨C,hC,A,c,hc,H⟩:=d.couplingCurve_C2_exponential_error
  apply tendstoUniformlyOn_of_degree_exponential_bound _ _ C c A hc
  exact H.mono (fun _ hp heven m hm=>hp heven m hm j hj)

theorem couplingCurve_critical_limit (d:LimitingStandingData Ξ seed):
    Tendsto (fun p=>d.couplingCurve p 1) (atTop⊓𝓟 {p:ℕ|Even p})
      (𝓝 (pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) 1)) := by
  obtain ⟨C,hC,A,c,hc,H⟩:=d.couplingCurve_eventually
  have hzero:=tendstoUniformlyOn_of_degree_exponential_bound
    (fun p m=>d.couplingCurve p m-pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) m)
    (Icc d.massLower 1) C c A hc
    (H.mono (fun _ hp heven m hm=>by
      simpa only [Real.norm_eq_abs] using (hp heven m hm).2.2.2.2.1))
  have hh:=hzero.tendsto_at (show (1:ℝ)∈Icc d.massLower 1 from ⟨d.massLower_mem.2.le,le_rfl⟩)
  have hadd:=hh.add_const (pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) 1)
  simpa only [sub_add_cancel,zero_add] using hadd

end LimitingStandingData
end DepthPaper
