module

public import GeneralDepthPaper.StationaryMassC2

@[expose] public section


/-! The true mass response has a positive ordinary mass derivative on the
whole closed parameter window. The bound follows from its actual C²
convergence and the proved pressure-envelope slope. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 1400000
namespace LimitingStandingData
variable {Ξ:AdmissibleCovariance} {r:ℕ} {seed:AtomicPoint r}

theorem stationaryMassFunction_mass_partial_error
    (d:LimitingStandingData Ξ seed) (p:ℕ) (theta:ℝ×ℝ) (ht:theta∈d.parameterWindow)
    (hf:ContDiffAt ℝ ∞ (d.stationaryMassFunction p) theta)
    {ε:ℝ} (hε:‖iteratedFDeriv ℝ 1 (fun u:ℝ×ℝ=>d.stationaryMassFunction p u-
      (u.1-pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) u.2)/2) theta‖≤ε) :
    |fderiv ℝ (d.stationaryMassFunction p) theta (0,1)+
      deriv (pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture)) theta.2/2|≤ε := by
  let g:ℝ×ℝ→ℝ:=fun u=>(u.1-pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) u.2)/2
  have hg:ContDiffAt ℝ ∞ g theta :=
    (contDiffAt_fst.sub ((d.ell_smooth theta.2 ht.2).comp theta contDiffAt_snd)).div_const 2
  have hi:HasDerivAt (fun t:ℝ=>(theta.1,t)) (0,1) theta.2 :=
    (hasDerivAt_const theta.2 theta.1).prodMk (hasDerivAt_id theta.2)
  have hd:=((hf.sub hg).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt theta.2 hi
  have hdf:=((hf.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt theta.2 hi).sub
    (((d.ell_smooth theta.2 ht.2).differentiableAt (by simp)).hasDerivAt.const_sub theta.1 |>.div_const 2)
  have he:fderiv ℝ (fun u=>d.stationaryMassFunction p u-g u) theta (0,1)=
      fderiv ℝ (d.stationaryMassFunction p) theta (0,1)+
        deriv (pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture)) theta.2/2 := by
    have hh:=hd.unique hdf
    convert hh using 1 <;> ring
  rw [←he,←Real.norm_eq_abs]
  have hh:=(fderiv ℝ (fun u=>d.stationaryMassFunction p u-g u) theta).le_opNorm ((0,1):ℝ×ℝ)
  simp only [Prod.norm_def,Real.norm_eq_abs,abs_one,norm_zero,max_eq_right zero_le_one,mul_one] at hh
  exact hh.trans (by simpa only [norm_iteratedFDeriv_one] using hε)

theorem stationaryMassFunction_mass_partial_pos_eventually (d:LimitingStandingData Ξ seed) :
    ∀ᶠp:ℕ in atTop,∀he:Even p,∀theta∈d.parameterWindow,
      ContDiffAt ℝ ∞ (d.stationaryMassFunction p) theta ∧
      d.slope/2≤fderiv ℝ (d.stationaryMassFunction p) theta (0,1) := by
  obtain ⟨C,hC,A,c,hc,H⟩:=d.stationaryMassFunction_C2_exponential_error
  have Hsmall:∀ᶠp:ℕ in atTop,C*(p:ℝ)^A*Real.exp (-c*(p:ℝ))≤d.slope/2 :=
    (tendsto_nat_polynomial_exp C c A hc).eventually
      (eventually_le_nhds (half_pos d.slope_pos))
  filter_upwards [H,Hsmall] with p hp hsmall he theta ht
  have hf:=hp he theta ht
  have hh:=d.stationaryMassFunction_mass_partial_error p theta ht hf.1 (hf.2 1 (by norm_num))
  have hn:=neg_le_abs (fderiv ℝ (d.stationaryMassFunction p) theta (0,1)+
    deriv (pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture)) theta.2/2)
  exact ⟨hf.1,by linarith [d.ell_slope theta.2 ht.2]⟩

end LimitingStandingData
end GeneralDepthPaper
