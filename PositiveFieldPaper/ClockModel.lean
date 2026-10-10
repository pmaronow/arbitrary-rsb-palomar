module

public import PositiveFieldPaper.PolynomialMoments
public import Mathlib.Probability.BrownianMotion.Basic

@[expose] public section


/-! Literal Brownian diffusion and Parisi functional in the paper's physical
 clock. The driving process is proved to be standard Brownian. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper
open scoped Topology NNReal
namespace PositiveFieldPaper

 def paperBrownian (β:ℝ) (t:ℝ≥0) (sample:BrownianSample):ℝ:=
  β*canonicalBrownian ((β^2)⁻¹.toNNReal*t) sample

 theorem isBrownianReal_paperBrownian (β:ℝ) (hβ:0<β) :
    IsBrownianReal (paperBrownian β) brownianMeasure := by
  have hc:((β^2)⁻¹.toNNReal:ℝ)=(β^2)⁻¹:=Real.coe_toNNReal _ (inv_nonneg.mpr (sq_nonneg β))
  have hc0:(β^2)⁻¹.toNNReal≠0:=by
    intro h
    have he:=congrArg (fun r:ℝ≥0=>(r:ℝ)) h
    rw [hc,NNReal.coe_zero] at he
    exact inv_ne_zero (pow_ne_zero 2 hβ.ne') he
  have he:(Real.sqrt ((β^2)⁻¹.toNNReal:ℝ))⁻¹=β:=by
    rw [hc,Real.sqrt_inv,Real.sqrt_sq hβ.le,inv_inv]
  have hh:=isBrownianReal_canonicalBrownian.smul hc0
  change IsBrownianReal (fun t sample=>β*canonicalBrownian ((β^2)⁻¹.toNNReal*t) sample) canonicalBrownianMeasure
  simpa only [he] using hh

 theorem paperBrownian_at_real (β:ℝ) {t:ℝ} (ht:0≤t) (sample:BrownianSample) :
    paperBrownian β t.toNNReal sample=β*canonicalBrownian (t/β^2).toNNReal sample := by
  unfold paperBrownian
  congr 1
  congr 1
  apply NNReal.coe_injective
  simp only [NNReal.coe_mul,Real.coe_toNNReal _ ht,
    Real.coe_toNNReal _ (inv_nonneg.mpr (sq_nonneg β)),Real.coe_toNNReal _ (div_nonneg ht (sq_nonneg β))]
  ring

 theorem Y_eq_real_state (β h:ℝ) (hβ:β≠0) (ν:ParisiMeasure) {t:ℝ}
    (ht:t∈Icc (0:ℝ) (L β)) (sample:BrownianSample) :
    Y β h hβ ν t sample=selectedParisiStateReal β h hβ ν sample (t/β^2) := by
  have hs:=overlapTime_mem hβ ht
  unfold Y
  rw [selectedParisiItoState_eq β h hβ ν
    (by simpa only [Real.coe_toNNReal _ hs.1] using hs.2),
    Real.coe_toNNReal _ hs.1]

 theorem optimal_diffusion_integral_equation (β h:ℝ) (hβ:β≠0) (ν:ParisiMeasure) {t:ℝ}
    (ht:t∈Icc (0:ℝ) (L β)) (sample:BrownianSample) :
    Y β h hβ ν t sample=h+paperBrownian β t.toNNReal sample+
      ∫r in (0:ℝ)..t,mass β ν r*B β ν r (Y β h hβ ν r sample) := by
  have hs:=overlapTime_mem hβ ht
  have hh:=selectedParisiState_integral_equation β h hβ ν sample hs
  rw [←Y_eq_real_state β h hβ ν ht sample,←paperBrownian_at_real β ht.1 sample] at hh
  have hint:(∫r in (0:ℝ)..(t/β^2),β^2*parisiCDF ν r*
      parisiGradient β ν (r,selectedParisiStateReal β h hβ ν sample r))=
      ∫r in (0:ℝ)..t,mass β ν r*B β ν r (Y β h hβ ν r sample) := by
    let f:ℝ→ℝ:=fun r=>parisiCDF ν r*parisiGradient β ν (r,selectedParisiStateReal β h hβ ν sample r)
    have he:(∫r in (0:ℝ)..t,mass β ν r*B β ν r (Y β h hβ ν r sample))=
        ∫r in (0:ℝ)..t,f (r/β^2) := by
      apply intervalIntegral.integral_congr_Ioo_of_le ht.1
      intro r hr
      have hrI:r∈Icc (0:ℝ) (L β):=⟨hr.1.le,hr.2.le.trans ht.2⟩
      simp only [mass,B_eq_gradient β hβ ν r _ hrI,Y_eq_real_state β h hβ ν hrI sample,f]
    rw [he,intervalIntegral.integral_comp_div f (pow_ne_zero 2 hβ),zero_div,smul_eq_mul,
      ←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r _
    dsimp only [f]
    ring
  rwa [hint] at hh

 theorem parisi_functional_paper_clock (β h:ℝ) (hβ:β≠0) (ν:ParisiMeasure) :
    parisiFunctional β h ν=Real.log 2+U β ν 0 h-
      (1/(2*L β))*∫t in (0:ℝ)..L β,t*mass β ν t := by
  unfold parisiFunctional parisiPDEFunctional Paper.parisiFunctional U
  simp only [zero_div]
  have he:β^2/2*(∫q in (0:ℝ)..1,q*parisiCDF ν q)=
      (1/(2*L β))*∫t in (0:ℝ)..L β,t*mass β ν t := by
    unfold L mass
    have hh:=intervalIntegral.integral_comp_div (fun q:ℝ=>q*parisiCDF ν q)
      (a:=0) (b:=β^2) (c:=β^2) (pow_ne_zero 2 hβ)
    simp only [zero_div,div_self (pow_ne_zero 2 hβ),smul_eq_mul] at hh
    have hg:(∫t in (0:ℝ)..β^2,t*parisiCDF ν (t/β^2))=
        β^2*(∫t in (0:ℝ)..β^2,(t/β^2)*parisiCDF ν (t/β^2)):=by
      rw [←intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      field_simp [hβ]
    rw [hg,hh]
    field_simp [hβ]
  rw [he]

end PositiveFieldPaper
