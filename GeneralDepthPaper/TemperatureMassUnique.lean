module

public import GeneralDepthPaper.TemperatureMassState

@[expose] public section


/-! Pathwise uniqueness for every continuous solution of the literal
temperature–mass integral equation, on every truncated physical interval. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace GeneralDepthPaper
open FourPapersCommon Paper
set_option maxHeartbeats 800000

theorem temperatureMassState_unique (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (m : ℝ) (hm : 0 < m) (qc : ℝ) (hc : qc∈Icc (0:ℝ) 1)
    (ω : BrownianSample) (X : ℝ→ℝ) (hX : Continuous X)
    (heq : ∀t∈Icc (0:ℝ) qc,X t=canonicalBrownian (Ξ.first t).toNNReal ω+
      ∫s in (0:ℝ)..t,Ξ.second s*m*parisiCDF μ s*temperatureMassGradient Ξ μ m s (X s)) :
    ∀t∈Icc (0:ℝ) qc,X t=temperatureMassState Ξ μ m hm t.toNNReal ω := by
  let d:=temperatureMassDriftData Ξ μ m hm
  let c:=covarianceRateData Ξ
  let W:=rateNoiseReal c ω
  have hW : Continuous W:=continuous_rateNoiseReal c ω
  have hn {t : ℝ} (ht : t∈Icc (0:ℝ) qc) : W t=canonicalBrownian (Ξ.first t).toNNReal ω := by
    dsimp only [W,rateNoiseReal,timeChangedBrownian]
    congr 1
    apply NNReal.coe_injective
    rw [covarianceRateData_clock Ξ t.toNNReal
      (by rw [Real.coe_toNNReal _ ht.1];exact ht.2.trans hc.2),
      Real.coe_toNNReal _ ht.1,Real.coe_toNNReal _ (Ξ.first_nonneg ht.1)]
  have hx : ∀t∈Icc (0:ℝ) qc,X t=0+W t+∫s in (0:ℝ)..t,d.coefficient s*d.gradient s (X s) := by
    intro t ht
    rw [zero_add,hn ht,heq t ht]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    have hsU : s∈Icc (0:ℝ) 1:=⟨hs.1,hs.2.trans (ht.2.trans hc.2)⟩
    simp only [d,temperatureMassDriftData,projIcc_of_mem (by norm_num : (0:ℝ)≤1) hsU]
    ring
  have hxu:=additiveStateReal_unique d 0 qc hc.1 W hW X hX hx
  let Y:=clockedStateReal d c 0 1 (by norm_num) ω
  have hyu:=additiveStateReal_unique d 0 qc hc.1 W hW Y
    (continuous_clockedStateReal d c 0 1 (by norm_num) ω)
    (fun t ht=>clockedStateReal_integral_equation d c 0 1 (by norm_num) ω
      ⟨ht.1,ht.2.trans hc.2⟩)
  intro t ht
  have he : X t=Y t:=(hxu ht).trans (hyu ht).symm
  rw [he]
  dsimp only [temperatureMassState]
  rw [clockedItoState_eq _ _ _ _ _
    (by rw [Real.coe_toNNReal _ ht.1];exact ht.2.trans hc.2),Real.coe_toNNReal _ ht.1]

end GeneralDepthPaper
