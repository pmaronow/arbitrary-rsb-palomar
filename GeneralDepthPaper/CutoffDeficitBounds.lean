module

public import GeneralDepthPaper.CutoffSplitting
public import GeneralDepthPaper.StateCompactMass
public import GeneralDepthPaper.DoobEndpointAverageBounds

@[expose] public section


/-! Genuine selected-diffusion endpoint bounds, with every state-law and
compact-mass input discharged from the actual covariance and cutoff. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace GeneralDepthPaper
open FourPapersCommon
set_option maxHeartbeats 1000000

theorem cutoff_endpoint_deficit_bounds (Ξ:AdmissibleCovariance) {r:ℕ}
    (z:AtomicPoint r) (hz:IsAtomicPoint z) (m:ℝ) (hm:m∈Ioc (0:ℝ) 1)
    (Q:Overlap) (qc:ℝ) (hc:atomicLocation z (Fin.last r) < qc)
    (hqcQ:qc < (Q:ℝ)) {B:ℝ} (hB:0≤B) (hvar:Ξ.first qc≤B)
    (hW:1≤Ξ.first Q-Ξ.first qc) :
    (1/4)*doobCompactLowerConstant (3*B+2)*
        (Real.sqrt (2*Real.pi*(Ξ.first Q-Ξ.first qc)))⁻¹*
        Real.exp (-m^2*(Ξ.first Q-Ξ.first qc)/2)≤
      1-Gamma Ξ (twoLevelMeasure z hz m Q) Q ∧
    1-Gamma Ξ (twoLevelMeasure z hz m Q) Q≤
      8*(Real.sqrt (2*Real.pi*(Ξ.first Q-Ξ.first qc)))⁻¹*
        Real.exp (-m^2*(Ξ.first Q-Ξ.first qc)/2) := by
  let ν:=twoLevelMeasure z hz m Q
  let ρ:=Paper.canonicalBrownianMeasure.map (fun sample=>optimalState Ξ ν sample qc)
  have hqu:qc∈Icc (0:ℝ) 1:=⟨(cutoff_pos z hz qc hc).le,hqcQ.le.trans Q.property.2⟩
  have hmeas:Measurable (fun sample=>optimalState Ξ ν sample qc):=
    measurable_mixedState Ξ.toEvenMixture 0 ν hqu
  letI:IsProbabilityMeasure ρ:=(Measure.isProbabilityMeasure_map_iff hmeas.aemeasurable).mpr inferInstance
  let W:ℝ≥0:=(Ξ.first Q-Ξ.first qc).toNNReal
  have hWreal:(W:ℝ)=Ξ.first Q-Ξ.first qc:=Real.coe_toNNReal _ (by linarith)
  have hWone:1≤(W:ℝ):=hWreal.symm ▸ hW
  have hWne:W≠0:=by intro hh;rw [hh] at hWone;norm_num at hWone
  have hR:0≤3*B+2:=by linarith
  have hmass:(1/2:ℝ)≤ρ.real (Icc (-(3*B+2)) (3*B+2)) := by
    dsimp only [ρ]
    rw [map_measureReal_apply hmeas measurableSet_Icc]
    have he:(fun sample=>optimalState Ξ ν sample qc)⁻¹' Icc (-(3*B+2)) (3*B+2)=
        {sample:BrownianSample | |optimalState Ξ ν sample qc|≤3*B+2}:=by
      ext sample
      exact abs_le.symm
    rw [he]
    exact optimalState_compact_mass Ξ ν hqu hB hvar
  have hlo:=terminalEndpointDeficit_average_lower hm.1 hm.2 hR W hWone ρ hmass
  have hup:=terminalEndpointDeficit_average_upper hm.1 hm.2 W hWne ρ
  have he:1-Gamma Ξ ν Q=∫x,terminalEndpointDeficit m W x ∂ρ:=
    (cutoff_splitting_at Ξ Ξ z hz m hm Q qc hc hqcQ).endpoint_deficit
  rw [he]
  exact ⟨by simpa only [hWreal] using hlo,by simpa only [hWreal] using hup⟩

end GeneralDepthPaper
