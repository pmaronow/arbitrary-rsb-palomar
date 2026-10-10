module

public import GeneralDepthPaper.RevisedSectionFourEnvelope
public import GeneralDepthPaper.RevisedSectionFourScalar

@[expose] public section

/-! Exact full-parameter envelope and optimized-value C³ checks for revised
Proposition 4.5(ii), on its symmetric closed parameter window. The actual
stationary objective and the literal limiting pressure expression appear
in the targets. These are statements under actual `LimitingStandingData`;
the seed-to-standing-data construction is verified separately. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Verification.OptimizedValueTargets
variable {Ξ : GeneralDepthPaper.AdmissibleCovariance} {r : ℕ}
  {seed : GeneralDepthPaper.AtomicPoint r}

theorem prop4_5_full_parameter_envelope
    (d : GeneralDepthPaper.LimitingStandingData Ξ seed) :
    ∀ᶠp : ℕ in atTop,∀_heven : Even p,∀θ∈d.revisedParameterWindow,
      HasFDerivAt
        (fun u : ℝ×ℝ=>GeneralDepthPaper.stationaryReducedObjective Ξ p
          d.cutoff d.stripRateLower d.stripRateUpper (u,d.stationaryBranch p u))
        ((fderiv ℝ (GeneralDepthPaper.stationaryReducedObjective Ξ p
          d.cutoff d.stripRateLower d.stripRateUpper) (θ,d.stationaryBranch p θ)).comp
            (ContinuousLinearMap.inl ℝ (ℝ×ℝ) (GeneralDepthPaper.AtomicPoint r))) θ := by
  filter_upwards [d.revisedScalarObjective_fullDerivative_eventually] with p hp heven θ hθ
  exact hp heven θ (d.revisedParameterWindow_subset hθ)

theorem prop4_5_optimized_value_C3
    (d : GeneralDepthPaper.LimitingStandingData Ξ seed) :
    ∀j : ℕ,j≤3 →
      TendstoUniformlyOn
        (fun p θ=>iteratedFDeriv ℝ j
          (fun u : ℝ×ℝ=>GeneralDepthPaper.stationaryReducedObjective Ξ p
            d.cutoff d.stripRateLower d.stripRateUpper (u,d.stationaryBranch p u)-
              (GeneralDepthPaper.scaledThermodynamicPressure Ξ.toEvenMixture u.2/u.2+
                u.1*u.2/2)) θ)
        (fun _=>0) (atTop⊓𝓟 {p : ℕ|Even p}) d.revisedParameterWindow := by
  intro j hj
  simpa only [GeneralDepthPaper.LimitingStandingData.revisedScalarObjective,
    GeneralDepthPaper.revisedLimitingScalarObjective,GeneralDepthPaper.limitingPressureObjective]
    using (d.revisedScalarObjective_C3_uniform_limit j hj).mono d.revisedParameterWindow_subset

theorem prop4_5_optimized_value_C3_exponential
    (d : GeneralDepthPaper.LimitingStandingData Ξ seed) :
    ∃C : ℝ,0<C ∧ ∃A : ℕ,∃c : ℝ,0<c ∧
      ∀ᶠp : ℕ in atTop,∀_heven : Even p,∀θ∈d.revisedParameterWindow,
        ContDiffAt ℝ ∞ (fun u : ℝ×ℝ=>GeneralDepthPaper.stationaryReducedObjective Ξ p
          d.cutoff d.stripRateLower d.stripRateUpper (u,d.stationaryBranch p u)) θ ∧
        ∀j : ℕ,j≤3 → ‖iteratedFDeriv ℝ j
          (fun u : ℝ×ℝ=>GeneralDepthPaper.stationaryReducedObjective Ξ p
            d.cutoff d.stripRateLower d.stripRateUpper (u,d.stationaryBranch p u)-
              (GeneralDepthPaper.scaledThermodynamicPressure Ξ.toEvenMixture u.2/u.2+
                u.1*u.2/2)) θ‖≤C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) := by
  obtain ⟨C,hC,A,c,hc,H⟩ := d.revisedScalarObjective_C3_exponential_error
  refine ⟨C,hC,A,c,hc,?_⟩
  filter_upwards [H] with p hp heven θ hθ
  exact hp heven θ (d.revisedParameterWindow_subset hθ)

end Verification.OptimizedValueTargets
