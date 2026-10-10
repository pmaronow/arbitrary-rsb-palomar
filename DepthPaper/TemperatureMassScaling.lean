module

public import DepthPaper.TemperatureMassMoments
public import DepthPaper.TemperatureMassUnique
public import DepthPaper.TemperatureMassRecursion
public import DepthPaper.ScaledLogCoshJetBounds

@[expose] public section


/-! Lemma 3.1, with the actual selected mixed potential, actual diffusion,
and literal terminal ψ. The theorem is stronger than the atomic statement:
the same conclusions hold for any probability measure supported below qc. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace DepthPaper
open FourPapersCommon Paper ColeHopfFoundation.ProbabilityTheory

theorem temperature_mass_scaling (Ξ : AdmissibleCovariance) (ν : ParisiMeasure)
    (m : ℝ) (hm : 0 < m) (qc : ℝ) (hc : qc∈Icc (0:ℝ) 1)
    (hs : ∀q∈FRSB.parisiSupport ν,q≤qc) :
    (∀x,temperatureMassPotential Ξ ν m qc qc x=m⁻¹*Real.log (Real.cosh (m*x))) ∧
    (∀q∈Icc (0:ℝ) qc,∀x,HasDerivAt (temperatureMassPotential Ξ ν m qc q)
      (temperatureMassGradient Ξ ν m q x) x) ∧
    (∀a b mass,0≤a→a<b→b≤qc→(∀s∈Ico a b,parisiCDF ν s=mass)→
      ∀q∈Ioo a b,∀x,HasDerivAt (fun t=>temperatureMassPotential Ξ ν m qc t x)
        (-Ξ.second q/2*(temperatureMassHessian Ξ ν m q x+
          m*mass*temperatureMassGradient Ξ ν m q x^2)) q) ∧
    (∀a b mass,0≤a→a<b→b≤qc→(∀s∈Ico a b,parisiCDF ν s=mass)→∀x,
      temperatureMassPotential Ξ ν m qc a x=
        coleHopf (m*mass) (Ξ.first b-Ξ.first a).toNNReal
          (temperatureMassPotential Ξ ν m qc b) x) ∧
    (∀q:ℝ≥0,(q:ℝ)≤qc→∀ω,temperatureMassState Ξ ν m hm q ω=
      canonicalBrownian (Ξ.first q).toNNReal ω+
        ∫s in (0:ℝ)..(q:ℝ),Ξ.second s*m*parisiCDF ν s*
          temperatureMassGradient Ξ ν m s (temperatureMassState Ξ ν m hm s.toNNReal ω)) ∧
    (∀ω (X:ℝ→ℝ),Continuous X→
      (∀t∈Icc (0:ℝ) qc,X t=canonicalBrownian (Ξ.first t).toNNReal ω+
        ∫s in (0:ℝ)..t,Ξ.second s*m*parisiCDF ν s*temperatureMassGradient Ξ ν m s (X s))→
      ∀t∈Icc (0:ℝ) qc,X t=temperatureMassState Ξ ν m hm t.toNNReal ω) ∧
    (∀q∈Icc (0:ℝ) qc,temperatureMassGamma Ξ ν m hm q=
      Gamma ((temperatureCovarianceFamily Ξ).covariance m) ν q) ∧
    (∀q∈Icc (0:ℝ) qc,(1/2:ℝ)*(∫s in (0:ℝ)..q,
      Ξ.second s*(temperatureMassGamma Ξ ν m hm s-s))=
        (m^2)⁻¹*firstVariation ((temperatureCovarianceFamily Ξ).covariance m) ν q) ∧
    LipschitzWith 1 (fun x=>m⁻¹*Real.log (Real.cosh (m*x))) ∧
    m⁻¹*Real.log (Real.cosh (m*0))=0 ∧
    (∀I:Set ℝ,IsCompact I→I⊆Ioi (0:ℝ)→∀j k:ℕ,
      ∃C:ℝ,0≤C ∧ ∀a∈I,∀x:ℝ,
        ‖iteratedDeriv k (fun b=>iteratedDeriv (j+1)
          (fun y=>b⁻¹*Real.log (Real.cosh (b*y))) x) a‖≤C) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro x
    rw [temperatureMassPotential_terminal Ξ ν m hm hc hs,
      terminalValue_scaledLogCoshTerminal_all]
  · intro q hq x
    exact hasDerivAt_temperatureMassPotential_spatial Ξ ν m hm qc q x
      ⟨hq.1,hq.2.trans hc.2⟩
  · intro a b mass ha hab hb hCDF q hq x
    exact hasDerivAt_temperatureMassPotential_time Ξ ν m hm qc ha hab (hb.trans hc.2) hCDF hq x
  · intro a b mass ha hab hb hCDF x
    exact temperatureMassPotential_coleHopf Ξ ν m hm qc
      ⟨ha,hab.le.trans (hb.trans hc.2)⟩ ⟨ha.trans hab.le,hb.trans hc.2⟩ hab hCDF x
  · intro q hq ω
    exact temperatureMassState_integral_equation Ξ ν m hm q (hq.trans hc.2) ω
  · intro ω X hX heq
    exact temperatureMassState_unique Ξ ν m hm qc hc ω X hX heq
  · intro q hq
    exact temperature_mass_Gamma Ξ ν m hm ⟨hq.1,hq.2.trans hc.2⟩
  · intro q hq
    exact temperature_mass_firstVariation Ξ ν m hm ⟨hq.1,hq.2.trans hc.2⟩
  · simpa only [funext (terminalValue_scaledLogCoshTerminal_all m)] using
      lipschitzWith_scaledLogCoshTerminal m
  · simp only [mul_zero,Real.cosh_zero,Real.log_one]
  · exact scaledLogCosh_literal_mixed_uniform_bound

end DepthPaper
