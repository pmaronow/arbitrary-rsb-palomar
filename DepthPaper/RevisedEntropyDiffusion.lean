module

public import DepthPaper.RevisedEntropyColeHopf
public import FourPapersCommon.MixedColeHopf
public import FRSB.ConstantMassLaw

@[expose] public section

/-! Exact bounded-observable transport for the actual mixed Parisi diffusion,
in the paper's original overlap coordinate. The variance-clock conversion
does not exclude a quadratic covariance term. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal

namespace DepthPaper
open FourPapersCommon
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

theorem revisedMixedState_eq_ItoState (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : ParisiMeasure) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    (ω : BrownianSample) :
    Paper.selectedParisiItoState (mixedBeta ξ) h (mixedBeta_ne_zero ξ)
      (mixedMeasure ξ μ) (ξ.clock q).toNNReal ω = mixedState ξ h μ ω q := by
  rw [Paper.selectedParisiItoState_eq _ _ _ _
    (by simpa only [Real.coe_toNNReal _ (ξ.clock_mem_unitInterval hq).1]
      using (ξ.clock_mem_unitInterval hq).2)]
  rw [Real.coe_toNNReal _ (ξ.clock_mem_unitInterval hq).1]
  rfl

theorem revisedMixedState_constantCDF_expectation
    (ξ : AdmissibleEvenMixture) (h : ℝ) (μ : ParisiMeasure)
    {a b m : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hab : a < b) (hc : ∀ q ∈ Ico a b, Paper.parisiCDF μ q = m)
    (ψ : ℝ → ℝ) (hψ : Measurable ψ) (C : ℝ) (hψb : ∀ x, ‖ψ x‖ ≤ C) :
    (∫ ω, ψ (mixedState ξ h μ ω b) ∂Paper.canonicalBrownianMeasure) =
      ∫ ω, (∫ y, ψ y ∂FRSB.constantMassKernel m
        (ξ.first b - ξ.first a).toNNReal (fun y => mixedPotential ξ μ (b, y))
        (mixedState ξ h μ ω a)) ∂Paper.canonicalBrownianMeasure := by
  let A := (ξ.clock a).toNNReal
  let T := (ξ.clock b - ξ.clock a).toNNReal
  have hclock : ξ.clock a < ξ.clock b := ξ.clock_strictMonoOn ha hb hab
  have hA : (A : ℝ) = ξ.clock a :=
    Real.coe_toNNReal _ (ξ.clock_mem_unitInterval ha).1
  have hT : (T : ℝ) = ξ.clock b - ξ.clock a :=
    Real.coe_toNNReal _ (sub_nonneg.mpr hclock.le)
  have hTpos : 0 < T := by
    exact_mod_cast (show (0 : ℝ) < (T : ℝ) by rw [hT]; linarith)
  have hsum : (A : ℝ) + T = ξ.clock b := by rw [hA, hT]; ring
  have hsumNN : A + T = (ξ.clock b).toNNReal := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add, hsum,
      Real.coe_toNNReal _ (ξ.clock_mem_unitInterval hb).1]
  have hinterval : ∀ s ∈ Ico (A : ℝ) ((A : ℝ) + T),
      Paper.parisiCDF (mixedMeasure ξ μ) s = m := by
    rw [hsum, hA]
    exact parisiCDF_mixedMeasure_constant_interval ξ μ ha hb hc
  have H := FRSB.selectedParisiState_constantMass_weighted_borel
    (mixedBeta ξ) h (mixedBeta_ne_zero ξ) (mixedMeasure ξ μ) A T hTpos
    (by rw [hsum]; exact (ξ.clock_mem_unitInterval hb).2) m hinterval
    ψ hψ C hψb (fun _ => 1) stronglyMeasurable_const 1 (by intro ω; norm_num)
  simp only [one_mul] at H
  rw [hsumNN] at H
  have hstateA (ω : BrownianSample) :
      Paper.selectedParisiItoState (mixedBeta ξ) h (mixedBeta_ne_zero ξ)
        (mixedMeasure ξ μ) A ω = mixedState ξ h μ ω a := by
    exact revisedMixedState_eq_ItoState ξ h μ ha ω
  simp_rw [revisedMixedState_eq_ItoState ξ h μ hb,
    hstateA] at H
  have hvariance : mixedBeta ξ ^ 2 * (T : ℝ) = ξ.first b - ξ.first a := by
    rw [mixedBeta_sq, hT]
    unfold AdmissibleEvenMixture.clock
    field_simp [ξ.variance_pos.ne']
  have hkernel : FRSB.parisiConstantMassKernel (mixedBeta ξ) (mixedMeasure ξ μ)
      A T m = FRSB.constantMassKernel m (ξ.first b - ξ.first a).toNNReal
        (fun y => mixedPotential ξ μ (b, y)) := by
    unfold FRSB.parisiConstantMassKernel
    rw [hsum, hvariance]
    rfl
  rw [hkernel] at H
  exact H

end DepthPaper
