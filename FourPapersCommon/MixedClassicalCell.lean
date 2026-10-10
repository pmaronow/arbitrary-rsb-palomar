module

public import FourPapersCommon.MixedColeHopf
public import FourPapersCommon.MixtureAnalysis
public import FRSB.BackwardsConstantTime

@[expose] public section


/-! The actual mixed Parisi equation in its original overlap coordinate on
every constant-CDF interval. No pointwise time differentiability is assumed. -/
noncomputable section
open Set Filter
open scoped Topology
namespace FourPapersCommon
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 64

theorem hasDerivAt_mixedPotential_constantCDF_time (ξ : AdmissibleEvenMixture)
    (μ : ParisiMeasure) {a b mass : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀s∈Ico a b,Paper.parisiCDF μ s=mass) {q : ℝ} (hq : q∈Ioo a b) (x : ℝ) :
    HasDerivAt (fun t=>mixedPotential ξ μ (t,x))
      (-(ξ.second q/2)*(mixedHessian ξ μ (q,x)+mass*mixedGradient ξ μ (q,x)^2)) q := by
  have haU : a∈Icc (0:ℝ) 1 := ⟨ha,hab.le.trans hb⟩
  have hbU : b∈Icc (0:ℝ) 1 := ⟨ha.trans hab.le,hb⟩
  have hqU : q∈Icc (0:ℝ) 1 := ⟨ha.trans hq.1.le,hq.2.le.trans hb⟩
  have hqC : ξ.clock q∈Ioo (ξ.clock a) (ξ.clock b) :=
    ⟨ξ.clock_strictMonoOn haU hqU hq.1,ξ.clock_strictMonoOn hqU hbU hq.2⟩
  have hclock : HasDerivAt ξ.clock (ξ.second q/ξ.variance) q :=
    ξ.hasDerivAt_clock (by rw [abs_of_nonneg hqU.1]; linarith [hqU.2])
  have hd:=(FRSB.hasDerivAt_parisiPotential_constantCDF_time (mixedBeta ξ) (mixedBeta_ne_zero ξ)
    (mixedMeasure ξ μ) (ξ.clock_mem_unitInterval haU).1
    (ξ.clock_strictMonoOn haU hbU hab) (ξ.clock_mem_unitInterval hbU).2
    (parisiCDF_mixedMeasure_constant_interval ξ μ haU hbU hc) hqC x).comp q hclock
  convert! hd using 1
  simp only [mixedHessian,mixedGradient,mixedBeta_sq]
  field_simp [ξ.variance_pos.ne']

end FourPapersCommon
