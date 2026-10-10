module

public import FRSB.CurvatureIdentity
public import FRSB.MomentQuotient

@[expose] public section


/-! The actual second self-consistency derivative, including its exact
constant-mass expression on any open physical interval. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped Topology
namespace FRSB

 def GammaSecond (β:ℝ) (μ:ParisiMeasure) (s:ℝ) : ℝ :=
  β^4*(quotientNumerator β μ s-2*parisiCDF μ s*quotientDenominator β μ s)

 theorem GammaSecond_eq_integral (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    {s:ℝ} (hs:s∈Icc (0:ℝ) 1) :
    GammaSecond β μ s=β^4*(∫ ω, D β μ s ω ^ 2-2*parisiCDF μ s*C β μ s ω ^ 3
      ∂canonicalBrownianMeasure) := by
  unfold GammaSecond quotientNumerator quotientDenominator
  simp only [quotientNumeratorPolynomial,quotientDenominatorPolynomial,moment_X_pow]
  rw [integral_sub (integrable_jetProcess_pow β hβ μ 2 2 hs)
    ((integrable_jetProcess_pow β hβ μ 1 3 hs).const_mul (2*parisiCDF μ s)),integral_const_mul]

 theorem continuousAt_CDF_of_constant_on_Ioo (μ:ParisiMeasure) (m a b:ℝ)
    (hCDF:∀s∈Ioo a b,parisiCDF μ s=m) {s:ℝ} (hs:s∈Ioo a b) :
    ContinuousAt (parisiCDF μ) s := by
  apply continuousAt_const.congr
  filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
  exact (hCDF t ht).symm

 theorem hasDerivAt_GammaPrime_of_constant_CDF (β:ℝ) (hβ:β≠0)
    (μ:ParisiMeasure) (m a b:ℝ) (hI:Ioo a b⊆Ioo (0:ℝ) 1)
    (hCDF:∀s∈Ioo a b,parisiCDF μ s=m) {s:ℝ} (hs:s∈Ioo a b) :
    HasDerivAt (GammaPrime β μ) (GammaSecond β μ s) s := by
  rw [GammaSecond_eq_integral β hβ μ ⟨(hI hs).1.le,(hI hs).2.le⟩]
  exact hasDerivAt_GammaPrime_of_continuousAt_CDF β hβ μ (hI hs)
    (continuousAt_CDF_of_constant_on_Ioo μ m a b hCDF hs)

 theorem GammaSecond_eq_constant_mass (β:ℝ) (μ:ParisiMeasure) (m a b:ℝ)
    (hCDF:∀s∈Ioo a b,parisiCDF μ s=m) {s:ℝ} (hs:s∈Ioo a b) :
    GammaSecond β μ s=β^4*(quotientNumerator β μ s-2*m*quotientDenominator β μ s) := by
  simp only [GammaSecond,hCDF s hs]

 theorem continuousOn_GammaSecond_of_constant_CDF (β:ℝ) (hβ:β≠0)
    (μ:ParisiMeasure) (m a b:ℝ) (hI:Ioo a b⊆Ioo (0:ℝ) 1)
    (hCDF:∀s∈Ioo a b,parisiCDF μ s=m) : ContinuousOn (GammaSecond β μ) (Ioo a b) := by
  have hm:Ioo a b⊆Icc (0:ℝ) 1 :=fun t ht=>⟨(hI ht).1.le,(hI ht).2.le⟩
  have hc : ContinuousOn (fun s=>β^4*(quotientNumerator β μ s-
      (2*m)*quotientDenominator β μ s)) (Ioo a b) :=
    continuousOn_const.mul (((continuousOn_quotientNumerator β hβ μ).mono hm).sub
      (continuousOn_const.mul ((continuousOn_quotientDenominator β hβ μ).mono hm)))
  apply hc.congr
  intro s hs
  exact GammaSecond_eq_constant_mass β μ m a b hCDF hs

end FRSB
