module

public import FourPapersCommon.AllFieldStateApproximation
public import FourPapersCommon.MixedMeasure
public import FRSB.GammaIdentity

@[expose] public section


/-! Uniform overlap-observable continuity for the actual same-Brownian
selected states, at every initial field. The bound uses the already proved
pathwise state estimate and actual bounded, Lipschitz PDE gradients. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FRSB
open scoped Topology NNReal
namespace FourPapersCommon
set_option maxHeartbeats 500000

def selectedMomentError (β : ℝ) (μ ν : Paper.ParisiMeasure) : ℝ :=
  2*(‖parisiGradientBCF β μ-parisiGradientBCF β ν‖+
    β^2*Real.exp (β^2)*(‖parisiGradientBCF β μ-parisiGradientBCF β ν‖+
      parisiCDFDistance μ ν))

theorem selectedMoment_sub_norm_le (β h : ℝ) (hβ : β≠0)
    (μ ν : Paper.ParisiMeasure) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    ‖selectedParisiSecondMoment β h hβ μ t-selectedParisiSecondMoment β h hβ ν t‖≤
      selectedMomentError β μ ν := by
  unfold selectedParisiSecondMoment selectedMomentError
  apply norm_integral_sq_sub_sq_le canonicalBrownianMeasure
    (fun ω=>fieldMagnetization β h hβ μ t ω)
    (fun ω=>fieldMagnetization β h hβ ν t ω)
  · exact (continuous_parisiGradient β μ).measurable.comp
      (measurable_const.prodMk (measurable_selectedParisiStateReal β h hβ μ t ht))
  · exact (continuous_parisiGradient β ν).measurable.comp
      (measurable_const.prodMk (measurable_selectedParisiStateReal β h hβ ν t ht))
  · intro ω; exact norm_parisiGradient_le_one β μ _
  · intro ω; exact norm_parisiGradient_le_one β ν _
  intro ω
  let x:=selectedParisiStateReal β h hβ μ ω t
  let y:=selectedParisiStateReal β h hβ ν ω t
  calc
    ‖fieldMagnetization β h hβ μ t ω-fieldMagnetization β h hβ ν t ω‖ ≤
      ‖parisiGradient β μ (t,x)-parisiGradient β ν (t,x)‖+
        ‖parisiGradient β ν (t,x)-parisiGradient β ν (t,y)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖parisiGradientBCF β μ-parisiGradientBCF β ν‖+‖x-y‖ := by
      apply add_le_add
      · exact norm_parisiSlabExtend_sub_le (by norm_num) _ _ _
      · simpa only [dist_eq_norm,NNReal.coe_one,one_mul] using
          (lipschitzWith_parisiGradient_all β ν t).dist_le_mul x y
    _ ≤ ‖parisiGradientBCF β μ-parisiGradientBCF β ν‖+
      β^2*Real.exp (β^2)*(‖parisiGradientBCF β μ-parisiGradientBCF β ν‖+
        parisiCDFDistance μ ν) :=
      add_le_add_right (selectedState_dist_le β h hβ μ ν ω ht) _

theorem tendsto_selectedMomentError_of_weak {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (β : ℝ) (μs : ι→Paper.ParisiMeasure)
    (μ : Paper.ParisiMeasure) (hμ : Tendsto μs L (𝓝 μ)) :
    Tendsto (fun i=>selectedMomentError β (μs i) μ) L (𝓝 0) := by
  have hg := (((continuous_gradientBCF β).tendsto μ).comp hμ).sub_const
    (parisiGradientBCF β μ) |>.norm
  have hc := tendsto_parisiCDFDistance_of_tendsto hμ
  simpa only [selectedMomentError,sub_self,norm_zero,mul_zero,add_zero,Function.comp_apply] using
    (hg.add ((hg.add hc).const_mul (β^2*Real.exp (β^2)))).const_mul 2

theorem tendstoUniformlyOn_selectedMoment_of_weak {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (β h : ℝ) (hβ : β≠0)
    (μs : ι→Paper.ParisiMeasure) (μ : Paper.ParisiMeasure)
    (hμ : Tendsto μs L (𝓝 μ)) :
    TendstoUniformlyOn (fun i=>selectedParisiSecondMoment β h hβ (μs i))
      (selectedParisiSecondMoment β h hβ μ) L (Icc (0:ℝ) 1) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(tendsto_selectedMomentError_of_weak β μs μ hμ).eventually
    (eventually_lt_nhds hε)] with i hi
  intro t ht
  simpa only [dist_eq_norm,norm_sub_rev] using (selectedMoment_sub_norm_le β h hβ (μs i) μ ht).trans_lt hi

theorem tendstoUniformlyOn_mixedGamma_of_weak {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μs : ι→Paper.ParisiMeasure) (μ : Paper.ParisiMeasure)
    (hμ : Tendsto μs L (𝓝 μ)) :
    TendstoUniformlyOn (fun i=>mixedGamma ξ h (μs i))
      (mixedGamma ξ h μ) L (Icc (0:ℝ) 1) := by
  have hu := tendstoUniformlyOn_selectedMoment_of_weak (mixedBeta ξ) h
    (mixedBeta_ne_zero ξ) (fun i=>mixedMeasure ξ (μs i)) (mixedMeasure ξ μ)
    (((continuous_mixedMeasure ξ).tendsto μ).comp hμ)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hu) ε hε] with i hi
  intro q hq
  exact hi (ξ.clock q) (ξ.clock_mem_unitInterval hq)

end FourPapersCommon
