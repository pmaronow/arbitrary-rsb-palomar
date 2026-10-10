module

public import FRSB.PolynomialMomentContinuity
public import FRSB.DiffusionApproximation
public import FRSB.UniformSpatialRegularity

@[expose] public section


/-! Uniform weak-measure convergence of the actual polynomial moments. The
jets and the same-Brownian states both vary with the overlap measure. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter MvPolynomial
open scoped Topology BigOperators
namespace FRSB
open Paper
set_option maxHeartbeats 1000000

def uniformPolynomialMomentBound (β : ℝ) (f : MomentPolynomial) : ℝ :=
  ∑ d ∈ f.support, ‖f.coeff d‖ * ∏ j ∈ d.support, uniformSpatialConstant β j ^ d j

theorem uniformPolynomialMomentBound_nonneg (β : ℝ) (f : MomentPolynomial) :
    0 ≤ uniformPolynomialMomentBound β f := by
  apply Finset.sum_nonneg
  intro d _
  exact mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun j _ =>
    pow_nonneg (uniformSpatialConstant_pos β j).le _)

theorem norm_momentPolynomialValue_le_uniform (β : ℝ) (μ : ParisiMeasure)
    (f : MomentPolynomial) (s : ℝ) (ω : BrownianSample) :
    ‖momentPolynomialValue β μ f s ω‖ ≤ uniformPolynomialMomentBound β f := by
  apply (norm_momentPolynomialValue_le β μ f s ω).trans
  unfold polynomialMomentBound uniformPolynomialMomentBound
  apply Finset.sum_le_sum
  intro d _
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.prod_le_prod₀ (fun j _ => pow_nonneg (norm_nonneg _) _)
  intro j _
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_spatialDerivativeBCF_le_uniform β μ j) _

theorem norm_parisiSpatialJet_sub_le (β : ℝ) (μ : ParisiMeasure)
    (j : ℕ) (s x y : ℝ) :
    ‖parisiSpatialJet β μ (j+1) s y - parisiSpatialJet β μ (j+1) s x‖ ≤
      uniformSpatialConstant β (j+1) * ‖y-x‖ := by
  apply Convex.norm_image_sub_le_of_norm_deriv_le (s := univ)
    (fun z _ => (hasDerivAt_parisiSpatialJet_succ β μ j s z).differentiableAt)
    (fun z _ => ?_) convex_univ (mem_univ x) (mem_univ y)
  rw [(hasDerivAt_parisiSpatialJet_succ β μ j s z).deriv]
  exact (norm_parisiSpatialJet_succ_le β μ (j+1) s z).trans
    (norm_spatialDerivativeBCF_le_uniform β μ (j+1))

def jetProcessMeasureError (β : ℝ) (j : ℕ) (μ ν : ParisiMeasure) : ℝ :=
  ‖bcfSpatialDerivative (parisiGradientBCF β μ) j -
      bcfSpatialDerivative (parisiGradientBCF β ν) j‖ +
    uniformSpatialConstant β (j+1) * (β ^ 2 * Real.exp (β ^ 2) *
      (‖parisiGradientBCF β μ-parisiGradientBCF β ν‖ + parisiCDFDistance μ ν))

theorem norm_jetProcess_sub_le_measureError (β : ℝ) (μ ν : ParisiMeasure)
    (j : ℕ) (ω : BrownianSample) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖jetProcess β μ (j+1) s ω-jetProcess β ν (j+1) s ω‖ ≤
      jetProcessMeasureError β j μ ν := by
  apply (norm_sub_le_norm_sub_add_norm_sub _
    (parisiSpatialJet β ν (j+1) s (optimalStateReal β μ ω s)) _).trans
  apply add_le_add
  · change ‖parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1)
        (bcfSpatialDerivative (parisiGradientBCF β μ) j) _ -
      parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1)
        (bcfSpatialDerivative (parisiGradientBCF β ν) j) _‖ ≤ _
    exact norm_parisiSlabExtend_sub_le (by norm_num) _ _ _
  · exact (norm_parisiSpatialJet_sub_le β ν j s
      (optimalStateReal β ν ω s) (optimalStateReal β μ ω s)).trans
      (mul_le_mul_of_nonneg_left (optimalState_dist_le β μ ν ω hs)
        (uniformSpatialConstant_pos β (j+1)).le)

theorem tendsto_jetProcessMeasureError_of_weak {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (β : ℝ) (j : ℕ) (ν : ι → ParisiMeasure)
    (μ : ParisiMeasure) (hμ : Tendsto ν L (nhds μ)) :
    Tendsto (fun i => jetProcessMeasureError β j (ν i) μ) L (nhds 0) := by
  have hj := ((tendsto_spatialDerivativeBCF_of_weak β j μ ν hμ).sub_const
    (bcfSpatialDerivative (parisiGradientBCF β μ) j)).norm
  have hg := (((continuous_gradientBCF β).tendsto μ).comp hμ).sub_const
    (parisiGradientBCF β μ) |>.norm
  have hc := tendsto_parisiCDFDistance_of_tendsto hμ
  simpa [jetProcessMeasureError] using hj.add
    (tendsto_const_nhds.mul (tendsto_const_nhds.mul (hg.add hc)))

theorem jetProcess_uniform_convergence_of_weak {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (β : ℝ) (j : ℕ) (ν : ι → ParisiMeasure)
    (μ : ParisiMeasure) (hμ : Tendsto ν L (nhds μ)) :
    ∀ ε > 0, ∀ᶠ i in L, ∀ ω : BrownianSample, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖jetProcess β (ν i) (j+1) s ω-jetProcess β μ (j+1) s ω‖ < ε := by
  intro ε hε
  filter_upwards [(tendsto_jetProcessMeasureError_of_weak β j ν μ hμ).eventually
    (eventually_lt_nhds hε)] with i hi ω s hs
  exact (norm_jetProcess_sub_le_measureError β (ν i) μ j ω hs).trans_lt hi

theorem momentPolynomialValue_uniform_convergence_of_weak {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (β : ℝ) (ν : ι → ParisiMeasure) (μ : ParisiMeasure)
    (hμ : Tendsto ν L (nhds μ)) (f : MomentPolynomial) :
    ∀ ε > 0, ∀ᶠ i in L, ∀ ω : BrownianSample, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖momentPolynomialValue β (ν i) f s ω-momentPolynomialValue β μ f s ω‖ < ε := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    intro ε hε
    exact .of_forall fun _ _ _ _ => by simpa [momentPolynomialValue] using hε
  | add p q hp hq =>
    intro ε hε
    filter_upwards [hp (ε/2) (by positivity), hq (ε/2) (by positivity)] with i hip hiq ω s hs
    have he : momentPolynomialValue β (ν i) (p+q) s ω-momentPolynomialValue β μ (p+q) s ω =
        (momentPolynomialValue β (ν i) p s ω-momentPolynomialValue β μ p s ω) +
        (momentPolynomialValue β (ν i) q s ω-momentPolynomialValue β μ q s ω) := by
      simp only [momentPolynomialValue, map_add]
      ring
    rw [he]
    exact (norm_add_le _ _).trans_lt (by linarith [hip ω s hs, hiq ω s hs])
  | mul_X p j hp =>
    intro ε hε
    let B := uniformPolynomialMomentBound β p
    let K := uniformSpatialConstant β j
    have hB : 0 ≤ B := uniformPolynomialMomentBound_nonneg β p
    have hK : 0 ≤ K := (uniformSpatialConstant_pos β j).le
    let δ := ε/(K+B+1)
    have hden : 0 < K+B+1 := by positivity
    have hδ : 0 < δ := div_pos hε hden
    filter_upwards [hp δ hδ, jetProcess_uniform_convergence_of_weak β j ν μ hμ δ hδ]
      with i hip hij ω s hs
    have hpi := hip ω s hs
    have hji := hij ω s hs
    have hbp : ‖momentPolynomialValue β μ p s ω‖ ≤ B :=
      norm_momentPolynomialValue_le_uniform β μ p s ω
    have hbj : ‖jetProcess β (ν i) (j+1) s ω‖ ≤ K :=
      (norm_parisiSpatialJet_succ_le β (ν i) j s _).trans
        (norm_spatialDerivativeBCF_le_uniform β (ν i) j)
    have he : momentPolynomialValue β (ν i) (p * X j) s ω-momentPolynomialValue β μ (p * X j) s ω =
        (momentPolynomialValue β (ν i) p s ω-momentPolynomialValue β μ p s ω) *
          jetProcess β (ν i) (j+1) s ω + momentPolynomialValue β μ p s ω *
          (jetProcess β (ν i) (j+1) s ω-jetProcess β μ (j+1) s ω) := by
      simp only [momentPolynomialValue, map_mul, eval_X]
      ring
    rw [he]
    apply (norm_add_le _ _).trans_lt
    rw [norm_mul, norm_mul]
    have hb := add_le_add (mul_le_mul hpi.le hbj (norm_nonneg _) hδ.le)
      (mul_le_mul hbp hji.le (norm_nonneg _) hB)
    apply hb.trans_lt
    have hdlt : δ * (K+B) < ε := by
      dsimp only [δ]
      rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith
    nlinarith

theorem moment_uniform_convergence_of_weak {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (β : ℝ) (hβ : β ≠ 0) (ν : ι → ParisiMeasure)
    (μ : ParisiMeasure) (hμ : Tendsto ν L (nhds μ)) (f : MomentPolynomial) :
    ∀ ε > 0, ∀ᶠ i in L, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖moment β (ν i) f s-moment β μ f s‖ < ε := by
  intro ε hε
  filter_upwards [momentPolynomialValue_uniform_convergence_of_weak β ν μ hμ f
    (ε/2) (by positivity)] with i hi s hs
  unfold moment
  rw [← integral_sub (integrable_momentPolynomialValue β hβ (ν i) f hs)
    (integrable_momentPolynomialValue β hβ μ f hs)]
  have hh := norm_integral_le_of_norm_le_const (μ := canonicalBrownianMeasure)
    (f := fun ω => momentPolynomialValue β (ν i) f s ω-momentPolynomialValue β μ f s ω)
    (C := ε/2)
    (.of_forall fun ω => (hi ω s hs).le)
  rw [probReal_univ, mul_one] at hh
  exact hh.trans_lt (by linarith)

theorem tendstoUniformlyOn_moment_of_weak {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (β : ℝ) (hβ : β ≠ 0) (ν : ι → ParisiMeasure)
    (μ : ParisiMeasure) (hμ : Tendsto ν L (nhds μ)) (f : MomentPolynomial) :
    TendstoUniformlyOn (fun i => moment β (ν i) f) (moment β μ f) L (Icc (0 : ℝ) 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [moment_uniform_convergence_of_weak β hβ ν μ hμ f ε hε] with i hi s hs
  rw [dist_eq_norm, norm_sub_rev]
  exact hi s hs

end FRSB
