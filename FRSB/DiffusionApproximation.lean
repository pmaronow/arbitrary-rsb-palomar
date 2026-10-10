module

public import FRSB.OptimalDiffusion
public import FRSB.IntegralGronwall
public import Paper.ParisiCDFIntegral
public import FRSB.GlobalMeasureStability

@[expose] public section


/-! Deterministic L¹-CDF stability for the actual same-Brownian optimal states. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction
namespace FRSB

 theorem continuous_M_path (β : ℝ) (μ : ParisiMeasure) (ω : BrownianSample) :
    Continuous (fun s => M β μ s ω) := by
  simp only [M, jetProcess, parisiSpatialJet_one]
  exact (Paper.continuous_parisiGradient β μ).comp
    (continuous_id.prodMk (continuous_optimalStateReal β μ ω))

 theorem optimalDrift_intervalIntegrable (β : ℝ) (μ : ParisiMeasure)
    (ω : BrownianSample) (a b : ℝ) :
    IntervalIntegrable (fun s => β ^ 2 * alpha μ s * M β μ s ω) volume a b :=
  ((Paper.parisiCDF_intervalIntegrable μ a b).const_mul (β ^ 2)).mul_continuousOn
    (continuous_M_path β μ ω).continuousOn

 theorem optimalState_drift_difference_le (β : ℝ) (μ ν : ParisiMeasure)
    (d : ℝ) (_hd : 0 ≤ d)
    (hgrad : ∀ s x, ‖Paper.parisiGradient β μ (s,x) -
      Paper.parisiGradient β ν (s,x)‖ ≤ d) (ω : BrownianSample) (s : ℝ) :
    ‖alpha μ s * M β μ s ω - alpha ν s * M β ν s ω‖ ≤
      ‖alpha μ s - alpha ν s‖ + d +
        ‖optimalStateReal β μ ω s - optimalStateReal β ν ω s‖ := by
  have hm : ‖M β μ s ω‖ ≤ 1 := by
    simpa only [M, jetProcess, parisiSpatialJet_one] using
      Paper.norm_parisiGradient_le_one β μ (s, optimalStateReal β μ ω s)
  have han : ‖alpha ν s‖ ≤ 1 := by
    change ‖Paper.parisiCDF ν s‖ ≤ 1
    rw [Real.norm_of_nonneg (Paper.parisiCDF_nonneg ν s)]
    exact Paper.parisiCDF_le_one ν s
  have hM : ‖M β μ s ω - M β ν s ω‖ ≤ d +
      ‖optimalStateReal β μ ω s - optimalStateReal β ν ω s‖ := by
    simp only [M, jetProcess, parisiSpatialJet_one]
    calc
      ‖Paper.parisiGradient β μ (s, optimalStateReal β μ ω s) -
          Paper.parisiGradient β ν (s, optimalStateReal β ν ω s)‖ ≤
          ‖Paper.parisiGradient β μ (s, optimalStateReal β μ ω s) -
            Paper.parisiGradient β ν (s, optimalStateReal β μ ω s)‖ +
          ‖Paper.parisiGradient β ν (s, optimalStateReal β μ ω s) -
            Paper.parisiGradient β ν (s, optimalStateReal β ν ω s)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ d + ‖optimalStateReal β μ ω s - optimalStateReal β ν ω s‖ := by
        apply add_le_add (hgrad s _)
        simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using
          (Paper.lipschitzWith_parisiGradient_all β ν s).dist_le_mul
            (optimalStateReal β μ ω s) (optimalStateReal β ν ω s)
  have he : alpha μ s * M β μ s ω - alpha ν s * M β ν s ω =
      (alpha μ s - alpha ν s) * M β μ s ω +
        alpha ν s * (M β μ s ω - M β ν s ω) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_mul]
  have h1 := mul_le_mul_of_nonneg_left hm (norm_nonneg (alpha μ s - alpha ν s))
  have h2 := mul_le_mul han hM (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  simp only [mul_one, one_mul] at h1 h2
  exact (add_le_add h1 h2).trans_eq (by ring)

 theorem optimalState_L1_dist_le (β : ℝ) (μ ν : ParisiMeasure)
    (d : ℝ) (hd : 0 ≤ d)
    (hgrad : ∀ s x, ‖Paper.parisiGradient β μ (s,x) -
      Paper.parisiGradient β ν (s,x)‖ ≤ d)
    (ω : BrownianSample) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖optimalStateReal β μ ω t - optimalStateReal β ν ω t‖ ≤
      β ^ 2 * Real.exp (β ^ 2) * (d + Paper.parisiCDFDistance μ ν) := by
  let e : ℝ → ℝ := fun s => ‖optimalStateReal β μ ω s - optimalStateReal β ν ω s‖
  have he : Continuous e := ((continuous_optimalStateReal β μ ω).sub
    (continuous_optimalStateReal β ν ω)).norm
  have hCDFint (a b : ℝ) : IntervalIntegrable (fun s => ‖alpha μ s - alpha ν s‖) volume a b :=
    ((Paper.parisiCDF_intervalIntegrable μ a b).sub
      (Paper.parisiCDF_intervalIntegrable ν a b)).norm
  have hbudget : 0 ≤ Paper.parisiCDFDistance μ ν := Paper.parisiCDFDistance_nonneg μ ν
  have hbound : ∀ r ∈ Icc (0 : ℝ) 1,
      e r ≤ β ^ 2 * (d + Paper.parisiCDFDistance μ ν) + β ^ 2 * ∫ s in 0..r, e s := by
    intro r hr
    have hiμ := optimalDrift_intervalIntegrable β μ ω 0 r
    have hiν := optimalDrift_intervalIntegrable β ν ω 0 r
    have hCDFle : (∫ s in 0..r, ‖alpha μ s - alpha ν s‖) ≤ Paper.parisiCDFDistance μ ν :=
      intervalIntegral.integral_mono_interval le_rfl hr.1 hr.2
        (ae_of_all _ (fun s => norm_nonneg _)) (hCDFint 0 1)
    have hdint : IntervalIntegrable (fun _ : ℝ => d) volume 0 r := intervalIntegrable_const
    have hisum : IntervalIntegrable
        (fun s => β ^ 2 * (‖alpha μ s - alpha ν s‖ + d + e s)) volume 0 r :=
      (((hCDFint 0 r).add hdint).add (he.intervalIntegrable 0 r)).const_mul _
    have hm := intervalIntegral.integral_mono_on hr.1 ((hiμ.sub hiν).norm) hisum
      (fun s _ => by
        rw [mul_assoc (β ^ 2), mul_assoc (β ^ 2), ← mul_sub, norm_mul,
          Real.norm_of_nonneg (sq_nonneg β)]
        exact mul_le_mul_of_nonneg_left (optimalState_drift_difference_le β μ ν d hd hgrad ω s)
          (sq_nonneg β))
    have heq : e r = ‖∫ s in 0..r,
        (β ^ 2 * alpha μ s * M β μ s ω - β ^ 2 * alpha ν s * M β ν s ω)‖ := by
      dsimp only [e]
      rw [optimalState_integral_equation β μ ω hr, optimalState_integral_equation β ν ω hr,
        add_sub_add_left_eq_sub, intervalIntegral.integral_sub hiμ hiν]
    rw [heq]
    apply ((intervalIntegral.norm_integral_le_integral_norm hr.1).trans hm).trans
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
      ((hCDFint 0 r).add hdint) (he.intervalIntegrable 0 r),
      intervalIntegral.integral_add (hCDFint 0 r) hdint, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left hCDFle (sq_nonneg β),
      mul_le_mul_of_nonneg_left hr.2 hd]
  have hg := integral_gronwall_exp_bound e he (β ^ 2 * (d + Paper.parisiCDFDistance μ ν))
    (β ^ 2) (mul_nonneg (sq_nonneg β) (add_nonneg hd hbudget)) (sq_nonneg β)
    (fun s _ => norm_nonneg _) hbound t ht
  exact hg.trans_eq (by ring)

/-- The paper's exact deterministic bound with the actual global gradient norm. -/
theorem optimalState_dist_le (β : ℝ) (μ ν : ParisiMeasure) (ω : BrownianSample)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖optimalStateReal β μ ω t - optimalStateReal β ν ω t‖ ≤
      β ^ 2 * Real.exp (β ^ 2) *
        (‖Paper.parisiGradientBCF β μ - Paper.parisiGradientBCF β ν‖ +
          Paper.parisiCDFDistance μ ν) :=
  optimalState_L1_dist_le β μ ν _ (norm_nonneg _) (fun s x =>
    Paper.norm_parisiSlabExtend_sub_le (by norm_num) _ _ (s,x)) ω ht

/-- Actual weak-measure convergence gives uniform same-Brownian path convergence.
The deterministic bound holds simultaneously for every sample path. -/
theorem optimalState_uniform_convergence_of_weak {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (β : ℝ) (μs : ι → ParisiMeasure) (μ : ParisiMeasure)
    (hμ : Tendsto μs L (nhds μ)) :
    ∀ ε > 0, ∀ᶠ i in L, ∀ ω : BrownianSample, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖optimalStateReal β (μs i) ω t - optimalStateReal β μ ω t‖ < ε := by
  have hgrad := ((continuous_gradientBCF β).tendsto μ).comp hμ
  have hn : Tendsto (fun i => ‖Paper.parisiGradientBCF β (μs i) -
      Paper.parisiGradientBCF β μ‖) L (nhds 0) := by
    simpa using (hgrad.sub (tendsto_const_nhds (x := Paper.parisiGradientBCF β μ))).norm
  have hc := tendsto_parisiCDFDistance_of_tendsto hμ
  have hbudget : Tendsto (fun i => β ^ 2 * Real.exp (β ^ 2) *
      (‖Paper.parisiGradientBCF β (μs i) - Paper.parisiGradientBCF β μ‖ +
        Paper.parisiCDFDistance (μs i) μ)) L (nhds 0) := by
    simpa using tendsto_const_nhds.mul (hn.add hc)
  intro ε hε
  filter_upwards [hbudget.eventually (eventually_lt_nhds hε)] with i hi ω t ht
  exact (optimalState_dist_le β (μs i) μ ω ht).trans_lt hi

end FRSB
