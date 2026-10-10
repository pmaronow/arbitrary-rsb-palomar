module

public import GeneralDepthPaper.HighOverlapIntermediate

@[expose] public section


/-! The literal intermediate-region integral budget, before discarding its
nonnegative lower-endpoint primitive. This includes both displayed bounds. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace GeneralDepthPaper
set_option maxHeartbeats 600000

theorem firstVariation_high_degree_increment_integral_bound (Ξ : AdmissibleCovariance)
    (p : ℕ) (hp : 4 ≤ p) (he : Even p) (hn : p ∉ Ξ.degrees)
    {lam : ℝ} (hlam : 0 < lam) (μ : ParisiMeasure) {a b c : ℝ}
    (ha : a ∈ Icc (0:ℝ) 1) (hab : a ≤ b) (hbc : b ≤ c) (hc : c ≤ 1) :
    firstVariation (Ξ.addHighDegree p hp he hn lam hlam) μ b ≤
      firstVariation (Ξ.addHighDegree p hp he hn lam hlam) μ a +
        (1/2:ℝ) * (∫ s in a..1, (1-s)*Ξ.second s) +
        (lam/2) * (∫ s in a..c, (1-s)*(p:ℝ)*((p-1:ℕ):ℝ)*s^(p-2)) := by
  let X := Ξ.addHighDegree p hp he hn lam hlam
  have hb : b ∈ Icc (0:ℝ) 1 := ⟨ha.1.trans hab,hbc.trans hc⟩
  have hd : IntervalIntegrable (firstVariationDerivative X μ) volume a b :=
    ((contDiffOn_firstVariationDerivative X μ).continuousOn.mono
      (Icc_subset_Icc ha.1 hb.2)).intervalIntegrable_of_Icc hab
  have hpC : Continuous (fun s : ℝ => (1-s)*(p:ℝ)*((p-1:ℕ):ℝ)*s^(p-2)) := by fun_prop
  have hbC : Continuous (fun s : ℝ => (1-s)*Ξ.second s) :=
    (continuous_const.sub continuous_id).mul Ξ.continuous_second
  have huC : Continuous (fun s : ℝ => (1/2:ℝ)*X.second s*(1-s)) := by
    exact (continuous_const.mul X.continuous_second).mul (continuous_const.sub continuous_id)
  have hupper := intervalIntegral.integral_mono_on hab hd (huC.intervalIntegrable a b)
    (fun s hs => by
      unfold firstVariationDerivative
      exact mul_le_mul_of_nonneg_left (sub_le_sub_right (Gamma_le_one X μ s) s)
        (mul_nonneg (by norm_num) (X.second_nonneg (ha.1.trans hs.1))))
  have hdecomp : (∫ s in a..b, (1/2:ℝ)*X.second s*(1-s)) =
      (1/2:ℝ)*(∫ s in a..b, (1-s)*Ξ.second s) +
      (lam/2)*(∫ s in a..b, (1-s)*(p:ℝ)*((p-1:ℕ):ℝ)*s^(p-2)) := by
    calc
      _ = ∫ s in a..b, (1/2:ℝ)*((1-s)*Ξ.second s) +
          (lam/2)*((1-s)*(p:ℝ)*((p-1:ℕ):ℝ)*s^(p-2)) := by
        apply intervalIntegral.integral_congr
        intro s _
        dsimp only [X]
        rw [Ξ.addHighDegree_second]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add ((hbC.const_mul _).intervalIntegrable _ _)
          ((hpC.const_mul _).intervalIntegrable _ _),
          intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  have hbmono := intervalIntegral.integral_mono_interval (μ := volume) (a := a) (b := b) (c := a) (d := 1)
    le_rfl hab hb.2
    (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact mul_nonneg (sub_nonneg.mpr hs.2) (Ξ.second_nonneg (ha.1.trans hs.1.le)))
    (hbC.intervalIntegrable a 1)
  have hpmono := intervalIntegral.integral_mono_interval (μ := volume) (a := a) (b := b) (c := a) (d := c)
    le_rfl hab hbc
    (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact mul_nonneg
          (mul_nonneg (mul_nonneg (sub_nonneg.mpr (hs.2.trans hc)) (Nat.cast_nonneg p))
            (Nat.cast_nonneg (p-1))) (pow_nonneg (ha.1.trans hs.1.le) _))
    (hpC.intervalIntegrable a c)
  rw [←firstVariation_difference_eq_integral X μ ha hb,hdecomp] at hupper
  have hbm := mul_le_mul_of_nonneg_left hbmono (by norm_num : (0:ℝ) ≤ 1/2)
  have hpm := mul_le_mul_of_nonneg_left hpmono (by positivity : (0:ℝ) ≤ lam/2)
  linarith

theorem high_overlap_intermediate_literal_budget (Ξ : AdmissibleCovariance)
    (p : ℕ) (hp : 4 ≤ p) (he : Even p) (hn : p ∉ Ξ.degrees)
    {lam : ℝ} (hlam : 0 < lam) (μ : ParisiMeasure) {qc q hat γ : ℝ}
    (hc : qc ∈ Icc (0:ℝ) 1) (hq : qc ≤ q) (hh : q ≤ hat) (ht : hat ≤ 1)
    (hneg : firstVariation (Ξ.addHighDegree p hp he hn lam hlam) μ qc ≤ -3*γ)
    (hcost : (1/2:ℝ)*(∫ s in qc..1, (1-s)*Ξ.second s) ≤ γ) :
    firstVariation (Ξ.addHighDegree p hp he hn lam hlam) μ q ≤
      firstVariation (Ξ.addHighDegree p hp he hn lam hlam) μ qc +
        (1/2:ℝ)*(∫ s in qc..1, (1-s)*Ξ.second s) +
        (lam/2)*(∫ s in qc..hat, (1-s)*(p:ℝ)*((p-1:ℕ):ℝ)*s^(p-2)) ∧
    firstVariation (Ξ.addHighDegree p hp he hn lam hlam) μ qc +
        (1/2:ℝ)*(∫ s in qc..1, (1-s)*Ξ.second s) +
        (lam/2)*(∫ s in qc..hat, (1-s)*(p:ℝ)*((p-1:ℕ):ℝ)*s^(p-2)) ≤
      -2*γ + (lam/2)*(∫ s in qc..hat, (1-s)*(p:ℝ)*((p-1:ℕ):ℝ)*s^(p-2)) := by
  exact ⟨firstVariation_high_degree_increment_integral_bound Ξ p hp he hn hlam μ hc hq hh ht,
    by linarith⟩

end GeneralDepthPaper
