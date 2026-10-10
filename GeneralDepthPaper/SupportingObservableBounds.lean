module

public import GeneralDepthPaper.TruncatedObservableConvergence

@[expose] public section


/-! The literal pointwise drift and squared-magnetization comparison
inequalities in Appendix A.2. Every coefficient and observable here belongs
to the actual truncated recursion and its constructed diffusion. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal BoundedContinuousFunction
namespace GeneralDepthPaper
open FourPapersCommon Paper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

namespace TruncatedParisiData

def gradientSlice {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) (t : ℝ) : ℝ →ᵇ ℝ :=
  (d.spatialField 0).compContinuous ⟨fun x => (t,x),by fun_prop⟩

@[simp] theorem gradientSlice_apply {r : ℕ} {qc : ℝ}
    (d : TruncatedParisiData r qc) (t x : ℝ) :
    d.gradientSlice t x = d.spatialField 0 (t,x) := rfl

theorem norm_gradientSlice_le_one {r : ℕ} {qc : ℝ}
    (d : TruncatedParisiData r qc) (t : ℝ) : ‖d.gradientSlice t‖ ≤ 1 :=
  (BoundedContinuousFunction.norm_compContinuous_le _ _).trans d.spatialField_zero_bound

/-- Display 40, with the limit datum's actual covariance bound as the constant. -/
theorem drift_discrepancy_bound {r s : ℕ} {qc : ℝ}
    (d : TruncatedParisiData r qc) (e : TruncatedParisiData s qc) (t x : ℝ) :
    |d.covarianceField 2 t*d.coefficient t*d.spatialField 0 (t,x)-
      e.covarianceField 2 t*e.coefficient t*e.spatialField 0 (t,x)| ≤
      |d.covarianceField 2 t*d.coefficient t-e.covarianceField 2 t*e.coefficient t|+
      ‖e.covarianceJet 2‖*‖d.gradientSlice t-e.gradientSlice t‖ := by
  have hd : |d.spatialField 0 (t,x)| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using
      ((d.spatialField 0).norm_coe_le_norm (t,x)).trans d.spatialField_zero_bound
  have he : |e.covarianceField 2 t*e.coefficient t| ≤ ‖e.covarianceJet 2‖ := by
    simpa only [Real.norm_eq_abs,TruncatedParisiData.driftData,coe_nnnorm] using
      e.driftData.coefficient_bound t
  have hg : |d.spatialField 0 (t,x)-e.spatialField 0 (t,x)| ≤
      ‖d.gradientSlice t-e.gradientSlice t‖ := by
    simpa only [Real.norm_eq_abs,BoundedContinuousFunction.sub_apply,gradientSlice_apply] using
      (d.gradientSlice t-e.gradientSlice t).norm_coe_le_norm x
  have hid : d.covarianceField 2 t*d.coefficient t*d.spatialField 0 (t,x)-
      e.covarianceField 2 t*e.coefficient t*e.spatialField 0 (t,x) =
      (d.covarianceField 2 t*d.coefficient t-e.covarianceField 2 t*e.coefficient t)*
        d.spatialField 0 (t,x)+e.covarianceField 2 t*e.coefficient t*
        (d.spatialField 0 (t,x)-e.spatialField 0 (t,x)) := by ring
  rw [hid]
  calc
    _ ≤ |(d.covarianceField 2 t*d.coefficient t-e.covarianceField 2 t*e.coefficient t)*
        d.spatialField 0 (t,x)|+|e.covarianceField 2 t*e.coefficient t*
        (d.spatialField 0 (t,x)-e.spatialField 0 (t,x))| := abs_add_le _ _
    _ ≤ _ := by
      simp only [abs_mul]
      exact add_le_add (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hd (abs_nonneg _))
        (mul_le_mul (by simpa only [abs_mul] using he) hg (abs_nonneg _) (norm_nonneg _))

/-- Display 41, with the limit datum's actual spatial Lipschitz bound. -/
theorem Gamma_discrepancy_bound {r s : ℕ} {qc : ℝ}
    (d : TruncatedParisiData r qc) (e : TruncatedParisiData s qc) (t : ℝ) :
    |d.Gamma t-e.Gamma t| ≤ 2*‖d.gradientSlice t-e.gradientSlice t‖+
      2*‖truncatedPotentialFamily e.parameter‖*
        Real.sqrt (∫ω,(d.state t.toNNReal ω-e.state t.toNNReal ω)^2
          ∂canonicalBrownianMeasure) := by
  refine integral_observable_difference_le (d.state t.toNNReal) (e.state t.toNNReal)
    (d.memLp_state _) (e.memLp_state _)
    (fun x => (d.gradientSlice t x)^2) (fun x => (e.gradientSlice t x)^2)
    (d.integrable_spatial_observable_square 0 t) (e.integrable_spatial_observable_square 0 t)
    (by positivity) (by positivity) ?_ ?_
  · intro x
    have hd : |d.gradientSlice t x| ≤ 1 := by
      simpa only [Real.norm_eq_abs] using
        (d.gradientSlice t).norm_coe_le_norm x |>.trans (d.norm_gradientSlice_le_one t)
    have he : |e.gradientSlice t x| ≤ 1 := by
      simpa only [Real.norm_eq_abs] using
        (e.gradientSlice t).norm_coe_le_norm x |>.trans (e.norm_gradientSlice_le_one t)
    have hg : |d.gradientSlice t x-e.gradientSlice t x| ≤
        ‖d.gradientSlice t-e.gradientSlice t‖ := by
      simpa only [Real.norm_eq_abs,BoundedContinuousFunction.sub_apply] using
        (d.gradientSlice t-e.gradientSlice t).norm_coe_le_norm x
    exact (abs_square_sub_le_of_abs_le (by norm_num) hd he).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hg (by norm_num : (0:ℝ) ≤ 2))
  · intro x y
    have he (z : ℝ) : |e.gradientSlice t z| ≤ 1 := by
      simpa only [Real.norm_eq_abs] using
        (e.gradientSlice t).norm_coe_le_norm z |>.trans (e.norm_gradientSlice_le_one t)
    have hl : |e.gradientSlice t x-e.gradientSlice t y| ≤
        ‖truncatedPotentialFamily e.parameter‖*|x-y| := by
      simpa only [gradientSlice_apply,Real.dist_eq,coe_nnnorm,Fin.castSucc_zero] using
        (e.lipschitzWith_spatialField 0 t).dist_le_mul x y
    calc
      _ ≤ 2*1*|e.gradientSlice t x-e.gradientSlice t y| :=
        abs_square_sub_le_of_abs_le (by norm_num) (he x) (he y)
      _ ≤ 2*1*(‖truncatedPotentialFamily e.parameter‖*|x-y|) :=
        mul_le_mul_of_nonneg_left hl (by norm_num)
      _ = _ := by ring

end TruncatedParisiData

/-- A single positive, explicitly derived constant works in both displays
40 and 41 for every approximant. No convergence or discrepancy estimate is
assumed; only the genuine limit datum is used to construct the constant. -/
theorem truncated_drift_and_Gamma_comparison {r s : ℕ} {qc : ℝ}
    (d : ℕ → TruncatedParisiData r qc) (e : TruncatedParisiData s qc) :
    ∃ C : ℝ,0 < C ∧ ∀ n t,
      (∀ x,|(d n).covarianceField 2 t*(d n).coefficient t*(d n).spatialField 0 (t,x)-
          e.covarianceField 2 t*e.coefficient t*e.spatialField 0 (t,x)| ≤
        |(d n).covarianceField 2 t*(d n).coefficient t-e.covarianceField 2 t*e.coefficient t|+
          C*‖(d n).gradientSlice t-e.gradientSlice t‖) ∧
      |(d n).Gamma t-e.Gamma t| ≤ 2*‖(d n).gradientSlice t-e.gradientSlice t‖+
        2*C*Real.sqrt (∫ω,((d n).state t.toNNReal ω-e.state t.toNNReal ω)^2
          ∂canonicalBrownianMeasure) := by
  let C := 1+‖e.covarianceJet 2‖+‖truncatedPotentialFamily e.parameter‖
  have hcov : ‖e.covarianceJet 2‖ ≤ C := by dsimp [C]; linarith [norm_nonneg (truncatedPotentialFamily e.parameter)]
  have hLip : ‖truncatedPotentialFamily e.parameter‖ ≤ C := by dsimp [C]; linarith [norm_nonneg (e.covarianceJet 2)]
  refine ⟨C,by dsimp [C]; positivity,fun n t => ⟨fun x => ?_,?_⟩⟩
  · exact ((d n).drift_discrepancy_bound e t x).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right hcov (norm_nonneg _)))
  · exact ((d n).Gamma_discrepancy_bound e t).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hLip (by norm_num)) (Real.sqrt_nonneg _)))

end GeneralDepthPaper
