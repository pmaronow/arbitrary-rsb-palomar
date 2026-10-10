module

public import GeneralDepthPaper.AnalyticKernel
public import GeneralDepthPaper.AnalyticDerivativeBound

set_option backward.privateInPublic true

@[expose] public section


/-! Explicit convergent multilinear coefficients retain the uniform derivative
majorants of the actual bounded exponential kernel. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal BoundedContinuousFunction
namespace GeneralDepthPaper
variable {S E : Type*} [TopologicalSpace S] [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

private theorem scalarTaylor_envelope (L : S→E→L[ℝ] ℝ) (H : S→ℝ)
    (r : ℝ≥0) (hr : 0<r) (C : ℝ)
    (hb : ∀s,‖H s‖*Real.exp ((r:ℝ)*‖L s‖)≤C) (n : ℕ) (s : S) :
    ‖laplaceTaylorTerm L H n s‖≤C/(r:ℝ)^n := by
  apply (le_div_iff₀ (pow_pos (show 0<(r:ℝ) from hr) n)).mpr
  calc
    ‖laplaceTaylorTerm L H n s‖*(r:ℝ)^n
      ≤(‖H s‖*‖L s‖^n/(n.factorial:ℝ))*(r:ℝ)^n := by
        gcongr; exact norm_laplaceTaylorTerm_le L H n s
    _=‖H s‖*(((r:ℝ)*‖L s‖)^n/(n.factorial:ℝ)) := by rw [mul_pow]; ring
    _≤‖H s‖*Real.exp ((r:ℝ)*‖L s‖) :=
      mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp _
        (mul_nonneg r.2 (norm_nonneg _)) n) (norm_nonneg _)
    _≤C := hb s

private def scalarTaylorBCF (L : S→E→L[ℝ] ℝ) (H : S→ℝ) (hL : Continuous L)
    (hH : Continuous H) (r : ℝ≥0) (hr : 0<r) (C : ℝ) (hC : 0≤C)
    (hb : ∀s,‖H s‖*Real.exp ((r:ℝ)*‖L s‖)≤C)
    (n : ℕ) (v : Fin n→E) : S →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun s=>laplaceTaylorTerm L H n s v)
    (by
      simp only [laplaceTaylorTerm_apply,smul_eq_mul]
      exact continuous_const.mul (hH.mul
        (continuous_finsetProd _ (fun i _=>(ContinuousLinearMap.apply ℝ ℝ (v i)).continuous.comp hL))))
    (C/(r:ℝ)^n*(∏i,‖v i‖)) (fun s=>
      (ContinuousMultilinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (scalarTaylor_envelope L H r hr C hb n s)
          (Finset.prod_nonneg (fun _ _=>norm_nonneg _))))

private def scalarTaylorMultilinear (L : S→E→L[ℝ] ℝ) (H : S→ℝ) (hL : Continuous L)
    (hH : Continuous H) (r : ℝ≥0) (hr : 0<r) (C : ℝ) (hC : 0≤C)
    (hb : ∀s,‖H s‖*Real.exp ((r:ℝ)*‖L s‖)≤C) (n : ℕ) :
    MultilinearMap ℝ (fun _:Fin n=>E) (S →ᵇ ℝ) where
  toFun := scalarTaylorBCF L H hL hH r hr C hC hb n
  map_update_add' := by
    intro _ v i a b
    ext s
    exact (laplaceTaylorTerm L H n s).map_update_add v i a b
  map_update_smul' := by
    intro _ v i c a
    ext s
    exact (laplaceTaylorTerm L H n s).map_update_smul v i c a

def boundedLaplaceTaylorSeries (L : S→E→L[ℝ] ℝ) (H : S→ℝ) (hL : Continuous L)
    (hH : Continuous H) (r : ℝ≥0) (hr : 0<r) (C : ℝ) (hC : 0≤C)
    (hb : ∀s,‖H s‖*Real.exp ((r:ℝ)*‖L s‖)≤C) : FormalMultilinearSeries ℝ E (S →ᵇ ℝ) :=
  fun n=>(scalarTaylorMultilinear L H hL hH r hr C hC hb n).mkContinuous (C/(r:ℝ)^n)
    (fun v=>(BoundedContinuousFunction.norm_le (mul_nonneg (by positivity)
      (Finset.prod_nonneg (fun _ _=>norm_nonneg _)))).mpr (fun s=>
        (ContinuousMultilinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (scalarTaylor_envelope L H r hr C hb n s)
            (Finset.prod_nonneg (fun _ _=>norm_nonneg _)))))

theorem hasFPowerSeriesOnBall_boundedExpKernel_zero (L : S→E→L[ℝ] ℝ) (H : S→ℝ)
    (hL : Continuous L) (hH : Continuous H) (r : ℝ≥0) (hr : 0<r)
    (C : ℝ) (hC : 0≤C) (hb : ∀s,‖H s‖*Real.exp ((r:ℝ)*‖L s‖)≤C) :
    HasFPowerSeriesOnBall (boundedExpKernel L H hL hH)
      (boundedLaplaceTaylorSeries L H hL hH r hr C hC hb) 0 (r:ℝ≥0∞) ∧
    (∀n,‖boundedLaplaceTaylorSeries L H hL hH r hr C hC hb n‖*(r:ℝ)^n ≤ C) := by
  let P := boundedLaplaceTaylorSeries L H hL hH r hr C hC hb
  have hP (n : ℕ) : ‖P n‖*(r:ℝ)^n≤C := by
    have hn := MultilinearMap.mkContinuous_norm_le
      (scalarTaylorMultilinear L H hL hH r hr C hC hb n) (by positivity)
      (show ∀v,‖scalarTaylorMultilinear L H hL hH r hr C hC hb n v‖≤
        C/(r:ℝ)^n*(∏i,‖v i‖) from fun v=>
          (BoundedContinuousFunction.norm_le (mul_nonneg (by positivity)
            (Finset.prod_nonneg (fun _ _=>norm_nonneg _)))).mpr
            (fun s=>(ContinuousMultilinearMap.le_opNorm _ _).trans
              (mul_le_mul_of_nonneg_right (scalarTaylor_envelope L H r hr C hb n s)
                (Finset.prod_nonneg (fun _ _=>norm_nonneg _)))))
    exact (le_div_iff₀ (pow_pos (show 0<(r:ℝ) from hr) n)).mp hn
  have hrad := P.le_radius_of_bound C hP
  refine ⟨⟨hrad,by exact_mod_cast hr,?_⟩,hP⟩
  intro y hy
  have hy0 : ‖y‖<(r:ℝ) := by
    apply (ENNReal.ofReal_lt_ofReal_iff (show 0<(r:ℝ) from hr)).mp
    simpa only [Metric.mem_eball,edist_dist,dist_zero_right,ENNReal.ofReal_coe_nnreal] using hy
  have hyP : y∈Metric.eball (0:E) P.radius := hy.trans_le hrad
  have hs := P.summable hyP
  have hbounded : ∃C:ℝ,∀s,‖H s*Real.exp (L s y)‖≤C := by
    refine ⟨C,fun s=>?_⟩
    rw [norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]
    apply (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)).trans (hb s)
    calc
      L s y≤|L s y| := le_abs_self _
      _≤‖L s‖*‖y‖ := (L s).le_opNorm y
      _≤‖L s‖*(r:ℝ) := mul_le_mul_of_nonneg_left hy0.le (norm_nonneg _)
      _=(r:ℝ)*‖L s‖ := mul_comm _ _

  have he : (∑'n,P n (fun _=>y))=boundedExpKernel L H hL hH y := by
    ext s
    change (BoundedContinuousFunction.evalCLM ℝ s) (∑'n,P n (fun _=>y))=_
    rw [(BoundedContinuousFunction.evalCLM ℝ s).map_tsum hs,
      boundedExpKernel_apply L H hL hH y hbounded s]
    change (∑'n,laplaceTaylorTerm L H n s (fun _=>y))=H s*Real.exp (L s y)
    have hexp := (NormedSpace.exp_series_hasSum_exp' (𝕂:=ℝ) (L s y)).mul_left (H s)
    rw [←Real.exp_eq_exp_ℝ] at hexp
    convert hexp.tsum_eq using 1
    apply tsum_congr
    intro n
    rw [laplaceTaylorTerm_apply]
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
    ring
  simpa only [zero_add,he] using hs.hasSum


theorem norm_iteratedFDeriv_boundedExpKernel_zero_le (L : S→E→L[ℝ] ℝ) (H : S→ℝ)
    (hL : Continuous L) (hH : Continuous H) (r : ℝ≥0) (hr : 0<r)
    (C : ℝ) (hC : 0≤C) (hb : ∀s,‖H s‖*Real.exp ((r:ℝ)*‖L s‖)≤C) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (boundedExpKernel L H hL hH) 0‖ ≤
      (n.factorial:ℝ)*C/(r:ℝ)^n := by
  obtain ⟨hs,hbnd⟩ := hasFPowerSeriesOnBall_boundedExpKernel_zero L H hL hH r hr C hC hb
  exact norm_iteratedFDeriv_le_of_geometric_coefficients hs r C hr hbnd n

theorem norm_iteratedFDeriv_boundedExpKernel_le (L : S→E→L[ℝ] ℝ) (H : S→ℝ)
    (hL : Continuous L) (hH : Continuous H) (p : E) (r : ℝ≥0) (hr : 0<r)
    (C : ℝ) (hC : 0≤C)
    (hb : ∀s,‖H s*Real.exp (L s p)‖*Real.exp ((r:ℝ)*‖L s‖)≤C) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (boundedExpKernel L H hL hH) p‖ ≤
      (n.factorial:ℝ)*C/(r:ℝ)^n := by
  let H0 : S→ℝ := fun s => H s*Real.exp (L s p)
  have hH0 : Continuous H0 := hH.mul
    (Real.continuous_exp.comp ((ContinuousLinearMap.apply ℝ ℝ p).continuous.comp hL))
  obtain ⟨hseries,hcoeff⟩ := hasFPowerSeriesOnBall_boundedExpKernel_zero L H0 hL hH0 r hr C hC hb
  have he : (fun q:E=>boundedExpKernel L H0 hL hH0 (q-p))=boundedExpKernel L H hL hH := by
    funext q
    have hf (s:S) : H0 s*Real.exp (L s (q-p))=H s*Real.exp (L s q) := by
      simp only [H0,map_sub,Real.exp_sub]
      field_simp
    have hbEq : (∃C:ℝ,∀s,‖H0 s*Real.exp (L s (q-p))‖≤C) ↔
        (∃C:ℝ,∀s,‖H s*Real.exp (L s q)‖≤C) := by simp only [hf]
    by_cases h : ∃C:ℝ,∀s,‖H s*Real.exp (L s q)‖≤C
    · ext s
      rw [boundedExpKernel_apply L H0 hL hH0 (q-p) (hbEq.mpr h),
        boundedExpKernel_apply L H hL hH q h]
      exact hf s
    · simp only [boundedExpKernel,dif_neg h,dif_neg (mt hbEq.mp h)]
  have hs := hseries.comp_sub p
  rw [zero_add,he] at hs
  exact norm_iteratedFDeriv_le_of_geometric_coefficients hs r C hr hcoeff n

end GeneralDepthPaper
