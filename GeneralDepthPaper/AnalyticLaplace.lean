module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.ContDiff.Basic

set_option backward.privateInPublic true

@[expose] public section


/-! Banach-algebra valued Laplace integrals. An exponential norm envelope
provides a genuine convergent Fréchet power series after Bochner integration. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal
namespace GeneralDepthPaper

variable {Ω E A : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedCommRing A] [NormedAlgebra ℝ A] [NormOneClass A] [CompleteSpace A]

/-- The actual multilinear Taylor integrand of a Laplace transform. -/
def laplaceTaylorTerm (L : Ω→E→L[ℝ] A) (H : Ω→A) (n : ℕ) (sample : Ω) :
    E [×n]→L[ℝ] A :=
  ((n.factorial:ℝ)⁻¹) • (H sample •
    ((ContinuousMultilinearMap.mkPiAlgebraFin ℝ n A).compContinuousLinearMap
      (fun _=>L sample)))

omit [MeasurableSpace Ω] [NormOneClass A] [CompleteSpace A] in
theorem laplaceTaylorTerm_apply (L : Ω→E→L[ℝ] A) (H : Ω→A)
    (n : ℕ) (sample : Ω) (v : Fin n→E) :
    laplaceTaylorTerm L H n sample v=
      ((n.factorial:ℝ)⁻¹) • (H sample*(∏i,L sample (v i))) := by
  simp [laplaceTaylorTerm,ContinuousMultilinearMap.mkPiAlgebraFin_apply,
    List.prod_ofFn,smul_eq_mul]

omit [MeasurableSpace Ω] [CompleteSpace A] in
theorem norm_laplaceTaylorTerm_le (L : Ω→E→L[ℝ] A) (H : Ω→A)
    (n : ℕ) (sample : Ω) :
    ‖laplaceTaylorTerm L H n sample‖≤
      ‖H sample‖*‖L sample‖^n/(n.factorial:ℝ) := by
  unfold laplaceTaylorTerm
  rw [norm_smul,Real.norm_of_nonneg (by positivity)]
  have h := (ContinuousMultilinearMap.mkPiAlgebraFin ℝ n A).norm_compContinuousLinearMap_le
    (fun _ : Fin n=>L sample)
  simp only [ContinuousMultilinearMap.norm_mkPiAlgebraFin,one_mul,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin] at h
  have hH := norm_smul_le (H sample)
    ((ContinuousMultilinearMap.mkPiAlgebraFin ℝ n A).compContinuousLinearMap (fun _=>L sample))
  calc
    (n.factorial:ℝ)⁻¹*‖H sample •
        ((ContinuousMultilinearMap.mkPiAlgebraFin ℝ n A).compContinuousLinearMap (fun _=>L sample))‖
      ≤(n.factorial:ℝ)⁻¹*(‖H sample‖*‖L sample‖^n)  := by
        exact mul_le_mul_of_nonneg_left
          (hH.trans (mul_le_mul_of_nonneg_left h (norm_nonneg _))) (by positivity)
    _= _ := by ring

theorem aestronglyMeasurable_laplaceTaylorTerm (L : Ω→E→L[ℝ] A) (H : Ω→A)
    (μ : Measure Ω) (hL : AEStronglyMeasurable L μ) (hH : AEStronglyMeasurable H μ)
    (n : ℕ) : AEStronglyMeasurable (laplaceTaylorTerm L H n) μ := by
  have hc : Continuous (fun l : E→L[ℝ] A=>
      (ContinuousMultilinearMap.mkPiAlgebraFin ℝ n A).compContinuousLinearMap (fun _=>l)) := by
    exact ((ContinuousLinearMap.apply ℝ _ (ContinuousMultilinearMap.mkPiAlgebraFin ℝ n A)).continuous.comp
      ((ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
        (fun _ : Fin n=>E) (fun _=>A) A).cont.comp
        (continuous_pi (fun _=>continuous_id))))
  convert! (hH.smul (hc.comp_aestronglyMeasurable hL)).const_smul ((n.factorial:ℝ)⁻¹) using 1

private theorem real_exp_hasSum (t : ℝ) :
    HasSum (fun n : ℕ=>t^n/(n.factorial:ℝ)) (Real.exp t) := by
  rw [Real.exp_eq_exp_ℝ]
  simpa only [smul_eq_mul,div_eq_mul_inv,mul_comm] using
    NormedSpace.exp_series_hasSum_exp' (𝕂:=ℝ) t

/-- An exponential operator-norm envelope suffices for a genuine
Banach-valued analytic integral, without an assumed regularity of the result. -/
theorem analyticAt_laplace_integral_zero (L : Ω→E→L[ℝ] A) (H : Ω→A)
    (μ : Measure Ω) (hL : AEStronglyMeasurable L μ) (hH : AEStronglyMeasurable H μ)
    (r : ℝ≥0) (hr : 0<r)
    (hi : Integrable (fun sample=>‖H sample‖*Real.exp ((r:ℝ)*‖L sample‖)) μ) :
    AnalyticAt ℝ (fun p : E=>∫sample,H sample*NormedSpace.exp (L sample p) ∂μ) 0 := by
  let M : Ω→ℝ := fun sample=>‖H sample‖*Real.exp ((r:ℝ)*‖L sample‖)
  have hr0 : 0<(r:ℝ) := hr
  have hb (n : ℕ) (sample : Ω) :
      ‖laplaceTaylorTerm L H n sample‖*(r:ℝ)^n≤M sample := by
    calc
      ‖laplaceTaylorTerm L H n sample‖*(r:ℝ)^n
        ≤(‖H sample‖*‖L sample‖^n/(n.factorial:ℝ))*(r:ℝ)^n := by
          gcongr; exact norm_laplaceTaylorTerm_le L H n sample
      _=‖H sample‖*((((r:ℝ)*‖L sample‖)^n)/(n.factorial:ℝ)) := by rw [mul_pow]; ring
      _≤M sample := mul_le_mul_of_nonneg_left
        (Real.pow_div_factorial_le_exp _ (mul_nonneg r.2 (norm_nonneg _)) n) (norm_nonneg _)
  have hti (n : ℕ) : Integrable (laplaceTaylorTerm L H n) μ := by
    apply (hi.div_const ((r:ℝ)^n)).mono'
      (aestronglyMeasurable_laplaceTaylorTerm L H μ hL hH n)
    exact .of_forall fun sample=> (le_div_iff₀ (pow_pos hr0 n)).mpr (hb n sample)
  let P : FormalMultilinearSeries ℝ E A := fun n=>∫sample,laplaceTaylorTerm L H n sample ∂μ
  have hP (n : ℕ) : ‖P n‖*(r:ℝ)^n≤∫sample,M sample ∂μ := by
    have hn : ‖P n‖≤∫sample,M sample/(r:ℝ)^n ∂μ := by
      apply (norm_integral_le_integral_norm _).trans
      apply integral_mono_ae (hti n).norm (hi.div_const _)
      exact .of_forall fun sample=>(le_div_iff₀ (pow_pos hr0 n)).mpr (hb n sample)
    rw [integral_div] at hn
    exact (le_div_iff₀ (pow_pos hr0 n)).mp hn
  refine ⟨P,?_⟩
  apply HasFPowerSeriesOnBall.hasFPowerSeriesAt (r := (r:ℝ≥0∞))
  refine ⟨P.le_radius_of_bound (∫sample,M sample ∂μ) hP,by exact_mod_cast hr,?_⟩
  intro y hy
  have hy0 : ‖y‖<(r:ℝ) := by
    apply (ENNReal.ofReal_lt_ofReal_iff hr0).mp
    simpa only [Metric.mem_eball,edist_dist,dist_zero_right,ENNReal.ofReal_coe_nnreal] using hy
  let B : ℕ→Ω→ℝ := fun n sample=>‖H sample‖*(‖L sample‖*‖y‖)^n/(n.factorial:ℝ)
  have hB (sample : Ω) : HasSum (fun n=>B n sample)
      (‖H sample‖*Real.exp (‖L sample‖*‖y‖)) := by
    convert (real_exp_hasSum (‖L sample‖*‖y‖)).mul_left ‖H sample‖ using 1 <;> simp [B,mul_div_assoc]
  have hBi : Integrable (fun sample=>∑'n,B n sample) μ := by
    simp_rw [(hB _).tsum_eq]
    apply hi.mono'
    · exact hH.norm.mul (Real.continuous_exp.comp_aestronglyMeasurable (hL.norm.mul_const ‖y‖))
    · refine .of_forall fun sample=>?_
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (by nlinarith [norm_nonneg (L sample)])) (norm_nonneg _)
  have hsum := hasSum_integral_of_dominated_convergence
    (F:=fun n sample=>laplaceTaylorTerm L H n sample (fun _=>y))
    (f:=fun sample=>H sample*NormedSpace.exp (L sample y)) B
    (fun n=>(ContinuousMultilinearMap.apply ℝ (fun _:Fin n=>E) A (fun _=>y)).continuous.comp_aestronglyMeasurable (hti n).aestronglyMeasurable)
    (fun n=>Filter.Eventually.of_forall fun sample=>by
      rw [laplaceTaylorTerm_apply]
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
      rw [norm_smul,Real.norm_of_nonneg (by positivity)]
      calc
        (n.factorial:ℝ)⁻¹*‖H sample*(L sample y)^n‖
          ≤(n.factorial:ℝ)⁻¹*(‖H sample‖*(‖L sample‖*‖y‖)^n) := by
            gcongr
            exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
              ((norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) ((L sample).le_opNorm y) n))
              (norm_nonneg _))
        _=B n sample := by simp only [B]; ring)
    (Filter.Eventually.of_forall fun sample=>(hB sample).summable)
    hBi (Filter.Eventually.of_forall fun sample=>by
      have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂:=ℝ) (L sample y)).mul_left (H sample)
      convert hs using 1
      ext n
      rw [laplaceTaylorTerm_apply]
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
      exact (mul_smul_comm _ _ _).symm)
  simp only [zero_add]
  convert hsum using 1
  ext n
  exact ContinuousMultilinearMap.integral_apply (hti n) (fun _=>y)

/-- Local analyticity at an arbitrary parameter, with the actual tilted
weight in the domination hypothesis. -/
theorem analyticAt_laplace_integral (L : Ω→E→L[ℝ] A) (H : Ω→A)
    (μ : Measure Ω) (hL : AEStronglyMeasurable L μ) (hH : AEStronglyMeasurable H μ)
    (p : E) (r : ℝ≥0) (hr : 0<r)
    (hi : Integrable (fun sample=>‖H sample*NormedSpace.exp (L sample p)‖*
      Real.exp ((r:ℝ)*‖L sample‖)) μ) :
    AnalyticAt ℝ (fun q : E=>∫sample,H sample*NormedSpace.exp (L sample q) ∂μ) p := by
  letI : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
  let H0 : Ω→A := fun sample=>H sample*NormedSpace.exp (L sample p)
  have hE : AEStronglyMeasurable (fun sample=>NormedSpace.exp (L sample p)) μ :=
    NormedSpace.exp_continuous.comp_aestronglyMeasurable
      ((ContinuousLinearMap.apply ℝ A p).continuous.comp_aestronglyMeasurable hL)
  have ha := analyticAt_laplace_integral_zero L H0 μ hL (hH.mul hE) r hr hi
  have hq : AnalyticAt ℝ (fun q : E=>q-p) p := analyticAt_id.sub analyticAt_const
  have ha0 : AnalyticAt ℝ (fun q : E=>∫sample,H0 sample*NormedSpace.exp (L sample q) ∂μ)
      (p-p) := by simpa only [sub_self] using ha
  have hc := ha0.comp (f:=fun q : E=>q-p) hq
  have he : (fun q : E=>∫sample,H0 sample*NormedSpace.exp (L sample (q-p)) ∂μ)=
      (fun q : E=>∫sample,H sample*NormedSpace.exp (L sample q) ∂μ) := by
    funext q
    apply integral_congr_ae
    exact .of_forall fun sample=>by
      change H sample*NormedSpace.exp (L sample p)*NormedSpace.exp (L sample (q-p)) = _
      rw [mul_assoc,←NormedSpace.exp_add]
      congr 2
      rw [←map_add]
      congr 1
      abel
  simpa only [Function.comp_def,he] using hc

end GeneralDepthPaper
