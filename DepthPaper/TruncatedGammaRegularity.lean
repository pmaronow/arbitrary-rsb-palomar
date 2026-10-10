module

public import DepthPaper.TruncatedGammaCell
public import FourPapersCommon.FiniteCellConstant

@[expose] public section


/-! Joining the actual Itô identities across all finite breakpoints. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal BoundedContinuousFunction ContDiff
namespace DepthPaper
open FourPapersCommon Paper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64
namespace TruncatedParisiData

def GammaSource {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) (t : ℝ) : ℝ :=
  d.covarianceField 2 t*d.Gamma2 t

def GammaPrimitive {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) (t : ℝ) : ℝ :=
  ∫s in 0..t,d.GammaSource s

@[fun_prop] theorem continuous_GammaSource {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) :
    Continuous d.GammaSource := (d.continuous_covarianceField 2).mul d.continuous_Gamma2

theorem hasDerivAt_GammaPrimitive {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) (t : ℝ) :
    HasDerivAt d.GammaPrimitive (d.GammaSource t) t :=
  intervalIntegral.integral_hasDerivAt_right (d.continuous_GammaSource.intervalIntegrable 0 t)
    d.continuous_GammaSource.aestronglyMeasurable.stronglyMeasurableAtFilter
    d.continuous_GammaSource.continuousAt

@[fun_prop] theorem continuous_GammaPrimitive {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) :
    Continuous d.GammaPrimitive := continuous_iff_continuousAt.mpr
      (fun t => (d.hasDerivAt_GammaPrimitive t).continuousAt)

theorem GammaPrimitive_sub {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) (a b : ℝ) :
    d.GammaPrimitive b-d.GammaPrimitive a = ∫s in a..b,d.GammaSource s := by
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (d.continuous_GammaSource.intervalIntegrable 0 a)
    (d.continuous_GammaSource.intervalIntegrable a b)
  change (∫s in 0..b,d.GammaSource s)-(∫s in 0..a,d.GammaSource s) = _
  linarith

theorem Gamma_minus_primitive_eq_cell_interior {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc)
    (i : Fin (r+1)) (a b : ℝ)
    (ha : a ∈ Ioo (d.node i.castSucc:ℝ) (d.node i.succ:ℝ))
    (hb : b ∈ Ioo (d.node i.castSucc:ℝ) (d.node i.succ:ℝ)) :
    d.Gamma b-d.GammaPrimitive b = d.Gamma a-d.GammaPrimitive a := by
  have hordered (x y : ℝ) (hx : x ∈ Ioo (d.node i.castSucc:ℝ) (d.node i.succ:ℝ))
      (hy : y ∈ Ioo (d.node i.castSucc:ℝ) (d.node i.succ:ℝ)) (hxy : x ≤ y) :
      d.Gamma y-d.GammaPrimitive y = d.Gamma x-d.GammaPrimitive x := by
    have hx0 : 0 ≤ x := ((d.node i.castSucc).property.1.trans hx.1.le)
    have hy0 : 0 ≤ y := hx0.trans hxy
    have he := d.Gamma_sub_eq_integral_cell_interior i x.toNNReal y.toNNReal
      (by simpa only [Real.coe_toNNReal x hx0] using hx.1)
      (Real.toNNReal_le_toNNReal hxy)
      (by simpa only [Real.coe_toNNReal y hy0] using hy.2)
    simp only [Real.coe_toNNReal x hx0,Real.coe_toNNReal y hy0] at he
    have hp := d.GammaPrimitive_sub x y
    change d.Gamma y-d.Gamma x = ∫s in x..y,d.GammaSource s at he
    linarith
  by_cases hab : a ≤ b
  · exact hordered a b ha hb hab
  · exact (hordered b a hb ha (not_le.mp hab).le).symm

theorem Gamma_minus_primitive_eq_cell {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc)
    (i : Fin (r+1)) (a b : ℝ)
    (ha : a ∈ Icc (d.node i.castSucc:ℝ) (d.node i.succ:ℝ))
    (hb : b ∈ Icc (d.node i.castSucc:ℝ) (d.node i.succ:ℝ)) :
    d.Gamma b-d.GammaPrimitive b = d.Gamma a-d.GammaPrimitive a := by
  have hlt : (d.node i.castSucc:ℝ) < (d.node i.succ:ℝ) :=
    d.node_strictMono Fin.castSucc_lt_succ
  let m := ((d.node i.castSucc:ℝ)+(d.node i.succ:ℝ))/2
  have hm : m ∈ Ioo (d.node i.castSucc:ℝ) (d.node i.succ:ℝ) := by
    dsimp [m]; constructor <;> linarith
  have he : EqOn (fun t => d.Gamma t-d.GammaPrimitive t)
      (fun _ => d.Gamma m-d.GammaPrimitive m)
      (Ioo (d.node i.castSucc:ℝ) (d.node i.succ:ℝ)) :=
    fun t ht => d.Gamma_minus_primitive_eq_cell_interior i m t hm ht
  have hc := he.closure (d.continuous_Gamma.sub d.continuous_GammaPrimitive) continuous_const
  rw [closure_Ioo hlt.ne] at hc
  exact (hc hb).trans (hc ha).symm

theorem Gamma_eq_initial_add_integral {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) qc) :
    d.Gamma t = d.Gamma 0+∫s in 0..t,d.covarianceField 2 s*d.Gamma2 s := by
  have he := finite_closed_cell_constant_of_pair (N := r+1)
    (fun j => (d.node j:ℝ)) (fun i j hij => d.node_strictMono.monotone hij)
    d.node_zero d.node_last (fun q => d.Gamma q-d.GammaPrimitive q)
    (fun i a ha b hb => d.Gamma_minus_primitive_eq_cell i a b ha hb) ht
  simp only [GammaPrimitive,intervalIntegral.integral_same,sub_zero] at he
  change d.Gamma t = d.Gamma 0+d.GammaPrimitive t
  unfold GammaPrimitive
  linarith

theorem hasDerivWithinAt_Gamma {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) qc) :
    HasDerivWithinAt d.Gamma (d.covarianceField 2 t*d.Gamma2 t) (Icc (0:ℝ) qc) t := by
  have hd : HasDerivWithinAt (fun q => d.Gamma 0+d.GammaPrimitive q) (d.GammaSource t)
      (Icc (0:ℝ) qc) t :=
    ((d.hasDerivAt_GammaPrimitive t).const_add (d.Gamma 0)).hasDerivWithinAt
  apply hd.congr
  · intro q hq
    exact d.Gamma_eq_initial_add_integral q hq
  · exact d.Gamma_eq_initial_add_integral t ht

theorem contDiffOn_Gamma {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) :
    ContDiffOn ℝ 1 d.Gamma (Icc (0:ℝ) qc) := by
  have hu := uniqueDiffOn_Icc d.qc_pos
  rw [contDiffOn_one_iff_derivWithin hu]
  refine ⟨fun t ht => (d.hasDerivWithinAt_Gamma t ht).differentiableWithinAt,?_⟩
  apply d.continuous_GammaSource.continuousOn.congr
  intro t ht
  exact (d.hasDerivWithinAt_Gamma t ht).derivWithin (hu t ht)

def firstVariationPrime {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) (t : ℝ) : ℝ :=
  (1/2:ℝ)*d.covarianceField 2 t*(d.Gamma t-t)

def firstVariationSecond {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) (t : ℝ) : ℝ :=
  (1/2:ℝ)*d.covarianceField 3 t*(d.Gamma t-t)+
    (1/2:ℝ)*d.covarianceField 2 t*(d.covarianceField 2 t*d.Gamma2 t-1)

@[fun_prop] theorem continuous_firstVariationSecond {r : ℕ} {qc : ℝ}
    (d : TruncatedParisiData r qc) : Continuous d.firstVariationSecond :=
  (((d.continuous_covarianceField 3).const_mul (1/2:ℝ)).mul
    (d.continuous_Gamma.sub continuous_id)).add
      (((d.continuous_covarianceField 2).const_mul (1/2:ℝ)).mul
        (d.continuous_GammaSource.sub continuous_const))

theorem hasDerivWithinAt_firstVariationPrime {r : ℕ} {qc : ℝ}
    (d : TruncatedParisiData r qc) (t : ℝ) (ht : t ∈ Icc (0:ℝ) qc) :
    HasDerivWithinAt d.firstVariationPrime (d.firstVariationSecond t) (Icc (0:ℝ) qc) t := by
  exact (((d.hasDerivWithinAt_covarianceField 2 t ht).const_mul (1/2:ℝ)).mul
    ((d.hasDerivWithinAt_Gamma t ht).sub (hasDerivAt_id t).hasDerivWithinAt)).congr_deriv
      (by simp only [firstVariationSecond,Pi.sub_apply,id_eq]; change
        (1/2:ℝ)*d.covarianceField 3 t*(d.Gamma t-t)+
          ((1/2:ℝ)*d.covarianceField 2 t)*(d.covarianceField 2 t*d.Gamma2 t-1) = _; ring)

theorem contDiffOn_firstVariation {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) :
    ContDiffOn ℝ 2 d.firstVariation (Icc (0:ℝ) qc) := by
  have hu := uniqueDiffOn_Icc d.qc_pos
  have he : EqOn (derivWithin d.firstVariation (Icc (0:ℝ) qc)) d.firstVariationPrime
      (Icc (0:ℝ) qc) := fun t ht =>
    (d.hasDerivAt_firstVariation t).hasDerivWithinAt.derivWithin (hu t ht)
  have hp : ContDiffOn ℝ 1 d.firstVariationPrime (Icc (0:ℝ) qc) := by
    rw [contDiffOn_one_iff_derivWithin hu]
    refine ⟨fun t ht => (d.hasDerivWithinAt_firstVariationPrime t ht).differentiableWithinAt,?_⟩
    apply d.continuous_firstVariationSecond.continuousOn.congr
    intro t ht
    exact (d.hasDerivWithinAt_firstVariationPrime t ht).derivWithin (hu t ht)
  change ContDiffOn ℝ ((1:ℕ∞ω)+1) _ _
  rw [contDiffOn_succ_iff_derivWithin hu]
  refine ⟨fun t _ => (d.hasDerivAt_firstVariation t).differentiableAt.differentiableWithinAt,
    by simp,?_⟩
  exact hp.congr he

end TruncatedParisiData
end DepthPaper
