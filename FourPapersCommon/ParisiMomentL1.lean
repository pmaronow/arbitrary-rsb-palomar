module

public import FourPapersCommon.ParisiGradientL1
public import Paper.ParisiSelectedMoment

@[expose] public section


/-! The actual coupled diffusion and squared magnetization are globally
Lipschitz in the integrated CDF distance, uniformly in the initial field. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace FourPapersCommon
open Paper
set_option maxHeartbeats 900000

theorem parisiRestartMeasure_zero (μ:ParisiMeasure) :
    parisiRestartMeasure μ 0 (by norm_num)=μ := by
  have he : parisiRestartOverlap 0 (by norm_num)=id:=by
    funext q
    apply Subtype.ext
    simp only [parisiRestartOverlap,sub_zero,max_eq_left q.property.1,id_eq]
  apply ProbabilityMeasure.toMeasure_injective
  change (μ:Measure Overlap).map (parisiRestartOverlap 0 (by norm_num))=μ
  rw [he,Measure.map_id]

theorem restartState_zero_eq_selected (β h:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    (t:ℝ) (ht:t∈Icc (0:ℝ) 1) (sample:BrownianSample) :
    canonicalParisiRestartState β h μ 0 (by norm_num) t.toNNReal sample=
      selectedParisiStateReal β h hβ μ sample t := by
  have he : canonicalParisiRestartState β h μ 0 (by norm_num)=selectedParisiItoState β h hβ μ:=by
    unfold canonicalParisiRestartState
    rw [parisiRestartMeasure_zero]
    have hfun:parisiRestartGradient β μ 0=(fun s x=>parisiGradient β μ (s,x)):=by
      funext s x
      simp only [parisiRestartGradient,zero_add]
    unfold selectedParisiItoState
    congr 1
  rw [he,selectedParisiItoState_eq β h hβ μ
    (by simpa only [Real.coe_toNNReal _ ht.1] using ht.2),Real.coe_toNNReal _ ht.1]

theorem parisiGradientL1Constant_nonneg (β:ℝ) : 0≤parisiGradientL1Constant β:=by
  unfold parisiGradientL1Constant
  positivity

def parisiStateL1Constant (β:ℝ) : ℝ :=
  β^2*(1+parisiGradientL1Constant β*Real.exp 1)*Real.exp (β^2)

theorem parisiStateL1Constant_nonneg (β:ℝ) : 0≤parisiStateL1Constant β:=by
  have hL:=parisiGradientL1Constant_nonneg β
  unfold parisiStateL1Constant
  positivity

theorem selectedParisiState_CDF_L1_bound (β h:ℝ) (hβ:β≠0) (μ ν:ParisiMeasure)
    (t:ℝ) (ht:t∈Icc (0:ℝ) 1) (sample:BrownianSample) :
    ‖selectedParisiStateReal β h hβ μ sample t-selectedParisiStateReal β h hβ ν sample t‖≤
      parisiStateL1Constant β*parisiCDFDistance μ ν := by
  let S:=parisiGradientL1Constant β*parisiCDFDistance μ ν
  have hS:0≤S:=mul_nonneg (parisiGradientL1Constant_nonneg β) (parisiCDFDistance_nonneg μ ν)
  have hg:∀s∈Icc (0:ℝ) 1,∀y:ℝ,
      ‖parisiGradient β μ (s,y)-parisiGradient β ν (s,y)‖≤S*Real.exp (1*(1-s)) := by
    intro s hs y
    exact (parisiGradient_CDF_L1_bound β hβ μ ν s hs y).trans
      (le_mul_of_one_le_right hS (Real.one_le_exp_iff.mpr (by linarith [hs.2])))
  have hb:=restartState_weighted_gradient_bound β h μ ν 0 (by norm_num) S 1 hS (by norm_num)
    hg t (by simpa only [sub_zero] using ht) sample
  rw [restartState_zero_eq_selected β h hβ μ t ht,restartState_zero_eq_selected β h hβ ν t ht] at hb
  simp only [sub_zero,mul_one,div_one] at hb
  have he:Real.exp (β^2*t)≤Real.exp (β^2):=Real.exp_le_exp.mpr (by nlinarith [sq_nonneg β,ht.2])
  have hB:0≤β^2*parisiCDFDistance μ ν+β^2*S*Real.exp 1:=by
    have hD:=parisiCDFDistance_nonneg μ ν;positivity
  exact hb.trans ((mul_le_mul_of_nonneg_left he hB).trans_eq (by
    dsimp only [parisiStateL1Constant,S];ring))

def parisiMomentL1Constant (β:ℝ) : ℝ :=
  2*(parisiGradientL1Constant β+parisiStateL1Constant β)

theorem parisiMomentL1Constant_nonneg (β:ℝ) : 0≤parisiMomentL1Constant β:=by
  have hG:=parisiGradientL1Constant_nonneg β
  have hS:=parisiStateL1Constant_nonneg β
  unfold parisiMomentL1Constant
  positivity

theorem selectedParisiSecondMoment_CDF_L1_bound (β h:ℝ) (hβ:β≠0) (μ ν:ParisiMeasure)
    (t:ℝ) (ht:t∈Icc (0:ℝ) 1) :
    ‖selectedParisiSecondMoment β h hβ μ t-selectedParisiSecondMoment β h hβ ν t‖≤
      parisiMomentL1Constant β*parisiCDFDistance μ ν := by
  rw [selectedParisiSecondMoment,selectedParisiSecondMoment,←integral_sub
    (integrable_selectedParisiSecondMoment_integrand β h hβ μ t ht)
    (integrable_selectedParisiSecondMoment_integrand β h hβ ν t ht)]
  have hp (sample:BrownianSample) :
      ‖parisiGradient β μ (t,selectedParisiStateReal β h hβ μ sample t)^2-
        parisiGradient β ν (t,selectedParisiStateReal β h hβ ν sample t)^2‖≤
      parisiMomentL1Constant β*parisiCDFDistance μ ν := by
    let X:=selectedParisiStateReal β h hβ μ sample t
    let Y:=selectedParisiStateReal β h hβ ν sample t
    let u:=parisiGradient β μ (t,X)
    let v:=parisiGradient β ν (t,Y)
    have hl:‖parisiGradient β μ (t,X)-parisiGradient β μ (t,Y)‖≤‖X-Y‖:=by
      simpa only [dist_eq_norm,NNReal.coe_one,one_mul] using
        (lipschitzWith_parisiGradient_all β μ t).dist_le_mul X Y
    have huv:‖u-v‖≤(parisiGradientL1Constant β+parisiStateL1Constant β)*parisiCDFDistance μ ν:=by
      have hh:=(norm_sub_le_norm_sub_add_norm_sub u (parisiGradient β μ (t,Y)) v).trans
        (add_le_add (hl.trans (selectedParisiState_CDF_L1_bound β h hβ μ ν t ht sample))
          (parisiGradient_CDF_L1_bound β hβ μ ν t ht Y))
      convert hh using 1 <;>ring
    have hs:‖u+v‖≤2:=(norm_add_le u v).trans (by
      linarith [norm_parisiGradient_le_one β μ (t,X),norm_parisiGradient_le_one β ν (t,Y)])
    change ‖u^2-v^2‖≤_
    rw [show u^2-v^2=(u-v)*(u+v) by ring,norm_mul]
    exact (mul_le_mul huv hs (norm_nonneg _) (by
      have hG:=parisiGradientL1Constant_nonneg β;have hS:=parisiStateL1Constant_nonneg β
      have hD:=parisiCDFDistance_nonneg μ ν;positivity)).trans_eq (by
        dsimp only [parisiMomentL1Constant];ring)
  simpa only [probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ:=canonicalBrownianMeasure) (.of_forall hp)

end FourPapersCommon
