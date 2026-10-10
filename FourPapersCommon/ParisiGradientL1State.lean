module

public import FourPapersCommon.ParisiRestartMagnetization
public import FourPapersCommon.IntegralGronwall

@[expose] public section


/-! Same-Brownian restart stability with an actual integrated CDF error.
The exponential weight is a deterministic device for the global gradient
estimate; no supremum of random paths is integrated. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace FourPapersCommon
open Paper
set_option maxHeartbeats 900000

def parisiCDFDistance (μ ν : ParisiMeasure) : ℝ :=
  ∫ s in (0:ℝ)..1, ‖parisiCDF μ s-parisiCDF ν s‖

theorem parisiCDFDistance_nonneg (μ ν : ParisiMeasure) : 0≤parisiCDFDistance μ ν :=
  intervalIntegral.integral_nonneg zero_le_one (fun _ _=>norm_nonneg _)

theorem integral_restart_CDF_difference_le (μ ν : ParisiMeasure) (a r : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hr : r∈Icc (0:ℝ) (1-a)) :
    (∫ s in 0..r, ‖parisiCDF μ (a+s)-parisiCDF ν (a+s)‖)≤parisiCDFDistance μ ν := by
  rw [intervalIntegral.integral_comp_add_left
    (fun s:ℝ=>‖parisiCDF μ s-parisiCDF ν s‖) a,add_zero]
  apply intervalIntegral.integral_mono_interval ha.1 (by linarith [hr.1])
    (by linarith [hr.2]) (Filter.Eventually.of_forall (fun _=>norm_nonneg _))
    (parisiCDF_difference_intervalIntegrable μ ν 0 1)

theorem integral_exp_backward_weight_le (K T r : ℝ) (hK : 0<K) :
    (∫ s in (0:ℝ)..r, Real.exp (K*(T-s)))≤Real.exp (K*T)/K := by
  have hd (s:ℝ) : HasDerivAt (fun u:ℝ=> -(Real.exp (K*(T-u))/K))
      (Real.exp (K*(T-s))) s := by
    have h0 : HasDerivAt (fun u:ℝ=>Real.exp (K*(T-u)))
        (Real.exp (K*(T-s))*(-K)) s := by
      simpa only [Pi.sub_apply,id_eq,mul_neg_one,zero_sub] using
        (((hasDerivAt_const s T).sub (hasDerivAt_id s)).const_mul K).exp
    convert (h0.div_const K).neg using 1
    field_simp
  have hi : IntervalIntegrable (fun s:ℝ=>Real.exp (K*(T-s))) volume 0 r :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))).intervalIntegrable _ _
  have he:=intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _=>hd s) hi
  rw [he]
  simp only [sub_zero]
  have hp : 0≤Real.exp (K*(T-r))/K:=div_nonneg (Real.exp_pos _).le hK.le
  linarith

theorem restart_feedback_difference_le (β : ℝ) (μ ν : ParisiMeasure)
    (t X Y B : ℝ) (hB : ‖parisiGradient β μ (t,Y)-parisiGradient β ν (t,Y)‖≤B) :
    ‖parisiCDF μ t*parisiGradient β μ (t,X)-
      parisiCDF ν t*parisiGradient β ν (t,Y)‖≤
      ‖X-Y‖+B+‖parisiCDF μ t-parisiCDF ν t‖ := by
  have he : parisiCDF μ t*parisiGradient β μ (t,X)-parisiCDF ν t*parisiGradient β ν (t,Y)=
    parisiCDF μ t*(parisiGradient β μ (t,X)-parisiGradient β ν (t,Y))+
      (parisiCDF μ t-parisiCDF ν t)*parisiGradient β ν (t,Y) := by ring
  have hc : ‖parisiCDF μ t‖≤1:=by
    rw [Real.norm_of_nonneg (parisiCDF_nonneg μ t)];exact parisiCDF_le_one μ t
  have hl : ‖parisiGradient β μ (t,X)-parisiGradient β μ (t,Y)‖≤‖X-Y‖:=by
    simpa only [dist_eq_norm,NNReal.coe_one,one_mul] using
      (lipschitzWith_parisiGradient_all β μ t).dist_le_mul X Y
  have hg : ‖parisiGradient β μ (t,X)-parisiGradient β ν (t,Y)‖≤‖X-Y‖+B:=
    (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hl hB)
  rw [he]
  calc
    _≤‖parisiCDF μ t‖*‖parisiGradient β μ (t,X)-parisiGradient β ν (t,Y)‖+
      ‖parisiCDF μ t-parisiCDF ν t‖*‖parisiGradient β ν (t,Y)‖:=by
        simpa only [norm_mul] using norm_add_le
          (parisiCDF μ t*(parisiGradient β μ (t,X)-parisiGradient β ν (t,Y)))
          ((parisiCDF μ t-parisiCDF ν t)*parisiGradient β ν (t,Y))
    _≤1*(‖X-Y‖+B)+‖parisiCDF μ t-parisiCDF ν t‖*1:=
      add_le_add (mul_le_mul hc hg (norm_nonneg _) (by norm_num))
        (mul_le_mul_of_nonneg_left (norm_parisiGradient_le_one β ν _) (norm_nonneg _))
    _= _:=by ring

theorem restartState_weighted_gradient_bound (β x : ℝ) (μ ν : ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (S K : ℝ) (hS : 0≤S) (hK : 0<K)
    (hg : ∀t∈Icc (0:ℝ) 1,∀y:ℝ,
      ‖parisiGradient β μ (t,y)-parisiGradient β ν (t,y)‖≤S*Real.exp (K*(1-t)))
    (r : ℝ) (hr : r∈Icc (0:ℝ) (1-a)) (sample : BrownianSample) :
    ‖canonicalParisiRestartState β x μ a ha.1 r.toNNReal sample-
      canonicalParisiRestartState β x ν a ha.1 r.toNNReal sample‖≤
      (β^2*parisiCDFDistance μ ν+β^2*S*(Real.exp (K*(1-a))/K))*Real.exp (β^2*r) := by
  let X:=fun s:ℝ=>canonicalParisiRestartState β x μ a ha.1 s.toNNReal sample
  let Y:=fun s:ℝ=>canonicalParisiRestartState β x ν a ha.1 s.toNNReal sample
  let f:=fun s:ℝ=>‖X s-Y s‖
  have hX : Continuous X:=(continuous_canonicalParisiRestartState β x μ a ha.1 sample).comp continuous_real_toNNReal
  have hY : Continuous Y:=(continuous_canonicalParisiRestartState β x ν a ha.1 sample).comp continuous_real_toNNReal
  have hf : Continuous f:=(hX.sub hY).norm
  have hmono (ρ:ParisiMeasure) : Monotone (fun s:ℝ=>parisiCDF ρ (a+s)) :=
    fun _ _ h=>(parisiCDF_monotone ρ) (by linarith)
  have hd (ρ:ParisiMeasure) (Z:ℝ→ℝ) (hZ:Continuous Z) (u:ℝ) :
      IntervalIntegrable (fun s=>parisiCDF ρ (a+s)*parisiGradient β ρ (a+s,Z s)) volume 0 u :=
    (hmono ρ).intervalIntegrable.mul_continuousOn
      (((continuous_parisiGradient β ρ).comp ((continuous_const.add continuous_id).prodMk hZ)).continuousOn)
  have hCDF (u:ℝ) : IntervalIntegrable (fun s=>‖parisiCDF μ (a+s)-parisiCDF ν (a+s)‖) volume 0 u :=
    ((hmono μ).intervalIntegrable.sub (hmono ν).intervalIntegrable).norm
  have hw : Continuous (fun s:ℝ=>S*Real.exp (K*(1-a-s))):=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      ((continuous_const.sub continuous_const).sub continuous_id)))
  let δ:=β^2*parisiCDFDistance μ ν+β^2*S*(Real.exp (K*(1-a))/K)
  have hδ : 0≤δ:=by
    have hD:=parisiCDFDistance_nonneg μ ν
    dsimp only [δ];positivity
  have hb : ∀u∈Icc (0:ℝ) (1-a),f u≤δ+β^2*(∫s in 0..u,f s) := by
    intro u hu
    have hstate (ρ:ParisiMeasure) : canonicalParisiRestartState β x ρ a ha.1 u.toNNReal sample=
        x+β*canonicalBrownian u.toNNReal sample+
          β^2*∫s in (0:ℝ)..u,parisiCDF ρ (a+s)*parisiGradient β ρ
            (a+s,canonicalParisiRestartState β x ρ a ha.1 s.toNNReal sample) := by
      simpa only [Real.coe_toNNReal _ hu.1] using
        canonicalParisiRestartState_integral_equation β x ρ a ha.1 u.toNNReal
          (by rw [Real.coe_toNNReal _ hu.1];linarith [hu.2,ha.1]) sample
    have he : X u-Y u=β^2*∫s in 0..u,
        (parisiCDF μ (a+s)*parisiGradient β μ (a+s,X s)-
         parisiCDF ν (a+s)*parisiGradient β ν (a+s,Y s)) := by
      dsimp only [X,Y];rw [hstate μ,hstate ν,intervalIntegral.integral_sub (hd μ X hX u) (hd ν Y hY u)];ring
    have hm:=intervalIntegral.integral_mono_on hu.1 ((hd μ X hX u).sub (hd ν Y hY u)).norm
      (((hf.intervalIntegrable 0 u).add (hw.intervalIntegrable 0 u)).add (hCDF u))
      (fun s hs=>by
        apply restart_feedback_difference_le β μ ν (a+s) (X s) (Y s) _
        rw [show 1-a-s=1-(a+s) by ring]
        exact hg (a+s) ⟨by linarith [hs.1,ha.1],by linarith [hs.2,hu.2]⟩ (Y s))
    have hc:=integral_restart_CDF_difference_le μ ν a u ha hu
    have hwle:=mul_le_mul_of_nonneg_left (integral_exp_backward_weight_le K (1-a) u hK) hS
    rw [←intervalIntegral.integral_const_mul] at hwle
    rw [intervalIntegral.integral_add ((hf.intervalIntegrable 0 u).add (hw.intervalIntegrable 0 u)) (hCDF u),
      intervalIntegral.integral_add (hf.intervalIntegrable 0 u) (hw.intervalIntegrable 0 u)] at hm
    have hnorm:=intervalIntegral.norm_integral_le_integral_norm (μ:=volume) hu.1
      (f:=fun s=>parisiCDF μ (a+s)*parisiGradient β μ (a+s,X s)-
        parisiCDF ν (a+s)*parisiGradient β ν (a+s,Y s))
    dsimp only [f];rw [he,norm_mul,Real.norm_of_nonneg (sq_nonneg β)]
    dsimp only [δ]
    have htot:=hnorm.trans hm
    have hfin : (∫s in 0..u,‖parisiCDF μ (a+s)*parisiGradient β μ (a+s,X s)-
        parisiCDF ν (a+s)*parisiGradient β ν (a+s,Y s)‖)≤
        (∫s in 0..u,f s)+S*(Real.exp (K*(1-a))/K)+parisiCDFDistance μ ν:=by
      calc
        _≤(∫s in 0..u,f s)+(∫s in 0..u,S*Real.exp (K*(1-a-s)))+
          (∫s in 0..u,‖parisiCDF μ (a+s)-parisiCDF ν (a+s)‖):=hm
        _≤_:=add_le_add (add_le_add le_rfl hwle) hc
    have hscaled:=mul_le_mul_of_nonneg_left (hnorm.trans hfin) (sq_nonneg β)
    convert hscaled using 1 <;> ring
  exact le_exp_of_integral_le f hf (1-a) δ (β^2) hδ (sq_nonneg β)
    (fun _ _=>norm_nonneg _) hb r hr

end FourPapersCommon
