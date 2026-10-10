module

public import FourPapersCommon.ParisiGradientL1State

@[expose] public section


/-! A global linear CDF-L1 estimate for the genuine Parisi gradient.
Restarting at every field and time gives a deterministic weighted supremum
contraction. This includes arbitrary measures and every external field. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace FourPapersCommon
open Paper
set_option maxHeartbeats 1200000

def weightedGradientGap (β : ℝ) (μ ν : ParisiMeasure) (K : ℝ) : ℝ :=
  sSup (Set.range (fun p:Overlap×ℝ=>Real.exp (-K*(1-(p.1:ℝ)))*
    ‖parisiGradient β μ ((p.1:ℝ),p.2)-parisiGradient β ν ((p.1:ℝ),p.2)‖))

theorem weightedGradientGap_bddAbove (β : ℝ) (μ ν : ParisiMeasure) (K : ℝ) (hK : 0≤K) :
    BddAbove (Set.range (fun p:Overlap×ℝ=>Real.exp (-K*(1-(p.1:ℝ)))*
      ‖parisiGradient β μ ((p.1:ℝ),p.2)-parisiGradient β ν ((p.1:ℝ),p.2)‖)) := by
  refine ⟨2,?_⟩
  rintro v ⟨p,rfl⟩
  have he:Real.exp (-K*(1-(p.1:ℝ)))≤1:=Real.exp_le_one_iff.mpr (by nlinarith [p.1.property.2])
  have hg : ‖parisiGradient β μ ((p.1:ℝ),p.2)-parisiGradient β ν ((p.1:ℝ),p.2)‖≤2:=
    (norm_sub_le _ _).trans (by linarith [norm_parisiGradient_le_one β μ ((p.1:ℝ),p.2),
      norm_parisiGradient_le_one β ν ((p.1:ℝ),p.2)])
  simpa only [one_mul] using mul_le_mul he hg (norm_nonneg _) zero_le_one

theorem weightedGradientGap_nonneg (β : ℝ) (μ ν : ParisiMeasure) (K : ℝ) (hK : 0≤K) :
    0≤weightedGradientGap β μ ν K := by
  let p:Overlap×ℝ:=(⟨0,by norm_num,by norm_num⟩,0)
  have hm:=le_csSup (weightedGradientGap_bddAbove β μ ν K hK) (Set.mem_range_self p)
  exact (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)).trans hm

theorem gradient_le_weightedGradientGap (β : ℝ) (μ ν : ParisiMeasure) (K : ℝ)
    (hK : 0≤K) (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (x : ℝ) :
    ‖parisiGradient β μ (t,x)-parisiGradient β ν (t,x)‖≤
      weightedGradientGap β μ ν K*Real.exp (K*(1-t)) := by
  have hm:=le_csSup (weightedGradientGap_bddAbove β μ ν K hK)
    (Set.mem_range_self ((⟨t,ht⟩:Overlap),x))
  have hh:=mul_le_mul_of_nonneg_right hm (Real.exp_pos (K*(1-t))).le
  convert hh using 1
  · rw [mul_right_comm,←Real.exp_add];simp
  · rfl

theorem integrable_restart_terminal_tanh (β x : ℝ) (μ : ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) :
    Integrable (fun sample=>Real.tanh (canonicalParisiRestartState β x μ a ha.1
      (1-a).toNNReal sample)) canonicalBrownianMeasure := by
  have hc : Continuous Real.tanh:=continuous_iff_continuousAt.mpr
    (fun y=>(hasDerivAt_tanh y).continuousAt)
  have hm : Measurable (fun sample=>Real.tanh (canonicalParisiRestartState β x μ a ha.1
    (1-a).toNNReal sample)) := hc.measurable.comp
    ((measurable_canonicalParisiRestartState β x μ a ha.1).comp
      (f:=fun sample:BrownianSample=>((1-a).toNNReal,sample))
      (measurable_const.prodMk (measurable_id : Measurable (fun sample:BrownianSample=>sample))))
  exact (integrable_const (μ:=canonicalBrownianMeasure) (1:ℝ)).mono' hm.aestronglyMeasurable
    (.of_forall fun _=>by simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one _).le)

theorem weightedGradientGap_contraction (β : ℝ) (hβ : β≠0) (μ ν : ParisiMeasure) :
    weightedGradientGap β μ ν (2*β^2*Real.exp (β^2))≤
      β^2*Real.exp (β^2)*parisiCDFDistance μ ν+
        weightedGradientGap β μ ν (2*β^2*Real.exp (β^2))/2 := by
  let R:=β^2
  let C:=R*Real.exp R
  let K:=2*C
  let S:=weightedGradientGap β μ ν K
  have hR : 0<R:=sq_pos_of_ne_zero hβ
  have hC : 0<C:=mul_pos hR (Real.exp_pos R)
  have hK : 0<K:=mul_pos (by norm_num) hC
  have hS : 0≤S:=weightedGradientGap_nonneg β μ ν K hK.le
  rw [show 2*β^2*Real.exp (β^2)=K by dsimp only [K,C,R];ring]
  change S≤C*parisiCDFDistance μ ν+S/2
  apply csSup_le (Set.range_nonempty _) 
  rintro _ ⟨p,rfl⟩
  let a:ℝ:=p.1
  let T:=1-a
  have ha:a∈Icc (0:ℝ) 1:=p.1.property
  have hT : 0≤T:=by dsimp only [T];linarith [ha.2]
  have hT1 : T≤1:=by dsimp only [T];linarith [ha.1]
  let B:=R*parisiCDFDistance μ ν+R*S*(Real.exp (K*T)/K)
  have hB : 0≤B:=by have hD:=parisiCDFDistance_nonneg μ ν;dsimp only [B];positivity
  have hs (sample:BrownianSample) :
      ‖canonicalParisiRestartState β p.2 μ a ha.1 T.toNNReal sample-
        canonicalParisiRestartState β p.2 ν a ha.1 T.toNNReal sample‖≤B*Real.exp R := by
    have hb:=restartState_weighted_gradient_bound β p.2 μ ν a ha S K hS hK
      (gradient_le_weightedGradientGap β μ ν K hK.le) T ⟨hT,le_rfl⟩ sample
    exact hb.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith [hR.le,hT1])) hB)
  have hl:=Paper.lipschitzWith_tanh
  have hd : ‖parisiGradient β μ (a,p.2)-parisiGradient β ν (a,p.2)‖≤B*Real.exp R := by
    rw [parisiGradient_eq_restart_terminal_tanh β hβ μ a ha,
      parisiGradient_eq_restart_terminal_tanh β hβ ν a ha,
      ←integral_sub (integrable_restart_terminal_tanh β p.2 μ a ha)
        (integrable_restart_terminal_tanh β p.2 ν a ha)]
    have hpoint (sample:BrownianSample) :
        ‖Real.tanh (canonicalParisiRestartState β p.2 μ a ha.1 T.toNNReal sample)-
          Real.tanh (canonicalParisiRestartState β p.2 ν a ha.1 T.toNNReal sample)‖≤B*Real.exp R := by
      have htanh:=hl.dist_le_mul (canonicalParisiRestartState β p.2 μ a ha.1 T.toNNReal sample)
        (canonicalParisiRestartState β p.2 ν a ha.1 T.toNNReal sample)
      simp only [dist_eq_norm,NNReal.coe_one,one_mul] at htanh
      exact htanh.trans (hs sample)
    have hn:=norm_integral_le_of_norm_le_const (μ:=canonicalBrownianMeasure)
      (C:=B*Real.exp R) (.of_forall hpoint)
    simpa only [probReal_univ,one_mul,mul_one] using hn
  have he : Real.exp (-K*T)*Real.exp (K*T)=1:=by rw [←Real.exp_add];simp
  have hweighted:=mul_le_mul_of_nonneg_left hd (Real.exp_pos (-K*T)).le
  have hident : Real.exp (-K*T)*(B*Real.exp R)=
      C*parisiCDFDistance μ ν*Real.exp (-K*T)+S/2 := by
    have hratio : R*Real.exp R/K=(1/2:ℝ) := by
      change C/(2*C)=(1/2:ℝ)
      field_simp
    calc
      _=C*parisiCDFDistance μ ν*Real.exp (-K*T)+
        (R*Real.exp R/K)*S*(Real.exp (-K*T)*Real.exp (K*T)) := by dsimp only [B,C];ring
      _=_:=by rw [he,hratio];ring
  have he1 : Real.exp (-K*T)≤1:=Real.exp_le_one_iff.mpr (by nlinarith [hK.le,hT])
  change Real.exp (-K*T)*‖parisiGradient β μ (a,p.2)-parisiGradient β ν (a,p.2)‖≤_
  exact hweighted.trans (hident.le.trans (add_le_add
    (mul_le_of_le_one_right (mul_nonneg hC.le (parisiCDFDistance_nonneg μ ν)) he1) le_rfl))

def parisiGradientL1Constant (β : ℝ) : ℝ :=
  2*β^2*Real.exp (β^2)*Real.exp (2*β^2*Real.exp (β^2))

theorem parisiGradient_CDF_L1_bound (β : ℝ) (hβ : β≠0) (μ ν : ParisiMeasure)
    (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (x : ℝ) :
    ‖parisiGradient β μ (t,x)-parisiGradient β ν (t,x)‖≤
      parisiGradientL1Constant β*parisiCDFDistance μ ν := by
  let K:=2*β^2*Real.exp (β^2)
  have hK : 0≤K:=by dsimp only [K];positivity
  have hS:=weightedGradientGap_contraction β hβ μ ν
  have hs : weightedGradientGap β μ ν K≤2*β^2*Real.exp (β^2)*parisiCDFDistance μ ν:=by
    dsimp only [K];linarith
  have he:Real.exp (K*(1-t))≤Real.exp K:=Real.exp_le_exp.mpr (by nlinarith [ht.1])
  exact (gradient_le_weightedGradientGap β μ ν K hK t ht x).trans (by
    calc
      _≤(2*β^2*Real.exp (β^2)*parisiCDFDistance μ ν)*Real.exp K:=
        mul_le_mul hs he (Real.exp_pos _).le (by
          have hD:=parisiCDFDistance_nonneg μ ν;positivity)
      _=parisiGradientL1Constant β*parisiCDFDistance μ ν:=by dsimp only [parisiGradientL1Constant,K];ring)

end FourPapersCommon
