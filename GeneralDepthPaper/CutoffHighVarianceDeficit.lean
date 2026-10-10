module

public import GeneralDepthPaper.CutoffDeficitRepresentation
public import GeneralDepthPaper.TerminalGradientApproximation
public import GeneralDepthPaper.DoobScaledSechBounds

@[expose] public section


/-! Uniform smoothing of the actual upper-region magnetization deficit.
The proof averages the genuine selected-state transition kernels. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace GeneralDepthPaper
open FourPapersCommon
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 64

theorem cutoff_high_variance_gradient_error {ε:ℝ} (hε:0 < ε):
    ∃C:ℝ,0 < C ∧ ∀Ξ:AdmissibleCovariance,∀r:ℕ,∀z:AtomicPoint r,∀hz:IsAtomicPoint z,
      ∀m∈Icc ε 1,∀Q:Overlap,∀qc:ℝ,atomicLocation z (Fin.last r) < qc→
        ∀q∈Icc qc (Q:ℝ),1 < Ξ.first Q-Ξ.first q→∀x:ℝ,
          |gradient Ξ (twoLevelMeasure z hz m Q) q x-Real.tanh (m*x)|≤
            C*Real.exp (-(ε^2)*(Ξ.first Q-Ξ.first q)/4):=by
  obtain ⟨C,hC,hb⟩:=coleHopf_gradient_uniform_exponential_error hε
  refine ⟨C,hC,?_⟩
  intro Ξ r z hz m hm Q qc hc q hq hV x
  rw [gradient_twoLevelMeasure_top_derivative Ξ z hz m ⟨hε.le.trans hm.1,hm.2⟩ Q qc hc q hq x]
  unfold terminalDoobPotential
  rw [cutoff_elapsed_variances Ξ Q (cutoff_pos z hz qc hc).le hq]
  exact hb m hm (Ξ.first Q-Ξ.first q) hV x

theorem cutoff_high_variance_deficit_bound {ε:ℝ} (hε:0 < ε):
    ∃C:ℝ,0 < C ∧ ∀Ξ:AdmissibleCovariance,∀r:ℕ,∀z:AtomicPoint r,∀hz:IsAtomicPoint z,
      ∀m∈Icc ε 1,∀Q:Overlap,∀qc:ℝ,atomicLocation z (Fin.last r) < qc→
        ∀q∈Ioc qc (Q:ℝ),1 < Ξ.first Q-Ξ.first q→
          1-Gamma Ξ (twoLevelMeasure z hz m Q) q≤
            2*Real.exp (-m^2*(Ξ.first q-Ξ.first qc)/2)+
              2*C*Real.exp (-(ε^2)*(Ξ.first Q-Ξ.first q)/4):=by
  obtain ⟨C,hC,hb⟩:=cutoff_high_variance_gradient_error hε
  refine ⟨C,hC,?_⟩
  intro Ξ r z hz m hm Q qc hc q hq hV
  let ν:=twoLevelMeasure z hz m Q
  let f:ℝ→ℝ:=fun y=>1-(gradient Ξ ν q y)^2
  let e:ℝ:=C*Real.exp (-(ε^2)*(Ξ.first Q-Ξ.first q)/4)
  let W:ℝ≥0:=(Ξ.first Q-Ξ.first qc).toNNReal
  let t:ℝ≥0:=(Ξ.first q-Ξ.first qc).toNNReal
  let K:=mixedScalarTransition Ξ.toEvenMixture ν qc q m
  let ρ:=Paper.canonicalBrownianMeasure.map (fun sample=>optimalState Ξ ν sample qc)
  have hc0:0≤qc:=(cutoff_pos z hz qc hc).le
  have hqu:q∈Icc (0:ℝ) 1:=⟨hc0.trans hq.1.le,hq.2.trans Q.property.2⟩
  have hcu:qc∈Icc (0:ℝ) 1:=⟨hc0,(hq.1.le.trans hq.2).trans Q.property.2⟩
  have hmeas:=measurable_mixedState Ξ.toEvenMixture 0 ν hcu
  letI:IsProbabilityMeasure ρ:=(Measure.isProbabilityMeasure_map_iff hmeas.aemeasurable).mpr inferInstance
  letI:IsMarkovKernel K:=isMarkovKernel_mixedScalarTransition Ξ.toEvenMixture ν qc q m hqu
  have htW:t≤W:=by
    dsimp only [t,W]
    apply Real.toNNReal_mono
    have hh:=Ξ.first_strictMonoOn.monotoneOn (hc0.trans hq.1.le) Q.property.1 hq.2
    linarith
  have ht:(t:ℝ)=Ξ.first q-Ξ.first qc:=by
    apply Real.coe_toNNReal
    exact sub_nonneg.mpr (Ξ.first_strictMonoOn.monotoneOn hc0 (hc0.trans hq.1.le) hq.1.le)
  have hKeq:∀x,K x=terminalDoobMeasure m W t x:=
    mixedScalarTransition_twoLevel_eq_terminalDoob Ξ z hz m ⟨hε.le.trans hm.1,hm.2⟩ Q qc hc q hq
  have hf:Continuous f:=by
    change Continuous (fun y=>1-Paper.parisiGradient (mixedBeta Ξ.toEvenMixture)
      (mixedMeasure Ξ.toEvenMixture ν) (Ξ.toEvenMixture.clock q,y)^2)
    exact continuous_const.sub (((Paper.continuous_parisiGradient _ _).comp
      (continuous_const.prodMk continuous_id)).pow 2)
  have hfb:∀y,‖f y‖≤1:=by
    intro y
    have hg:=norm_gradient_le_one Ξ ν q y
    have hs:(gradient Ξ ν q y)^2≤1:=by
      rw [Real.norm_eq_abs] at hg
      have hh:=pow_le_pow_left₀ (abs_nonneg (gradient Ξ ν q y)) hg 2
      simpa only [sq_abs,one_pow] using hh
    change ‖1-(gradient Ξ ν q y)^2‖≤1
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hs)]
    linarith [sq_nonneg (gradient Ξ ν q y)]
  have he:0≤e:=by dsimp only [e];positivity
  have hpoint:∀y,f y≤Paper.sech (m*y)^2+2*e:=by
    intro y
    have herr:=hb Ξ r z hz m hm Q qc hc q ⟨hq.1.le,hq.2⟩ hV y
    change |gradient Ξ ν q y-Real.tanh (m*y)|≤e at herr
    have hg:=norm_gradient_le_one Ξ ν q y
    rw [Real.norm_eq_abs] at hg
    have htanh:|Real.tanh (m*y)|≤1:=by
      exact abs_le.mpr ⟨(Real.neg_one_lt_tanh _).le,(Real.tanh_lt_one _).le⟩
    have hsum:|gradient Ξ ν q y+Real.tanh (m*y)|≤2:=
      (abs_add_le _ _).trans (by linarith)
    have hs:|(gradient Ξ ν q y)^2-(Real.tanh (m*y))^2|≤2*e:=by
      calc
        _=|gradient Ξ ν q y-Real.tanh (m*y)| * |gradient Ξ ν q y+Real.tanh (m*y)|:=by
          rw [←abs_mul];congr 1;ring
        _≤e*2:=mul_le_mul herr hsum (abs_nonneg _) he
        _=2*e:=by ring
    dsimp only [f]
    nlinarith [(abs_le.mp hs).1,Paper.tanh_sq_add_sech_sq (m*y)]
  have hinner:∀x,(∫y,f y ∂K x)≤2*Real.exp (-m^2*(t:ℝ)/2)+2*e:=by
    intro x
    have hi:Integrable f (K x):=(integrable_const (1:ℝ)).mono' hf.aestronglyMeasurable (.of_forall hfb)
    have hsm:Measurable (fun y=>Paper.sech (m*y)^2):=by unfold Paper.sech;fun_prop
    have hsi:Integrable (fun y=>Paper.sech (m*y)^2) (K x):=by
      apply (integrable_const (1:ℝ)).mono' hsm.aestronglyMeasurable
      exact .of_forall fun y=>by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact Paper.sech_sq_le_one _
    have hh:=integral_mono hi (hsi.add (integrable_const (2*e))) hpoint
    change (∫y,f y ∂K x)≤∫y,Paper.sech (m*y)^2+2*e ∂K x at hh
    rw [integral_add hsi (integrable_const (2*e)),integral_const,probReal_univ,smul_eq_mul,one_mul] at hh
    rw [hKeq x] at hh
    rw [hKeq x]
    exact hh.trans (add_le_add
      (terminalDoob_scaledSech_upper (hε.trans_le hm.1) hm.2 W t htW x) le_rfl)
  have houter:Integrable (fun x=>∫y,f y ∂K x) ρ:=by
    have hmeas:StronglyMeasurable (fun x=>∫y,f y ∂K x):=
      ((hf.measurable.comp measurable_snd).stronglyMeasurable).integral_kernel_prod_right'
    apply (integrable_const (1:ℝ)).mono' hmeas.aestronglyMeasurable
    exact .of_forall fun x=>by
      simpa only [probReal_univ,mul_one] using
        (norm_integral_le_of_norm_le_const (μ:=K x) (.of_forall hfb))
  have hh:=integral_mono houter
    (integrable_const (2*Real.exp (-m^2*(t:ℝ)/2)+2*e)) hinner
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at hh
  have hrep:=cutoff_deficit_representation Ξ z hz m ⟨hε.le.trans hm.1,hm.2⟩ Q qc hc q hq
  have heq:(∫x,∫y,f y ∂K x ∂ρ)=1-Gamma Ξ ν q:=by
    rw [hrep]
    apply integral_congr_ae
    exact .of_forall fun x=>by
      dsimp only
      rw [hKeq x]
      apply integral_congr_ae
      exact .of_forall fun y=>by
        dsimp only [f,ν]
        rw [gradient_twoLevelMeasure_top_derivative Ξ z hz m ⟨hε.le.trans hm.1,hm.2⟩ Q qc hc q ⟨hq.1.le,hq.2⟩ y]
  rw [heq,ht] at hh
  convert hh using 1 <;> dsimp only [e] <;> ring

end GeneralDepthPaper
