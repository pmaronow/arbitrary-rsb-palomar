module

public import GeneralDepthPaper.CutoffHighVarianceDeficit
public import GeneralDepthPaper.EndpointDeficitLemma
public import DepthPaper.RevisedDoobComparison

@[expose] public section

/-! Revised Lemma 4.2: exact intermediate deficit bound. Unlike a
large-variance approximation, this applies at every elapsed variance,
including q=qc and q=Q. The proof combines the exact tanh comparison
with the actual Doob transition law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace GeneralDepthPaper
open FourPapersCommon
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 64

theorem revised_intermediate_deficit_two (Ξ:AdmissibleCovariance) {r:ℕ}
    (z:AtomicPoint r) (hz:IsAtomicPoint z) (m:ℝ) (hm:m∈Ioc (0:ℝ) 1)
    (Q:Overlap) (qc:ℝ) (hc:atomicLocation z (Fin.last r)<qc)
    (q:ℝ) (hq:q∈Ioc qc (Q:ℝ)) :
    1-Gamma Ξ (twoLevelMeasure z hz m Q) q≤
      2*Real.exp (-m^2*(Ξ.first q-Ξ.first qc)/2):=by
  let ν:=twoLevelMeasure z hz m Q
  let f:ℝ→ℝ:=fun y=>1-(gradient Ξ ν q y)^2
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
    mixedScalarTransition_twoLevel_eq_terminalDoob Ξ z hz m ⟨hm.1.le,hm.2⟩ Q qc hc q hq
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
  have hpoint:∀y,f y≤Paper.sech (m*y)^2:=by
    intro y
    dsimp only [f,ν]
    rw [gradient_twoLevelMeasure_top_derivative Ξ z hz m ⟨hm.1.le,hm.2⟩ Q qc hc q ⟨hq.1.le,hq.2⟩ y]
    exact DepthPaper.revised_coleHopf_gradient_sech_upper hm.1 hm.2 (W-t) y
  have hinner:∀x,(∫y,f y ∂K x)≤2*Real.exp (-m^2*(t:ℝ)/2):=by
    intro x
    have hi:Integrable f (K x):=(integrable_const (1:ℝ)).mono' hf.aestronglyMeasurable (.of_forall hfb)
    have hsm:Measurable (fun y=>Paper.sech (m*y)^2):=by unfold Paper.sech;fun_prop
    have hsi:Integrable (fun y=>Paper.sech (m*y)^2) (K x):=by
      apply (integrable_const (1:ℝ)).mono' hsm.aestronglyMeasurable
      exact .of_forall fun y=>by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact Paper.sech_sq_le_one _
    have hh:=integral_mono hi hsi hpoint
    rw [hKeq x] at hh
    rw [hKeq x]
    exact hh.trans (terminalDoob_scaledSech_upper hm.1 hm.2 W t htW x)
  have houter:Integrable (fun x=>∫y,f y ∂K x) ρ:=by
    have hmeas:StronglyMeasurable (fun x=>∫y,f y ∂K x):=
      ((hf.measurable.comp measurable_snd).stronglyMeasurable).integral_kernel_prod_right'
    apply (integrable_const (1:ℝ)).mono' hmeas.aestronglyMeasurable
    exact .of_forall fun x=>by
      simpa only [probReal_univ,mul_one] using
        (norm_integral_le_of_norm_le_const (μ:=K x) (.of_forall hfb))
  have hh:=integral_mono houter
    (integrable_const (2*Real.exp (-m^2*(t:ℝ)/2))) hinner
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at hh
  have hrep:=cutoff_deficit_representation Ξ z hz m ⟨hm.1.le,hm.2⟩ Q qc hc q hq
  have heq:(∫x,∫y,f y ∂K x ∂ρ)=1-Gamma Ξ ν q:=by
    rw [hrep]
    apply integral_congr_ae
    exact .of_forall fun x=>by
      dsimp only
      rw [hKeq x]
      apply integral_congr_ae
      exact .of_forall fun y=>by
        dsimp only [f,ν]
        rw [gradient_twoLevelMeasure_top_derivative Ξ z hz m ⟨hm.1.le,hm.2⟩ Q qc hc q ⟨hq.1.le,hq.2⟩ y]
  rw [heq,ht] at hh
  exact hh


theorem revised_intermediate_deficit (Ξ:AdmissibleCovariance) {r:ℕ}
    (z:AtomicPoint r) (hz:IsAtomicPoint z) (m:ℝ) (hm:m∈Ioc (0:ℝ) 1)
    (Q:Overlap) (qc:ℝ) (hc:atomicLocation z (Fin.last r)<qc)
    (q:ℝ) (hq:q∈Icc qc (Q:ℝ)) :
    1-Gamma Ξ (twoLevelMeasure z hz m Q) q≤
      4*Real.exp (-m^2*(Ξ.first q-Ξ.first qc)/2):=by
  rcases hq.1.eq_or_lt with h|h
  · subst q
    have H:=Gamma_nonneg Ξ (twoLevelMeasure z hz m Q) qc
    simpa only [sub_self,mul_zero,neg_zero,zero_div,Real.exp_zero,mul_one] using
      (show 1-Gamma Ξ (twoLevelMeasure z hz m Q) qc≤(4:ℝ) by linarith)
  · have H:=revised_intermediate_deficit_two Ξ z hz m hm Q qc hc q ⟨h,hq.2⟩
    exact H.trans (by nlinarith [Real.exp_pos (-m^2*(Ξ.first q-Ξ.first qc)/2)])

end GeneralDepthPaper
