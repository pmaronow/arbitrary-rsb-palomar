module

public import DepthPaper.CutoffSelectedMoments
public import DepthPaper.TerminalDoobLaw
public import FourPapersCommon.MixedFiniteDiffusionLaw
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section


/-! Literal upper-region deficit representation in cutoff Lemma 4.1(c).
The transition is the genuine conditional h-transform of the selected
mixed diffusion. It is identified with the actual Appendix B kernel. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace DepthPaper
open FourPapersCommon ColeHopfFoundation.ProbabilityTheory
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

theorem cutoff_elapsed_variances (Ξ : AdmissibleCovariance) (Q : Overlap) {qc q : ℝ}
    (hc0 : 0≤qc) (hq : q∈Icc qc (Q:ℝ)) :
    (Ξ.first Q-Ξ.first qc).toNNReal-(Ξ.first q-Ξ.first qc).toNNReal=
      (Ξ.first Q-Ξ.first q).toNNReal := by
  have hqcq : Ξ.first qc≤Ξ.first q := Ξ.first_strictMonoOn.monotoneOn
    hc0 (hc0.trans hq.1) hq.1
  have hqQ : Ξ.first q≤Ξ.first Q := Ξ.first_strictMonoOn.monotoneOn
    (hc0.trans hq.1) Q.property.1 hq.2
  apply NNReal.coe_injective
  rw [NNReal.coe_sub (by
    rw [←NNReal.coe_le_coe,Real.coe_toNNReal _ (sub_nonneg.mpr hqcq),
      Real.coe_toNNReal _ (sub_nonneg.mpr (hqcq.trans hqQ))]
    linarith),Real.coe_toNNReal _ (sub_nonneg.mpr hqcq),
    Real.coe_toNNReal _ (sub_nonneg.mpr (hqcq.trans hqQ)),
    Real.coe_toNNReal _ (sub_nonneg.mpr hqQ)]
  ring

theorem gradient_twoLevelMeasure_top_derivative (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (Q : Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc)
    (q : ℝ) (hq : q∈Icc qc (Q:ℝ)) (x : ℝ) :
    gradient Ξ (twoLevelMeasure z hz m Q) q x=
      deriv (terminalDoobPotential m (Ξ.first Q-Ξ.first qc).toNNReal
        (Ξ.first q-Ξ.first qc).toNNReal) x := by
  have hc0:0≤qc:=(cutoff_pos z hz qc hc).le
  have hd:=(hasDerivAt_mixedPotential_spatial Ξ.toEvenMixture (twoLevelMeasure z hz m Q)
    q x ⟨hc0.trans hq.1,hq.2.trans Q.property.2⟩).sub_const ((Ξ.first 1-Ξ.first Q)/2)
  have he : (fun y=>potential Ξ (twoLevelMeasure z hz m Q) q y-(Ξ.first 1-Ξ.first Q)/2)=
      terminalDoobPotential m (Ξ.first Q-Ξ.first qc).toNNReal
        (Ξ.first q-Ξ.first qc).toNNReal := by
    funext y
    rw [potential_twoLevelMeasure_top_solution Ξ z hz m hm Q (hc.le.trans (hq.1.trans hq.2))
      q ⟨hc.le.trans hq.1,hq.2⟩ y]
    simp only [terminalDoobPotential,cutoff_elapsed_variances Ξ Q hc0 hq]
    ring
  change HasDerivAt
    (fun y=>potential Ξ (twoLevelMeasure z hz m Q) q y-(Ξ.first 1-Ξ.first Q)/2)
    (gradient Ξ (twoLevelMeasure z hz m Q) q x) x at hd
  rw [he] at hd
  exact hd.deriv.symm

theorem mixedScalarTransition_twoLevel_eq_terminalDoob (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (Q : Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc)
    (q : ℝ) (hq : q∈Ioc qc (Q:ℝ)) (x : ℝ) :
    mixedScalarTransition Ξ.toEvenMixture (twoLevelMeasure z hz m Q) qc q m x=
      terminalDoobMeasure m (Ξ.first Q-Ξ.first qc).toNNReal
        (Ξ.first q-Ξ.first qc).toNNReal x := by
  have hc0:0≤qc:=(cutoff_pos z hz qc hc).le
  have hcQ:=hq.1.le.trans hq.2
  have hcU:qc∈Icc (0:ℝ) 1:=⟨hc0,hcQ.trans Q.property.2⟩
  have hqU:q∈Icc (0:ℝ) 1:=⟨hc0.trans hq.1.le,hq.2.trans Q.property.2⟩
  have hmass:∀s∈Ico qc q,Paper.parisiCDF (twoLevelMeasure z hz m Q) s=m :=
    fun s hs=>parisiCDF_twoLevelMeasure_middle z hz m hm Q s
      ⟨hc.le.trans hs.1,hs.2.trans_le hq.2⟩
  rw [mixedScalarTransition_apply_actual Ξ.toEvenMixture _ hcU hqU hq.1 hmass,
    AdmissibleCovariance.toEvenMixture_first,AdmissibleCovariance.toEvenMixture_first]
  unfold terminalDoobMeasure
  congr 1
  funext y
  change ENNReal.ofReal (Real.exp (m*(potential Ξ (twoLevelMeasure z hz m Q) q y-
    potential Ξ (twoLevelMeasure z hz m Q) qc x)))=ENNReal.ofReal (terminalDoobWeight m _ _ x y)
  rw [potential_twoLevelMeasure_top_solution Ξ z hz m hm Q (hc.le.trans hcQ)
      q ⟨hc.le.trans hq.1.le,hq.2⟩ y,
    potential_twoLevelMeasure_top_solution Ξ z hz m hm Q (hc.le.trans hcQ) qc ⟨hc.le,hcQ⟩ x]
  simp only [terminalDoobWeight,terminalDoobPotential,tsub_zero,
    cutoff_elapsed_variances Ξ Q hc0 ⟨hq.1.le,hq.2⟩]
  congr 2
  ring

theorem cutoff_deficit_representation (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (Q : Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc)
    (q : ℝ) (hq : q∈Ioc qc (Q:ℝ)) :
    1-Gamma Ξ (twoLevelMeasure z hz m Q) q=
      ∫x,∫y,1-(deriv (terminalDoobPotential m (Ξ.first Q-Ξ.first qc).toNNReal
        (Ξ.first q-Ξ.first qc).toNNReal) y)^2
        ∂terminalDoobMeasure m (Ξ.first Q-Ξ.first qc).toNNReal
          (Ξ.first q-Ξ.first qc).toNNReal x
        ∂(Paper.canonicalBrownianMeasure.map (fun ω=>optimalState Ξ (twoLevelMeasure z hz m Q) ω qc)) := by
  let ν:=twoLevelMeasure z hz m Q
  let f:ℝ→ℝ:=fun y=>1-(gradient Ξ ν q y)^2
  have hc0:0≤qc:=(cutoff_pos z hz qc hc).le
  have hcU:qc∈Icc (0:ℝ) 1:=⟨hc0,(hq.1.le.trans hq.2).trans Q.property.2⟩
  have hqU:q∈Icc (0:ℝ) 1:=⟨hc0.trans hq.1.le,hq.2.trans Q.property.2⟩
  let ρ:=Paper.canonicalBrownianMeasure.map (fun ω=>optimalState Ξ ν ω qc)
  let lawq:=Paper.canonicalBrownianMeasure.map (fun ω=>optimalState Ξ ν ω q)
  have hmq:=measurable_mixedState Ξ.toEvenMixture 0 ν hqU
  have hmρ:=measurable_mixedState Ξ.toEvenMixture 0 ν hcU
  haveI:IsProbabilityMeasure lawq:=(Measure.isProbabilityMeasure_map_iff hmq.aemeasurable).mpr inferInstance
  haveI:IsProbabilityMeasure ρ:=(Measure.isProbabilityMeasure_map_iff hmρ.aemeasurable).mpr inferInstance
  have hf:Continuous f := by
    change Continuous (fun y=>1-Paper.parisiGradient (mixedBeta Ξ.toEvenMixture)
      (mixedMeasure Ξ.toEvenMixture ν) (Ξ.toEvenMixture.clock q,y)^2)
    exact continuous_const.sub (((Paper.continuous_parisiGradient _ _).comp
      (continuous_const.prodMk continuous_id)).pow 2)
  have hfb:∀y,‖f y‖≤2 := by
    intro y
    have hgrad:=norm_mixedGradient_le_one Ξ.toEvenMixture ν (q,y)
    calc
      _≤‖(1:ℝ)‖+‖gradient Ξ ν q y^2‖:=norm_sub_le _ _
      _≤2:=by rw [norm_pow,norm_one];change 1+‖mixedGradient Ξ.toEvenMixture ν (q,y)‖^2≤2;nlinarith [norm_nonneg (mixedGradient Ξ.toEvenMixture ν (q,y))]
  have hfi:Integrable f lawq:=(integrable_const (2:ℝ)).mono' hf.aestronglyMeasurable (ae_of_all _ hfb)
  have hsq:Integrable (fun ω=>gradient Ξ ν q (optimalState Ξ ν ω q)^2) Paper.canonicalBrownianMeasure := by
    have hfc:Continuous (fun y=>gradient Ξ ν q y^2):=by
      convert ((continuous_const (y:=(1:ℝ))).sub hf) using 1
      funext y
      dsimp [f]
      ring
    exact (integrable_const (1:ℝ)).mono' (hfc.measurable.comp hmq).aestronglyMeasurable
      (ae_of_all _ fun ω=>by
        rw [norm_pow]
        have hg:=norm_mixedGradient_le_one Ξ.toEvenMixture ν (q,optimalState Ξ ν ω q)
        change ‖mixedGradient Ξ.toEvenMixture ν (q,optimalState Ξ ν ω q)‖^2≤1
        nlinarith [norm_nonneg (mixedGradient Ξ.toEvenMixture ν (q,optimalState Ξ ν ω q))])
  have hlaw:=mixedState_constantMass_transitionLaw Ξ.toEvenMixture 0 ν hcU hqU hq.1
    (fun s hs=>parisiCDF_twoLevelMeasure_middle z hz m hm Q s
      ⟨hc.le.trans hs.1,hs.2.trans_le hq.2⟩)
  change lawq=mixedScalarTransition Ξ.toEvenMixture ν qc q m ∘ₘ ρ at hlaw
  have he : 1-Gamma Ξ ν q=∫y,f y ∂lawq := by
    dsimp only [lawq]
    change 1-Gamma Ξ ν q=∫y,f y
      ∂(Paper.canonicalBrownianMeasure.map (fun ω=>mixedState Ξ.toEvenMixture 0 ν ω q))
    rw [integral_map hmq.aemeasurable hf.aestronglyMeasurable]
    change 1-(∫ω,gradient Ξ ν q (optimalState Ξ ν ω q)^2 ∂Paper.canonicalBrownianMeasure)=_
    simp only [f]
    change 1-(∫ω,gradient Ξ ν q (optimalState Ξ ν ω q)^2 ∂Paper.canonicalBrownianMeasure)=
      ∫ω,1-gradient Ξ ν q (optimalState Ξ ν ω q)^2 ∂Paper.canonicalBrownianMeasure
    rw [integral_sub (integrable_const (1:ℝ)) hsq,integral_const]
    simp
  rw [he,hlaw,Measure.comp_eq_comp_const_apply,Kernel.integral_comp]
  · simp only [Kernel.const_apply]
    apply integral_congr_ae
    exact ae_of_all _ fun x=>by
      dsimp only [ν]
      rw [mixedScalarTransition_twoLevel_eq_terminalDoob Ξ z hz m hm Q qc hc q hq x]
      apply integral_congr_ae
      exact ae_of_all _ fun y=>by
        dsimp only [f,ν]
        rw [gradient_twoLevelMeasure_top_derivative Ξ z hz m hm Q qc hc q ⟨hq.1.le,hq.2⟩ y]
  · rw [←Measure.comp_eq_comp_const_apply,←hlaw]
    exact hfi

end DepthPaper
