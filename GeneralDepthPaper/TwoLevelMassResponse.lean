module

public import GeneralDepthPaper.FirstVariation
public import GeneralDepthPaper.HighDegreeModel
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

@[expose] public section


/-! A genuine inward mass variation, including the disappearing upper atom
at mass one. It identifies the derivative of any smooth actual extension
with the first-variation difference. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators
namespace GeneralDepthPaper
set_option maxHeartbeats 600000

theorem twoLevelMeasure_mass_decrease_mix {r : ℕ} (z : AtomicPoint r)
    (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1) (Q : Overlap)
    (e : ℝ) (he : e∈Icc (0:ℝ) 1) :
    twoLevelMeasure z hz (m*(1-e)) Q =
      Paper.parisiMix (twoLevelMeasure z hz m Q) (Measure.dirac Q).toProbabilityMeasure e := by
  have hme : m*(1-e)∈Icc (0:ℝ) 1 :=
    ⟨mul_nonneg hm.1 (sub_nonneg.mpr he.2),
      (mul_le_mul_of_nonneg_left (show 1-e≤1 by linarith [he.1]) hm.1).trans (by simpa using hm.2)⟩
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  change (∫x,f x ∂(Paper.parisiMix (Measure.dirac Q).toProbabilityMeasure
    (atomicMeasure z hz) (m*(1-e)) : Measure Overlap))=
    ∫x,f x ∂(Paper.parisiMix (Paper.parisiMix (Measure.dirac Q).toProbabilityMeasure
      (atomicMeasure z hz) m) (Measure.dirac Q).toProbabilityMeasure e : Measure Overlap)
  rw [Paper.integral_parisiMix f.continuous _ _ _ hme,
    Paper.integral_parisiMix f.continuous _ _ _ he,
    Paper.integral_parisiMix f.continuous _ _ _ hm]
  simp only [Measure.toProbabilityMeasure,ProbabilityMeasure.toMeasure,integral_dirac]
  ring

theorem smooth_twoLevel_mass_response {r : ℕ} (Ξ : AdmissibleCovariance)
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Ioc (0:ℝ) 1)
    (Q : Overlap) (F : ℝ→ℝ) (D : ℝ) (hF : HasDerivAt F D m)
    (heq : ∀s∈Ioc (0:ℝ) 1,F s=twoLevelFunctional Ξ z hz s Q) :
    D=firstVariation Ξ (twoLevelMeasure z hz m Q) Q-
      ∫q:Overlap,firstVariation Ξ (twoLevelMeasure z hz m Q) q
        ∂(atomicMeasure z hz : Measure Overlap) := by
  let μ:=twoLevelMeasure z hz m Q
  have hd:HasDerivAt (fun e:ℝ=>F (m*(1-e))) (-m*D) 0 := by
    have hi:HasDerivAt (fun e:ℝ=>m*(1-e)) (-m) 0 := by
      convert ((hasDerivAt_const (0:ℝ) 1).sub (hasDerivAt_id (0:ℝ))).const_mul m using 1 <;> simp
    have hF':HasDerivAt F D (m*(1-(0:ℝ))) := by simpa using hF
    simpa only [Function.comp_def,neg_mul,mul_comm D] using hF'.comp 0 hi
  have hv:=hasDerivWithinAt_parisiFunctional_mix Ξ μ (Measure.dirac Q).toProbabilityMeasure
  have hloc:(fun e:ℝ=>F (m*(1-e)))=ᶠ[𝓝[Ioi (0:ℝ)] 0]
      (fun e=>parisiFunctional Ξ (Paper.parisiMix μ (Measure.dirac Q).toProbabilityMeasure e)) := by
    have hh:∀ᶠe:ℝ in 𝓝 (0:ℝ),e<1 := eventually_lt_nhds (by norm_num)
    filter_upwards [hh.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with e he he0
    have hme:m*(1-e)∈Ioc (0:ℝ) 1 :=
      ⟨mul_pos hm.1 (sub_pos.mpr he),by nlinarith [hm.2, mul_pos hm.1 he0]⟩
    rw [heq _ hme,twoLevelFunctional,twoLevelMeasure_mass_decrease_mix z hz m
      ⟨hm.1.le,hm.2⟩ Q e ⟨he0.le,he.le⟩]
  have hder:=hd.hasDerivWithinAt.congr_of_eventuallyEq hloc.symm
    (by simpa only [Paper.parisiMix_zero,sub_zero,mul_one,μ,twoLevelFunctional] using (heq m hm).symm)
  have hsame : -m*D=-(∫q:Overlap,firstVariation Ξ μ q ∂((Measure.dirac Q).toProbabilityMeasure : Measure Overlap)-
      ∫q:Overlap,firstVariation Ξ μ q ∂(μ : Measure Overlap)) := by
    rw [←hder.derivWithin (uniqueDiffWithinAt_Ioi 0),←hv.derivWithin (uniqueDiffWithinAt_Ioi 0)]
  have hf:=continuous_firstVariation_overlap Ξ μ
  have hdirac:(∫q:Overlap,firstVariation Ξ μ q ∂((Measure.dirac Q).toProbabilityMeasure : Measure Overlap))=
      firstVariation Ξ μ Q := by
    change (∫q:Overlap,firstVariation Ξ μ q ∂(Measure.dirac Q))=_
    exact integral_dirac _ _
  have hint:(∫q:Overlap,firstVariation Ξ μ q ∂(μ : Measure Overlap))=
      (1-m)*firstVariation Ξ μ Q+m*(∫q:Overlap,firstVariation Ξ μ q
        ∂(atomicMeasure z hz : Measure Overlap)) := by
    change (∫q:Overlap,firstVariation Ξ μ q ∂(Paper.parisiMix (Measure.dirac Q).toProbabilityMeasure
      (atomicMeasure z hz) m : Measure Overlap))=_
    rw [Paper.integral_parisiMix hf _ _ _ ⟨hm.1.le,hm.2⟩]
    rw [hdirac]
  rw [hdirac] at hsame
  rw [hint] at hsame
  dsimp only [μ] at hsame ⊢
  apply mul_left_cancel₀ hm.1.ne' (b:=D)
  linear_combination -hsame

end GeneralDepthPaper
