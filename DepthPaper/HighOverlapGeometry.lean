module

public import DepthPaper.HighOverlapTail
public import DepthPaper.HighOverlapIntermediate

@[expose] public section


/-! Strict terminal first-variation geometry for the actual selected Γ.
The root and lower-region inputs are precisely the conclusions of the
paper's endpoint-root and lower-geometry lemmas, rather than substitute
analytical or probabilistic hypotheses. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 1100000

theorem Gamma_sub_overlap_strictAntiOn (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    {a : ℝ} (ha : a∈Ioo (0:ℝ) 1)
    (hslope : ∀q∈Icc a 1,GammaPrime Ξ μ q≤1/2) :
    StrictAntiOn (fun q=>Gamma Ξ μ q-q) (Icc a 1) := by
  apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _)
    (((continuousOn_Gamma Ξ μ).mono (Icc_subset_Icc_left ha.1.le)).sub continuousOn_id)
    (f':=fun q=>GammaPrime Ξ μ q-1)
  · intro q hq
    rw [interior_Icc] at hq
    exact ((hasDerivAt_Gamma Ξ μ ⟨ha.1.trans hq.1,hq.2⟩).sub (hasDerivAt_id q)).hasDerivWithinAt
  · intro q hq
    rw [interior_Icc] at hq
    have hh:=hslope q ⟨hq.1.le,hq.2.le⟩
    linarith

theorem firstVariation_terminal_strict_geometry (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    {a Q : ℝ} (ha : a∈Ioo (0:ℝ) 1) (hQ : Q∈Ioo a 1)
    (hroot : Gamma Ξ μ Q=Q) (hslope : ∀q∈Icc a 1,GammaPrime Ξ μ q≤1/2) :
    StrictMonoOn (firstVariation Ξ μ) (Icc a Q) ∧
      StrictAntiOn (firstVariation Ξ μ) (Icc Q 1) ∧
        deriv (deriv (firstVariation Ξ μ)) Q<0 := by
  have hg:=Gamma_sub_overlap_strictAntiOn Ξ μ ha hslope
  have hQu : Q∈Ioo (0:ℝ) 1:=⟨ha.1.trans hQ.1,hQ.2⟩
  have hleft : ∀q∈Ioo a Q,0<Gamma Ξ μ q-q := by
    intro q hq
    have hh:=hg ⟨hq.1.le,hq.2.le.trans hQ.2.le⟩ ⟨hQ.1.le,hQ.2.le⟩ hq.2
    dsimp only at hh
    rw [hroot,sub_self] at hh
    exact hh
  have hright : ∀q∈Ioo Q 1,Gamma Ξ μ q-q<0 := by
    intro q hq
    have hh:=hg ⟨hQ.1.le,hQ.2.le⟩ ⟨hQ.1.le.trans hq.1.le,hq.2.le⟩ hq.1
    dsimp only at hh
    rw [hroot,sub_self] at hh
    exact hh
  have hmono : StrictMonoOn (firstVariation Ξ μ) (Icc a Q) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
      ((continuousOn_firstVariation Ξ μ).mono (Icc_subset_Icc ha.1.le hQ.2.le))
      (f':=firstVariationDerivative Ξ μ)
    · intro q hq
      rw [interior_Icc] at hq
      exact (hasDerivAt_firstVariation Ξ μ ⟨ha.1.trans hq.1,hq.2.trans hQ.2⟩).hasDerivWithinAt
    · intro q hq
      rw [interior_Icc] at hq
      exact mul_pos (mul_pos (by norm_num) (Ξ.second_pos (ha.1.trans hq.1))) (hleft q hq)
  have hanti : StrictAntiOn (firstVariation Ξ μ) (Icc Q 1) := by
    apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _)
      ((continuousOn_firstVariation Ξ μ).mono (Icc_subset_Icc_left hQu.1.le))
      (f':=firstVariationDerivative Ξ μ)
    · intro q hq
      rw [interior_Icc] at hq
      exact (hasDerivAt_firstVariation Ξ μ ⟨hQu.1.trans hq.1,hq.2⟩).hasDerivWithinAt
    · intro q hq
      rw [interior_Icc] at hq
      exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) (Ξ.second_pos (hQu.1.trans hq.1))) (hright q hq)
  have hdsecond : HasDerivAt Ξ.second (deriv Ξ.second Q) Q :=
    ((contDiff_covariance_second Ξ).differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hdscore : HasDerivAt (fun q=>Gamma Ξ μ q-q) (GammaPrime Ξ μ Q-1) Q :=
    (hasDerivAt_Gamma Ξ μ hQu).sub (hasDerivAt_id Q)
  have hd:=((hdsecond.const_mul (1/2:ℝ)).mul hdscore)
  have hdval : (1/2:ℝ)*deriv Ξ.second Q*(Gamma Ξ μ Q-Q)+
      (1/2:ℝ)*Ξ.second Q*(GammaPrime Ξ μ Q-1)=
        (1/2:ℝ)*Ξ.second Q*(GammaPrime Ξ μ Q-1) := by rw [hroot];ring
  have heq : (fun q=>(1/2:ℝ)*Ξ.second q*(Gamma Ξ μ q-q)) =ᶠ[𝓝 Q]
      deriv (firstVariation Ξ μ) := by
    filter_upwards [Ioo_mem_nhds hQu.1 hQu.2] with q hq
    exact (hasDerivAt_firstVariation Ξ μ hq).deriv.symm
  have hdd : HasDerivAt (deriv (firstVariation Ξ μ))
      ((1/2:ℝ)*Ξ.second Q*(GammaPrime Ξ μ Q-1)) Q := by
    rw [hdval] at hd
    exact hd.congr_of_eventuallyEq heq.symm
  have hn : GammaPrime Ξ μ Q-1<0 := by have hh:=hslope Q ⟨hQ.1.le,hQ.2.le⟩;linarith
  refine ⟨hmono,hanti,?_⟩
  rw [hdd.deriv]
  exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) (Ξ.second_pos hQu.1)) hn

theorem firstVariation_global_geometry (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    {qc a Q γ : ℝ} (hc : qc∈Ioo (0:ℝ) a) (ha : a∈Ioo (0:ℝ) 1)
    (hQ : Q∈Ioo a 1) (hγ : 0 < γ) (S : Set ℝ)
    (hlower : ∀q∈Icc (0:ℝ) qc,firstVariation Ξ μ q≤0 ∧
      (firstVariation Ξ μ q=0↔q∈S))
    (hS : S⊆Icc (0:ℝ) qc)
    (hinter : ∀q∈Icc qc a,firstVariation Ξ μ q≤-γ)
    (hroot : Gamma Ξ μ Q=Q) (hslope : ∀q∈Icc a 1,GammaPrime Ξ μ q≤1/2)
    (hvalue : firstVariation Ξ μ Q≤0) :
    (∀q∈Icc (0:ℝ) 1,firstVariation Ξ μ q≤0) ∧
      {q∈Icc (0:ℝ) 1|firstVariation Ξ μ q=0}=
        (if firstVariation Ξ μ Q=0 then S∪{Q} else S) := by
  obtain ⟨hm,ha',hdd⟩:=firstVariation_terminal_strict_geometry Ξ μ ha hQ hroot hslope
  have hterminal : ∀q∈Icc a 1,firstVariation Ξ μ q≤firstVariation Ξ μ Q ∧
      (q≠Q→firstVariation Ξ μ q<firstVariation Ξ μ Q) := by
    intro q hq
    rcases lt_trichotomy q Q with hlt|heq|hgt
    · have hh:=hm ⟨hq.1,hlt.le⟩ ⟨hQ.1.le,le_rfl⟩ hlt
      exact ⟨hh.le,fun _=>hh⟩
    · subst q;exact ⟨le_rfl,fun hn=>(hn rfl).elim⟩
    · have hh:=ha' ⟨le_rfl,hQ.2.le⟩ ⟨hgt.le,hq.2⟩ hgt
      exact ⟨hh.le,fun _=>hh⟩
  have hneg : ∀q∈Icc (0:ℝ) 1,firstVariation Ξ μ q≤0 := by
    intro q hq
    by_cases hqc:q≤qc
    · exact (hlower q ⟨hq.1,hqc⟩).1
    · by_cases hqa:q≤a
      · exact (hinter q ⟨(le_of_not_ge hqc),hqa⟩).trans (by linarith)
      · exact (hterminal q ⟨le_of_not_ge hqa,hq.2⟩).1.trans hvalue
  refine ⟨hneg,?_⟩
  ext q
  simp only [mem_setOf_eq,mem_inter_iff]
  by_cases hv:firstVariation Ξ μ Q=0
  · rw [if_pos hv]
    constructor
    · intro hq
      by_cases hqc:q≤qc
      · exact Or.inl ((hlower q ⟨hq.1.1,hqc⟩).2.mp hq.2)
      · by_cases hqa:q≤a
        · have hh:=hinter q ⟨le_of_not_ge hqc,hqa⟩
          rw [hq.2] at hh
          linarith
        · right
          by_contra hn
          have hh:=(hterminal q ⟨le_of_not_ge hqa,hq.1.2⟩).2 hn
          rw [hq.2,hv] at hh
          exact (lt_irrefl (0:ℝ)) hh
    · intro hq
      rcases hq with hs|hq
      · have hh:=hS hs
        exact ⟨⟨hh.1,hh.2.trans (hc.2.trans ha.2).le⟩,(hlower q hh).2.mpr hs⟩
      · subst q
        exact ⟨⟨ha.1.le.trans hQ.1.le,hQ.2.le⟩,hv⟩
  · rw [if_neg hv]
    constructor
    · intro hq
      by_cases hqc:q≤qc
      · exact (hlower q ⟨hq.1.1,hqc⟩).2.mp hq.2
      · by_cases hqa:q≤a
        · have hh:=hinter q ⟨le_of_not_ge hqc,hqa⟩
          rw [hq.2] at hh
          linarith
        · have hh:=(hterminal q ⟨le_of_not_ge hqa,hq.1.2⟩).1
          rw [hq.2] at hh
          exact (hv (le_antisymm hvalue hh)).elim
    · intro hs
      have hh:=hS hs
      exact ⟨⟨hh.1,hh.2.trans (hc.2.trans ha.2).le⟩,(hlower q hh).2.mpr hs⟩

end DepthPaper
