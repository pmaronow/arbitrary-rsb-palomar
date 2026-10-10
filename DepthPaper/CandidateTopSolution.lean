module

public import DepthPaper.HighDegreeModel
public import DepthPaper.LargeVarianceNormalization

@[expose] public section


/-! Exact support and Cole–Hopf evolution above the lower atoms of the actual
two-level candidate. Zero upper mass (m=1) is included throughout. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace DepthPaper
open FourPapersCommon ColeHopfFoundation.ProbabilityTheory
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem twoLevelMeasure_support_upper {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (m : ℝ) (hm : m∈Icc (0:ℝ) 1) (Q : Overlap)
    (hQ : atomicLocation z (Fin.last r)≤(Q:ℝ)) :
    ∀x∈FRSB.parisiSupport (twoLevelMeasure z hz m Q),x≤(Q:ℝ) := by
  let ν:=twoLevelMeasure z hz m Q
  let S:Set Overlap:={q|(q:ℝ)≤(Q:ℝ)}
  have hS : IsClosed S := isClosed_le continuous_subtype_val continuous_const
  have hc : ((ν:Measure Overlap) S).toReal=1 :=
    parisiCDF_twoLevelMeasure_above z hz m hm Q hQ Q le_rfl
  have hmass : (ν:Measure Overlap) S=1 := (ENNReal.toReal_eq_one_iff _).mp hc
  have hnull : (ν:Measure Overlap) Sᶜ=0 := by
    rw [measure_compl hS.measurableSet (measure_ne_top _ _),hmass,measure_univ]
    simp
  have hs : (ν:Measure Overlap).support⊆S :=
    (ν:Measure Overlap).support_subset_of_isClosed hS (mem_ae_iff.mpr hnull)
  rintro x ⟨q,hq,rfl⟩
  exact hs hq

theorem potential_twoLevelMeasure_at_top (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (Q : Overlap) (hQ : atomicLocation z (Fin.last r)≤(Q:ℝ)) (x : ℝ) :
    potential Ξ (twoLevelMeasure z hz m Q) Q x=
      Real.log (Real.cosh x)+(Ξ.first 1-Ξ.first Q)/2 := by
  simpa only [potential,AdmissibleCovariance.toEvenMixture_first] using
    mixedPotential_terminal_region Ξ.toEvenMixture (twoLevelMeasure z hz m Q) Q.property
      (twoLevelMeasure_support_upper z hz m hm Q hQ) ⟨le_rfl,Q.property.2⟩ x

/-- The literal top-solution display, for every overlap from the last lower
atom through Q, including the top endpoint and zero upper mass. -/
theorem potential_twoLevelMeasure_top_solution (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (Q : Overlap) (hQ : atomicLocation z (Fin.last r)≤(Q:ℝ))
    (q : ℝ) (hq : q∈Icc (atomicLocation z (Fin.last r)) (Q:ℝ)) (x : ℝ) :
    potential Ξ (twoLevelMeasure z hz m Q) q x=
      (Ξ.first 1-Ξ.first Q)/2+
        coleHopf m (Ξ.first Q-Ξ.first q).toNNReal (fun y=>Real.log (Real.cosh y)) x := by
  by_cases he : q=(Q:ℝ)
  · subst q
    rw [potential_twoLevelMeasure_at_top Ξ z hz m hm Q hQ]
    simp only [sub_self,Real.toNNReal_zero,coleHopf_zero_var]
    ring
  have hqu : q∈Icc (0:ℝ) 1 :=
    ⟨(atomicLocation_mem_unit hz (Fin.last r)).1.trans hq.1,hq.2.trans Q.property.2⟩
  have hlt : q<(Q:ℝ) := lt_of_le_of_ne hq.2 he
  have hc : ∀s∈Ico q (Q:ℝ),Paper.parisiCDF (twoLevelMeasure z hz m Q) s=m :=
    fun s hs=>parisiCDF_twoLevelMeasure_middle z hz m hm Q s ⟨hq.1.trans hs.1,hs.2⟩
  have hu:=mixedPotential_coleHopf_on_constantCDF Ξ.toEvenMixture
    (twoLevelMeasure z hz m Q) hqu Q.property hlt hc x
  change potential Ξ (twoLevelMeasure z hz m Q) q x=
    coleHopf m (Ξ.toEvenMixture.first Q-Ξ.toEvenMixture.first q).toNNReal
      (fun y=>potential Ξ (twoLevelMeasure z hz m Q) Q y) x at hu
  simp_rw [potential_twoLevelMeasure_at_top Ξ z hz m hm Q hQ] at hu
  rw [AdmissibleCovariance.toEvenMixture_first,AdmissibleCovariance.toEvenMixture_first,
    coleHopf_add_const hasLinearGrowth_logCosh (by fun_prop)] at hu
  rw [hu]
  ring

end DepthPaper
