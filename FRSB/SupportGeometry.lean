module

public import Paper.JTVariational
public import Mathlib.Topology.Order.Compact

@[expose] public section


/-! Compact support geometry and genuine CDF masses at a putative support gap. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped Topology
namespace FRSB

def parisiSupport (μ : ParisiMeasure) : Set ℝ :=
  Subtype.val '' (μ : Measure Overlap).support

theorem parisiSupport_compact (μ : ParisiMeasure) : IsCompact (parisiSupport μ) :=
  (μ : Measure Overlap).isClosed_support.isCompact.image continuous_subtype_val

theorem parisiSupport_nonempty (μ : ParisiMeasure) : (parisiSupport μ).Nonempty := by
  apply Set.Nonempty.image
  apply (μ : Measure Overlap).nonempty_support
  intro hzero
  have h := measure_univ (μ := (μ : Measure Overlap))
  simp [hzero] at h

theorem parisiSupport_subset (μ : ParisiMeasure) : parisiSupport μ ⊆ Icc (0 : ℝ) 1 := by
  rintro x ⟨q, hq, rfl⟩
  exact q.property

theorem parisiSupport_extrema (μ : ParisiMeasure) :
    ∃ a q : ℝ, a ∈ parisiSupport μ ∧ q ∈ parisiSupport μ ∧
      ∀ x ∈ parisiSupport μ, a ≤ x ∧ x ≤ q := by
  obtain ⟨a, ha⟩ := (parisiSupport_compact μ).exists_isLeast (parisiSupport_nonempty μ)
  obtain ⟨q, hq⟩ := (parisiSupport_compact μ).exists_isGreatest (parisiSupport_nonempty μ)
  exact ⟨a, q, ha.1, hq.1, fun x hx => ⟨ha.2 hx, hq.2 hx⟩⟩

theorem compact_support_has_gap {S : Set ℝ} (hS : IsCompact S) {q x : ℝ}
    (hzero : 0 ∈ S) (hq : q ∈ S) (hx : x ∈ Icc (0 : ℝ) q) (hxS : x ∉ S) :
    ∃ a b : ℝ, a ∈ S ∧ b ∈ S ∧ a < x ∧ x < b ∧
      ∀ y ∈ Ioo a b, y ∉ S := by
  have hL : (S ∩ Iic x).Nonempty := ⟨0, hzero, hx.1⟩
  have hR : (S ∩ Ici x).Nonempty := ⟨q, hq, hx.2⟩
  obtain ⟨a, ha⟩ := (hS.inter_right isClosed_Iic).exists_isGreatest hL
  obtain ⟨b, hb⟩ := (hS.inter_right isClosed_Ici).exists_isLeast hR
  have hax : a < x := lt_of_le_of_ne ha.1.2 (by
    intro h
    exact hxS (h ▸ ha.1.1))
  have hxb : x < b := lt_of_le_of_ne hb.1.2 (by
    intro h
    exact hxS (h.symm ▸ hb.1.1))
  refine ⟨a, b, ha.1.1, hb.1.1, hax, hxb, ?_⟩
  intro y hy hyS
  by_cases hyx : y ≤ x
  · exact not_le_of_gt hy.1 (ha.2 ⟨hyS, hyx⟩)
  · exact not_le_of_gt hy.2 (hb.2 ⟨hyS, (lt_of_not_ge hyx).le⟩)

theorem parisiCDF_eq_zero_below_support (μ : ParisiMeasure) {a s : ℝ}
    (hmin : ∀ x ∈ parisiSupport μ, a ≤ x) (hs : s < a) : parisiCDF μ s = 0 := by
  have hset : {q : Overlap | (q : ℝ) ≤ s} ⊆ (μ : Measure Overlap).supportᶜ := by
    intro q hq hqs
    change (q : ℝ) ≤ s at hq
    have h := hmin q ⟨q, hqs, rfl⟩
    linarith
  have hz := measure_mono_null hset (μ : Measure Overlap).measure_compl_support
  simp only [parisiCDF, hz, ENNReal.toReal_zero]

theorem parisiCDF_constant_on_support_gap (μ : ParisiMeasure) {a b : ℝ}
    (hgap : ∀ x ∈ Ioo a b, x ∉ parisiSupport μ) {s : ℝ} (hs : s ∈ Ico a b) :
    parisiCDF μ s = parisiCDF μ a := by
  have heq : {q : Overlap | (q : ℝ) ≤ s} =ᵐ[(μ : Measure Overlap)]
      {q : Overlap | (q : ℝ) ≤ a} := by
    filter_upwards [Measure.support_mem_ae (μ := (μ : Measure Overlap))] with q hq
    apply propext
    constructor
    · intro hqs
      by_contra hqa
      exact hgap q ⟨lt_of_not_ge hqa, hqs.trans_lt hs.2⟩ ⟨q, hq, rfl⟩
    · intro hqa
      exact hqa.trans hs.1
  unfold parisiCDF
  rw [measure_congr heq]

theorem parisiCDF_positive_before_support_gap (μ : ParisiMeasure) {a b : ℝ}
    (hab : a < b) (ha : a ∈ parisiSupport μ)
    (hgap : ∀ x ∈ Ioo a b, x ∉ parisiSupport μ) : 0 < parisiCDF μ a := by
  obtain ⟨q, hq, hqa⟩ := ha
  let U : Set Overlap := {r | (r : ℝ) < b}
  have hU : IsOpen U := isOpen_lt continuous_subtype_val continuous_const
  have hqU : q ∈ U := by change (q : ℝ) < b; rw [hqa]; exact hab
  have hpos : 0 < (μ : Measure Overlap) U :=
    ((μ : Measure Overlap).mem_support_iff_forall q).mp hq U (hU.mem_nhds hqU)
  have heq : U =ᵐ[(μ : Measure Overlap)] {r : Overlap | (r : ℝ) ≤ a} := by
    filter_upwards [Measure.support_mem_ae (μ := (μ : Measure Overlap))] with r hr
    apply propext
    constructor
    · intro hrU
      by_contra hra
      exact hgap r ⟨lt_of_not_ge hra, hrU⟩ ⟨r, hr, rfl⟩
    · intro hra
      exact hra.trans_lt hab
  unfold parisiCDF
  rw [← measure_congr heq]
  exact ENNReal.toReal_pos hpos.ne' (measure_ne_top (μ : Measure Overlap) U)

end FRSB
