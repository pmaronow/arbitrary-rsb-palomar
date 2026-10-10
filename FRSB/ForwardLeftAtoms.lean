module

public import FRSB.ForwardBridgeParity
public import FRSB.ForwardBridgeApproximation

@[expose] public section


/-! The left forward gauge removes the atom at the observation time.
The endpoint bridge is exactly x, so this removal is a deterministic
factor and the actual left mass, not a CDF convention. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper
open scoped ContDiff Topology
namespace FRSB

def parisiLeftMass (μ : ParisiMeasure) (s : ℝ) : ℝ :=
  ((μ : Measure Overlap) {t : Overlap | (t : ℝ) < s}).toReal

def parisiAtomMass (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) : ℝ :=
  ((μ : Measure Overlap) {⟨s, hs.1.le, hs.2⟩}).toReal

lemma parisiAtomMass_nonneg (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    0 ≤ parisiAtomMass μ s hs := ENNReal.toReal_nonneg

lemma parisiCDF_eq_left_add_atom (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    parisiCDF μ s = parisiLeftMass μ s + parisiAtomMass μ s hs := by
  have hset : {t : Overlap | (t : ℝ) ≤ s} =
      {t : Overlap | (t : ℝ) < s} ∪ {⟨s, hs.1.le, hs.2⟩} := by
    ext t
    simp only [mem_setOf_eq, mem_union, mem_singleton_iff]
    constructor
    · intro ht
      rcases lt_or_eq_of_le ht with h | h
      · exact Or.inl h
      · exact Or.inr (Subtype.ext h)
    · rintro (h | h)
      · exact h.le
      · subst t; exact le_refl _
  have hd : Disjoint {t : Overlap | (t : ℝ) < s} {⟨s, hs.1.le, hs.2⟩} := by
    apply disjoint_left.mpr
    intro t ht he
    rw [mem_singleton_iff] at he
    subst t
    exact lt_irrefl s ht
  unfold parisiCDF parisiLeftMass parisiAtomMass
  rw [hset, measure_union hd (measurableSet_singleton _),
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]

lemma parisiAtomMass_eq_cdf_sub_left (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    parisiAtomMass μ s hs = parisiCDF μ s - parisiLeftMass μ s := by
  rw [parisiCDF_eq_left_add_atom μ s hs]
  ring

def forwardBridgeLeftAction (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) : ℝ :=
  ∫ t : Overlap, if (t : ℝ) < s then
    parisiPotential β μ (t, forwardBridgePoint β s hs path x t) else 0 ∂(μ : Measure Overlap)

lemma integrable_forwardBridgeLeftAction_integrand (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) :
    Integrable (fun t : Overlap => if (t : ℝ) < s then
      parisiPotential β μ (t, forwardBridgePoint β s hs path x t) else 0) (μ : Measure Overlap) := by
  have hp : Continuous (forwardBridgePoint β s hs path x) := by
    have hout := (continuous_forwardBridgePoint β s hs).comp
      (show Continuous (fun t : Overlap => ((path,x),t)) by fun_prop)
    simpa only [Function.comp_def] using hout
  have hcont : Continuous (fun t : Overlap => parisiPotential β μ
      (t, forwardBridgePoint β s hs path x t)) :=
    (continuous_parisiPotential β μ).comp (continuous_subtype_val.prodMk
      hp)
  apply (integrable_const (β ^ 2 + |x| + 2 * |β| * ‖path‖)).mono'
    ((hcont.measurable.ite (measurableSet_lt (by fun_prop) measurable_const) measurable_const).aestronglyMeasurable)
  exact .of_forall fun t => by
    split_ifs
    · rw [Real.norm_eq_abs]
      have hu := parisiPotential_absolute_growth β μ t (forwardBridgePoint β s hs path x t) t.property
      have hp := norm_forwardBridgePoint_le β s hs path x t
      rw [Real.norm_eq_abs] at hp
      linarith
    · simp only [norm_zero]
      positivity

lemma forwardBridgeAction_eq_left_add_atom (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) :
    forwardBridgeAction β μ s hs path x = forwardBridgeLeftAction β μ s hs path x +
      parisiAtomMass μ s hs * parisiPotential β μ (s,x) := by
  let q : Overlap := ⟨s,hs.1.le,hs.2⟩
  have he : (fun t : Overlap => if (t : ℝ) ≤ s then
      parisiPotential β μ (t, forwardBridgePoint β s hs path x t) else 0) =
      (fun t : Overlap => if (t : ℝ) < s then parisiPotential β μ (t, forwardBridgePoint β s hs path x t) else 0) +
      ({q} : Set Overlap).indicator (fun _ : Overlap => parisiPotential β μ (s,x)) := by
    funext t
    simp only [Pi.add_apply]
    by_cases hts : (t : ℝ) < s
    · have htq : t ∉ ({q} : Set Overlap) := by
        intro h
        have h' : t = q := mem_singleton_iff.mp h
        subst t
        exact lt_irrefl s hts
      simp only [if_pos hts.le, if_pos hts, indicator_of_notMem htq, add_zero]
    · by_cases hte : (t : ℝ) = s
      · have htq : t = q := Subtype.ext hte
        subst t
        simp only [q, if_pos (le_refl s), if_neg (lt_irrefl s), indicator_of_mem (mem_singleton _),
          zero_add, forwardBridgePoint_at_endpoint]
      · have hgt : s < (t : ℝ) := lt_of_le_of_ne (le_of_not_gt hts) (Ne.symm hte)
        have htq : t ∉ ({q} : Set Overlap) := by
          intro h
          exact hte (congrArg Subtype.val (mem_singleton_iff.mp h))
        simp only [if_neg (not_le.mpr hgt), if_neg hts, indicator_of_notMem htq, add_zero]
  unfold forwardBridgeAction forwardBridgeJet
  simp only [pow_zero, one_mul, parisiSpatialField]
  rw [he]
  simp only [Pi.add_def]
  rw [integral_add (integrable_forwardBridgeLeftAction_integrand β μ s hs path x)
      ((integrable_const _).indicator (measurableSet_singleton q)),
    integral_indicator_const _ (measurableSet_singleton q)]
  rfl

lemma forwardBridgeLeftAction_nonneg (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) :
    0 ≤ forwardBridgeLeftAction β μ s hs path x := by
  apply integral_nonneg
  intro t
  change 0 ≤ if (t : ℝ) < s then parisiPotential β μ (t, forwardBridgePoint β s hs path x t) else 0
  split_ifs
  · exact parisiPotential_nonneg β μ t _ t.property.2
  · exact le_refl 0

def forwardBridgeLeftFactor (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) : ℝ :=
  Real.exp (parisiAtomMass μ s hs * parisiPotential β μ (s,x)) * forwardBridgeFactor β μ s hs x

def forwardBridgeLeftCorrection (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) : ℝ :=
  forwardBridgeCorrection β μ s hs x - parisiAtomMass μ s hs * parisiPotential β μ (s,x)

lemma forwardBridgeLeftFactor_pos (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) : 0 < forwardBridgeLeftFactor β μ s hs x :=
  mul_pos (Real.exp_pos _) (forwardBridgeFactor_pos β μ s hs x)

lemma forwardBridgeLeftCorrection_eq_negativeLog (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    forwardBridgeLeftCorrection β μ s hs x = -Real.log (forwardBridgeLeftFactor β μ s hs x) := by
  simp only [forwardBridgeLeftCorrection, forwardBridgeLeftFactor, forwardBridgeCorrection,
    Real.log_mul (Real.exp_pos _).ne' (forwardBridgeFactor_pos β μ s hs x).ne', Real.log_exp]
  ring

lemma contDiff_forwardBridgeLeftCorrection (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) : ContDiff ℝ ∞ (forwardBridgeLeftCorrection β μ s hs) :=
  by
    have hu : ContDiff ℝ ∞ (fun x => parisiPotential β μ (s,x)) :=
      contDiff_parisiPotential_spatial β μ s ⟨hs.1.le,hs.2⟩
    exact (contDiff_forwardBridgeCorrection β μ s hs).sub (contDiff_const.mul hu)

lemma forwardBridgeLeftCorrection_even (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    forwardBridgeLeftCorrection β μ s hs (-x) = forwardBridgeLeftCorrection β μ s hs x := by
  simp only [forwardBridgeLeftCorrection, forwardBridgeCorrection_even,
    parisiPotential_even β μ s x ⟨hs.1.le,hs.2⟩]

lemma forwardBridgeLeftPathFactor_eq (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) :
    Real.exp (-forwardBridgeLeftAction β μ s hs path x) =
      Real.exp (parisiAtomMass μ s hs * parisiPotential β μ (s,x)) *
        forwardBridgePathFactor β μ s hs path x := by
  unfold forwardBridgePathFactor
  rw [← Real.exp_add, forwardBridgeAction_eq_left_add_atom]
  congr 1
  ring

lemma forwardBridgeLeftFactor_eq_integral (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    forwardBridgeLeftFactor β μ s hs x = ∫ path,
      Real.exp (-forwardBridgeLeftAction β μ s hs path x) ∂canonicalWienerMeasure := by
  simp_rw [forwardBridgeLeftPathFactor_eq]
  rw [integral_const_mul]
  rfl

lemma forwardBridgeLeftFactor_le_one (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) : forwardBridgeLeftFactor β μ s hs x ≤ 1 := by
  have hi : Integrable (fun path => Real.exp (-forwardBridgeLeftAction β μ s hs path x))
      canonicalWienerMeasure := by
    simp_rw [forwardBridgeLeftPathFactor_eq]
    exact (integrable_forwardBridgePathFactor β μ s hs x).const_mul _
  have hh := integral_mono hi (integrable_const (1 : ℝ))
    (fun path => Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (forwardBridgeLeftAction_nonneg β μ s hs path x)))
  rw [← forwardBridgeLeftFactor_eq_integral] at hh
  simpa [MeasureTheory.measureReal_def] using hh

lemma forwardBridgeLeftCorrection_nonneg (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) : 0 ≤ forwardBridgeLeftCorrection β μ s hs x := by
  rw [forwardBridgeLeftCorrection_eq_negativeLog]
  exact neg_nonneg.mpr (Real.log_nonpos (forwardBridgeLeftFactor_pos β μ s hs x).le
    (forwardBridgeLeftFactor_le_one β μ s hs x))

lemma iteratedDeriv_forwardBridgeLeftCorrection (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (x : ℝ) :
    iteratedDeriv j (forwardBridgeLeftCorrection β μ s hs) x =
      iteratedDeriv j (forwardBridgeCorrection β μ s hs) x -
        parisiAtomMass μ s hs * parisiSpatialField β μ j (s,x) := by
  have hu := contDiff_parisiPotential_spatial β μ s ⟨hs.1.le,hs.2⟩
  change iteratedDeriv j (forwardBridgeCorrection β μ s hs -
    (fun y => parisiAtomMass μ s hs * parisiPotential β μ (s,y))) x = _
  rw [iteratedDeriv_sub ((contDiff_forwardBridgeCorrection β μ s hs).of_le (by simp)).contDiffAt
    ((contDiff_const.mul hu).of_le (by simp)).contDiffAt,
    iteratedDeriv_const_mul _ (hu.of_le (by simp)).contDiffAt,
    ← parisiSpatialField_eq_iteratedDeriv β μ j s x ⟨hs.1.le,hs.2⟩]

lemma tendsto_parisiSpatialField_of_weak {A : Type*} {l : Filter A} [l.IsCountablyGenerated]
    (β : ℝ) (μ : ParisiMeasure) (ν : A → ParisiMeasure) (hν : Tendsto ν l (𝓝 μ))
    (j : ℕ) (s x : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun a => parisiSpatialField β (ν a) j (s,x)) l
      (𝓝 (parisiSpatialField β μ j (s,x))) := by
  have hd : Tendsto (fun a => parisiSpatialField β (ν a) j (s,x) - parisiSpatialField β μ j (s,x))
      l (𝓝 0) := squeeze_zero_norm
    (fun a => parisiSpatialField_measure_error_bound β (ν a) μ j s x hs)
    (tendsto_parisiSpatialMeasureError_of_weak β μ ν hν j)
  simpa only [sub_add_cancel, zero_add] using hd.add_const (parisiSpatialField β μ j (s,x))

/-- The actual left gauge converges in every spatial jet when both the
CDF and the endpoint singleton mass converge. Preserving quantizers
supply these masses exactly, including a terminal atom. -/
theorem tendsto_iteratedDeriv_forwardBridgeLeftCorrection_of_weak_masses
    {A : Type*} {l : Filter A} [l.IsCountablyGenerated] (β : ℝ) (μ : ParisiMeasure)
    (ν : A → ParisiMeasure) (hν : Tendsto ν l (𝓝 μ)) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (hα : Tendsto (fun a => parisiCDF (ν a) s) l (𝓝 (parisiCDF μ s)))
    (hδ : Tendsto (fun a => parisiAtomMass (ν a) s hs) l (𝓝 (parisiAtomMass μ s hs)))
    (j : ℕ) (x : ℝ) :
    Tendsto (fun a => iteratedDeriv j (forwardBridgeLeftCorrection β (ν a) s hs) x) l
      (𝓝 (iteratedDeriv j (forwardBridgeLeftCorrection β μ s hs) x)) := by
  simp_rw [iteratedDeriv_forwardBridgeLeftCorrection]
  exact (tendsto_iteratedDeriv_forwardBridgeCorrection_of_weak_cdf β μ ν hν s hs hα j x).sub
    (hδ.mul (tendsto_parisiSpatialField_of_weak β μ ν hν j s x ⟨hs.1.le,hs.2⟩))

lemma parisiAtomMass_le_one (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    parisiAtomMass μ s hs ≤ 1 := by
  have hh := ENNReal.toReal_mono (measure_ne_top (μ : Measure Overlap) univ)
    (measure_mono (subset_univ ({⟨s,hs.1.le,hs.2⟩} : Set Overlap)))
  simpa only [parisiAtomMass, measure_univ, ENNReal.toReal_one] using hh

def forwardBridgeLeftDerivativeConstant (β : ℝ) (j : ℕ) : ℝ :=
  negativeLogDerivativeConstant (forwardBridgeRelativeConstant β j) j + uniformSpatialConstant β (j - 1)

lemma forwardBridgeLeftDerivativeConstant_nonneg (β : ℝ) (j : ℕ) :
    0 ≤ forwardBridgeLeftDerivativeConstant β j :=
  add_nonneg (negativeLogDerivativeConstant_nonneg _ (forwardBridgeRelativeConstant_nonneg β j) j)
    (uniformSpatialConstant_pos β _).le

lemma forwardBridgeLeftCorrection_uniform_derivative_bound (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (hj : 1 ≤ j) (x : ℝ) :
    ‖iteratedDeriv j (forwardBridgeLeftCorrection β μ s hs) x‖ ≤ forwardBridgeLeftDerivativeConstant β j := by
  rw [iteratedDeriv_forwardBridgeLeftCorrection]
  have hfield : ‖parisiSpatialField β μ j (s,x)‖ ≤ uniformSpatialConstant β (j - 1) := by
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    simpa only [Nat.add_one_sub_one] using parisiSpatialField_uniform_bound β n μ (s,x)
  have hm : ‖parisiAtomMass μ s hs * parisiSpatialField β μ j (s,x)‖ ≤ uniformSpatialConstant β (j - 1) := by
    rw [norm_mul, Real.norm_of_nonneg (parisiAtomMass_nonneg μ s hs)]
    exact (mul_le_mul (parisiAtomMass_le_one μ s hs) hfield (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  exact (norm_sub_le _ _).trans (add_le_add
    (forwardBridgeCorrection_uniform_derivative_bound β μ s hs j hj x) hm)

end FRSB
