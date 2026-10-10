module

public import FRSB.ForwardBridgeDensity
public import FRSB.PotentialMeasureContinuity

@[expose] public section


/-! The endpoint-vanishing exponent removes the discontinuity caused by
an atom at the observation time.  The concrete bridge density is continuous
under genuine weak convergence of arbitrary probability measures. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper Filter
open scoped ContDiff Topology
namespace FRSB

def forwardBridgeEndpointDifference (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) (t : Overlap) : ℝ :=
  if (t : ℝ) ≤ s then parisiPotential β μ (s, x) -
    parisiPotential β μ (t, forwardBridgePoint β s hs path x t) else 0

theorem continuous_forwardBridgeEndpointDifference (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) :
    Continuous (forwardBridgeEndpointDifference β μ s hs path x) := by
  apply Continuous.if_le
  · exact continuous_const.sub ((continuous_parisiPotential β μ).comp
      (continuous_subtype_val.prodMk ((continuous_forwardBridgePoint β s hs).comp
        (show Continuous (fun t : Overlap => ((path, x), t)) by fun_prop))))
  · exact continuous_const
  · exact continuous_subtype_val
  · exact continuous_const
  · intro t ht
    have he : t = (⟨s, hs.1.le, hs.2⟩ : Overlap) := Subtype.ext ht
    rw [he, forwardBridgePoint_at_endpoint]
    simp

def forwardBridgeExponent (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) : ℝ :=
  ∫ t, forwardBridgeEndpointDifference β μ s hs path x t ∂(μ : Measure Overlap)

lemma integrable_forwardBridgeEndpointDifference (β : ℝ) (μ ν : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) :
    Integrable (forwardBridgeEndpointDifference β μ s hs path x) (ν : Measure Overlap) := by
  obtain ⟨C, hC⟩ := (isCompact_univ : IsCompact (univ : Set Overlap)).exists_bound_of_continuousOn
    (continuous_forwardBridgeEndpointDifference β μ s hs path x).continuousOn
  exact (integrable_const C).mono'
    (continuous_forwardBridgeEndpointDifference β μ s hs path x).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => hC t (mem_univ t))

theorem forwardBridgeExponent_eq (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) :
    forwardBridgeExponent β μ s hs path x =
      parisiCDF μ s * parisiPotential β μ (s, x) - forwardBridgeAction β μ s hs path x := by
  let S : Set Overlap := {t | (t : ℝ) ≤ s}
  have hS : MeasurableSet S := measurableSet_le (by fun_prop) measurable_const
  have hi0 := (integrable_const (parisiPotential β μ (s, x)) :
      Integrable (fun _ : Overlap => parisiPotential β μ (s, x)) (μ : Measure Overlap)).indicator hS
  have hi1 := integrable_forwardBridgeJet_integrand β μ s hs 0 path x
  have he : forwardBridgeEndpointDifference β μ s hs path x =
      S.indicator (fun _ => parisiPotential β μ (s, x)) -
        (fun t : Overlap => if (t : ℝ) ≤ s then forwardBridgeFraction s t ^ 0 *
          parisiSpatialField β μ 0 (t, forwardBridgePoint β s hs path x t) else 0) := by
    funext t
    simp only [forwardBridgeEndpointDifference, S, Set.indicator_apply,
      mem_setOf_eq, pow_zero, one_mul, parisiSpatialField, Pi.sub_apply]
    split_ifs <;> simp
  unfold forwardBridgeExponent
  rw [he]
  simp only [Pi.sub_apply]
  rw [integral_sub hi0 hi1, integral_indicator_const _ hS]
  rfl

theorem continuous_forwardBridgeExponent (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    Continuous (fun path => forwardBridgeExponent β μ s hs path x) := by
  have he : (fun path => forwardBridgeExponent β μ s hs path x) =
      fun path => parisiCDF μ s * parisiPotential β μ (s, x) -
        forwardBridgeAction β μ s hs path x := funext (forwardBridgeExponent_eq β μ s hs · x)
  rw [he]
  have hout := (continuous_forwardBridgeJet β μ s hs 0).comp
    (show Continuous (fun path : ForwardBridgePath => (path, x)) by fun_prop)
  have hsub := (continuous_const : Continuous (fun _ : ForwardBridgePath =>
    parisiCDF μ s * parisiPotential β μ (s, x))).sub hout
  convert hsub using 1
  funext path
  rfl

theorem forwardBridgeDensity_eq_exponent (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    forwardBridgeDensity β μ s hs x = heatDensity (β ^ 2 * s) x *
      ∫ path, Real.exp (forwardBridgeExponent β μ s hs path x) ∂canonicalWienerMeasure := by
  have he : (fun path => Real.exp (forwardBridgeExponent β μ s hs path x)) =
      fun path => Real.exp (parisiCDF μ s * parisiPotential β μ (s, x)) *
        forwardBridgePathFactor β μ s hs path x := by
    funext path
    rw [forwardBridgeExponent_eq, sub_eq_add_neg, Real.exp_add]
    rfl
  rw [he, integral_const_mul]
  unfold forwardBridgeDensity forwardBridgeFactor
  ring

theorem forwardBridgeExponent_upper_bound (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) :
    forwardBridgeExponent β μ s hs path x ≤ β ^ 2 + |x| := by
  rw [forwardBridgeExponent_eq]
  have hα := mul_le_of_le_one_left (parisiPotential_nonneg β μ s x hs.2) (parisiCDF_le_one μ s)
  have hu := parisiPotential_absolute_growth β μ s x ⟨hs.1.le, hs.2⟩
  have ha := forwardBridgeAction_nonneg β μ s hs path x
  linarith [le_abs_self (parisiPotential β μ (s, x))]

lemma forwardBridgeExponent_measure_error (β : ℝ) (μ ν : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) :
    ‖forwardBridgeExponent β ν s hs path x -
      ∫ t, forwardBridgeEndpointDifference β μ s hs path x t ∂(ν : Measure Overlap)‖ ≤
        2 * parisiPotentialMeasureError β ν μ := by
  have hiν := integrable_forwardBridgeEndpointDifference β ν ν s hs path x
  have hiμ := integrable_forwardBridgeEndpointDifference β μ ν s hs path x
  have hsub := integral_sub hiν hiμ
  unfold forwardBridgeExponent
  rw [← hsub]
  have hb : ∀ t : Overlap,
      ‖forwardBridgeEndpointDifference β ν s hs path x t -
        forwardBridgeEndpointDifference β μ s hs path x t‖ ≤
          2 * parisiPotentialMeasureError β ν μ := by
    intro t
    unfold forwardBridgeEndpointDifference
    split_ifs
    · have h1 := parisiPotential_measure_error_bound β ν μ s x ⟨hs.1.le, hs.2⟩
      have h2 := parisiPotential_measure_error_bound β ν μ t
        (forwardBridgePoint β s hs path x t) t.property
      have hh := norm_sub_le (parisiPotential β ν (s, x) - parisiPotential β μ (s, x))
        (parisiPotential β ν (t, forwardBridgePoint β s hs path x t) -
          parisiPotential β μ (t, forwardBridgePoint β s hs path x t))
      have he : parisiPotential β ν (s, x) - parisiPotential β ν (t, forwardBridgePoint β s hs path x t) -
          (parisiPotential β μ (s, x) - parisiPotential β μ (t, forwardBridgePoint β s hs path x t)) =
          (parisiPotential β ν (s, x) - parisiPotential β μ (s, x)) -
          (parisiPotential β ν (t, forwardBridgePoint β s hs path x t) -
            parisiPotential β μ (t, forwardBridgePoint β s hs path x t)) := by ring
      rw [he]
      linarith
    · have hn := (norm_nonneg _).trans (parisiPotential_measure_error_bound β ν μ s x ⟨hs.1.le, hs.2⟩)
      simp only [sub_self, norm_zero]
      linarith
  exact (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hb)).trans_eq (by simp)

theorem tendsto_forwardBridgeExponent_of_weak {A : Type*} {l : Filter A}
    [l.IsCountablyGenerated] (β : ℝ) (μ : ParisiMeasure) (ν : A → ParisiMeasure)
    (hν : Tendsto ν l (𝓝 μ)) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (path : ForwardBridgePath) (x : ℝ) :
    Tendsto (fun a => forwardBridgeExponent β (ν a) s hs path x) l
      (𝓝 (forwardBridgeExponent β μ s hs path x)) := by
  let H : C(Overlap, ℝ) := ⟨_, continuous_forwardBridgeEndpointDifference β μ s hs path x⟩
  have hfixed := (ProbabilityMeasure.continuous_integral_continuousMap H).tendsto μ |>.comp hν
  have herr := tendsto_parisiPotentialMeasureError_of_weak β μ ν hν
  have hzero : Tendsto (fun a =>
      ‖forwardBridgeExponent β (ν a) s hs path x - ∫ t, H t ∂(ν a : Measure Overlap)‖) l (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (fun a => forwardBridgeExponent_measure_error β μ (ν a) s hs path x)
      (by simpa using herr.const_mul 2)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hfixedzero := (hfixed.sub_const (forwardBridgeExponent β μ s hs path x)).norm
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun a => norm_sub_le_norm_sub_add_norm_sub _ _ _) (by simpa [H, forwardBridgeExponent] using hzero.add hfixedzero)

/-- Weak continuity includes measures with an atom at the observation time;
the CDFs themselves need not converge there. -/
theorem tendsto_forwardBridgeDensity_of_weak {A : Type*} {l : Filter A}
    [l.IsCountablyGenerated] (β : ℝ) (μ : ParisiMeasure) (ν : A → ParisiMeasure)
    (hν : Tendsto ν l (𝓝 μ)) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    Tendsto (fun a => forwardBridgeDensity β (ν a) s hs x) l
      (𝓝 (forwardBridgeDensity β μ s hs x)) := by
  simp_rw [forwardBridgeDensity_eq_exponent]
  apply Tendsto.const_mul
  apply tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ => Real.exp (β ^ 2 + |x|))
  · exact Filter.Eventually.of_forall fun a =>
      (Real.continuous_exp.comp (continuous_forwardBridgeExponent β (ν a) s hs x)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun a => Filter.Eventually.of_forall fun path => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (forwardBridgeExponent_upper_bound β (ν a) s hs path x)
  · exact integrable_const _
  · exact Filter.Eventually.of_forall fun path =>
      Real.continuous_exp.continuousAt.tendsto.comp
        (tendsto_forwardBridgeExponent_of_weak β μ ν hν s hs path x)

end FRSB
