module

public import FRSB.ForwardBridgeContinuity

@[expose] public section


/-! Every endpoint-vanishing spatial jet of the bridge exponent is weakly
continuous in the actual probability measure, even at its atoms. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper Filter
open scoped ContDiff Topology BoundedContinuousFunction
namespace FRSB

def parisiSpatialMeasureError (β : ℝ) (μ ν : ParisiMeasure) : ℕ → ℝ
  | 0 => parisiPotentialMeasureError β μ ν
  | n + 1 => ‖bcfSpatialDerivative (parisiGradientBCF β μ) n -
      bcfSpatialDerivative (parisiGradientBCF β ν) n‖

theorem parisiSpatialField_measure_error_bound (β : ℝ) (μ ν : ParisiMeasure)
    (j : ℕ) (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖parisiSpatialField β μ j (t, x) - parisiSpatialField β ν j (t, x)‖ ≤
      parisiSpatialMeasureError β μ ν j := by
  cases j with
  | zero => exact parisiPotential_measure_error_bound β μ ν t x ht
  | succ j => exact norm_parisiSlabExtend_sub_le (by norm_num) _ _ (t, x)

theorem tendsto_parisiSpatialMeasureError_of_weak {A : Type*} {l : Filter A}
    [l.IsCountablyGenerated] (β : ℝ) (μ : ParisiMeasure) (ν : A → ParisiMeasure)
    (hν : Tendsto ν l (𝓝 μ)) (j : ℕ) :
    Tendsto (fun a => parisiSpatialMeasureError β (ν a) μ j) l (𝓝 0) := by
  cases j with
  | zero => exact tendsto_parisiPotentialMeasureError_of_weak β μ ν hν
  | succ j =>
    have h := ((continuous_spatialDerivativeBCF β j).tendsto μ).comp hν
    simpa only [parisiSpatialMeasureError, sub_self, norm_zero, Function.comp_def] using
      (h.sub_const (bcfSpatialDerivative (parisiGradientBCF β μ) j)).norm

def forwardBridgeEndpointJet (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (path : ForwardBridgePath) (x : ℝ) (t : Overlap) : ℝ :=
  if (t : ℝ) ≤ s then parisiSpatialField β μ j (s, x) -
    forwardBridgeFraction s t ^ j *
      parisiSpatialField β μ j (t, forwardBridgePoint β s hs path x t) else 0

theorem continuous_forwardBridgeEndpointJet (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (path : ForwardBridgePath) (x : ℝ) :
    Continuous (forwardBridgeEndpointJet β μ s hs j path x) := by
  apply Continuous.if_le
  · exact continuous_const.sub (((show Continuous (fun t : Overlap =>
      forwardBridgeFraction s t) by unfold forwardBridgeFraction; fun_prop).pow j).mul
      ((continuous_parisiSpatialField β μ j).comp
        (continuous_subtype_val.prodMk ((continuous_forwardBridgePoint β s hs).comp
          (show Continuous (fun t : Overlap => ((path, x), t)) by fun_prop)))))
  · exact continuous_const
  · exact continuous_subtype_val
  · exact continuous_const
  · intro t ht
    have he : t = (⟨s, hs.1.le, hs.2⟩ : Overlap) := Subtype.ext ht
    rw [he, forwardBridgePoint_at_endpoint]
    simp [forwardBridgeFraction, hs.1.ne']

def forwardBridgeExponentJet (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (path : ForwardBridgePath) (x : ℝ) : ℝ :=
  ∫ t, forwardBridgeEndpointJet β μ s hs j path x t ∂(μ : Measure Overlap)

lemma integrable_forwardBridgeEndpointJet (β : ℝ) (μ ν : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (path : ForwardBridgePath) (x : ℝ) :
    Integrable (forwardBridgeEndpointJet β μ s hs j path x) (ν : Measure Overlap) :=
  (continuous_forwardBridgeEndpointJet β μ s hs j path x).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem forwardBridgeExponentJet_eq (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (path : ForwardBridgePath) (x : ℝ) :
    forwardBridgeExponentJet β μ s hs j path x =
      parisiCDF μ s * parisiSpatialField β μ j (s, x) - forwardBridgeJet β μ s hs j path x := by
  let S : Set Overlap := {t | (t : ℝ) ≤ s}
  have hS : MeasurableSet S := measurableSet_le (by fun_prop) measurable_const
  have hi0 := (integrable_const (parisiSpatialField β μ j (s, x)) :
      Integrable (fun _ : Overlap => parisiSpatialField β μ j (s, x)) (μ : Measure Overlap)).indicator hS
  have hi1 := integrable_forwardBridgeJet_integrand β μ s hs j path x
  have he : forwardBridgeEndpointJet β μ s hs j path x =
      S.indicator (fun _ => parisiSpatialField β μ j (s, x)) -
        (fun t : Overlap => if (t : ℝ) ≤ s then forwardBridgeFraction s t ^ j *
          parisiSpatialField β μ j (t, forwardBridgePoint β s hs path x t) else 0) := by
    funext t
    simp only [forwardBridgeEndpointJet, S, Set.indicator_apply, mem_setOf_eq, Pi.sub_apply]
    split_ifs <;> simp
  unfold forwardBridgeExponentJet
  rw [he]
  simp only [Pi.sub_apply]
  rw [integral_sub hi0 hi1, integral_indicator_const _ hS]
  rfl

lemma forwardBridgeExponentJet_zero (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) :
    forwardBridgeExponentJet β μ s hs 0 path x = forwardBridgeExponent β μ s hs path x := by
  rw [forwardBridgeExponentJet_eq, forwardBridgeExponent_eq]
  rfl

theorem hasDerivAt_forwardBridgeExponentJet (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (path : ForwardBridgePath) (x : ℝ) :
    HasDerivAt (forwardBridgeExponentJet β μ s hs j path)
      (forwardBridgeExponentJet β μ s hs (j + 1) path x) x := by
  have hd := ((hasDerivAt_parisiSpatialField β μ j s x ⟨hs.1.le, hs.2⟩).const_mul
    (parisiCDF μ s)).sub (hasDerivAt_forwardBridgeJet β μ s hs j path x)
  have he : forwardBridgeExponentJet β μ s hs j path =
      fun y => parisiCDF μ s * parisiSpatialField β μ j (s, y) - forwardBridgeJet β μ s hs j path y :=
    funext (forwardBridgeExponentJet_eq β μ s hs j path)
  rw [he, forwardBridgeExponentJet_eq]
  exact hd

theorem iteratedDeriv_forwardBridgeExponent (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (path : ForwardBridgePath) (x : ℝ) :
    iteratedDeriv j (forwardBridgeExponent β μ s hs path) x =
      forwardBridgeExponentJet β μ s hs j path x := by
  induction j generalizing x with
  | zero => exact (forwardBridgeExponentJet_zero β μ s hs path x).symm
  | succ j ih =>
    have he : iteratedDeriv j (forwardBridgeExponent β μ s hs path) =
        forwardBridgeExponentJet β μ s hs j path := funext ih
    rw [iteratedDeriv_succ, he]
    exact (hasDerivAt_forwardBridgeExponentJet β μ s hs j path x).deriv

theorem contDiff_forwardBridgeExponent (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) :
    ContDiff ℝ ∞ (forwardBridgeExponent β μ s hs path) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro j hj
  have he : iteratedDeriv j (forwardBridgeExponent β μ s hs path) =
      forwardBridgeExponentJet β μ s hs j path :=
    funext (iteratedDeriv_forwardBridgeExponent β μ s hs j path)
  rw [he]
  exact fun x => (hasDerivAt_forwardBridgeExponentJet β μ s hs j path x).differentiableAt

theorem norm_forwardBridgeExponentJet_succ_le (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (path : ForwardBridgePath) (x : ℝ) :
    ‖forwardBridgeExponentJet β μ s hs (j + 1) path x‖ ≤ 2 * uniformSpatialConstant β j := by
  rw [forwardBridgeExponentJet_eq]
  have hα : ‖parisiCDF μ s‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (parisiCDF_nonneg μ s)]
    exact parisiCDF_le_one μ s
  have hp := parisiSpatialField_uniform_bound β j μ (s, x)
  have hg := norm_forwardBridgeJet_succ_le β μ s hs j path x
  have hh := norm_sub_le (parisiCDF μ s * parisiSpatialField β μ (j + 1) (s, x))
    (forwardBridgeJet β μ s hs (j + 1) path x)
  rw [norm_mul] at hh
  have hm := mul_le_mul hα hp (norm_nonneg _) zero_le_one
  simp only [one_mul] at hm
  linarith

theorem forwardBridgeEndpointJet_measure_error (β : ℝ) (μ ν : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (path : ForwardBridgePath) (x : ℝ) (t : Overlap) :
    ‖forwardBridgeEndpointJet β ν s hs j path x t - forwardBridgeEndpointJet β μ s hs j path x t‖ ≤
      2 * parisiSpatialMeasureError β ν μ j := by
  have h1 := parisiSpatialField_measure_error_bound β ν μ j s x ⟨hs.1.le, hs.2⟩
  have h2 := parisiSpatialField_measure_error_bound β ν μ j t (forwardBridgePoint β s hs path x t) t.property
  have hE : 0 ≤ parisiSpatialMeasureError β ν μ j := (norm_nonneg _).trans h1
  unfold forwardBridgeEndpointJet
  split_ifs
  · let θ := forwardBridgeFraction s t ^ j
    have hθ : ‖θ‖ ≤ 1 := by
      rw [norm_pow, Real.norm_of_nonneg (forwardBridgeFraction_mem s hs.1 t).1]
      exact pow_le_one₀ (forwardBridgeFraction_mem s hs.1 t).1 (forwardBridgeFraction_mem s hs.1 t).2
    have he : parisiSpatialField β ν j (s, x) - θ * parisiSpatialField β ν j (t, forwardBridgePoint β s hs path x t) -
        (parisiSpatialField β μ j (s, x) - θ * parisiSpatialField β μ j (t, forwardBridgePoint β s hs path x t)) =
        (parisiSpatialField β ν j (s, x) - parisiSpatialField β μ j (s, x)) -
        θ * (parisiSpatialField β ν j (t, forwardBridgePoint β s hs path x t) -
          parisiSpatialField β μ j (t, forwardBridgePoint β s hs path x t)) := by ring
    rw [he]
    have hh := norm_sub_le (parisiSpatialField β ν j (s, x) - parisiSpatialField β μ j (s, x))
      (θ * (parisiSpatialField β ν j (t, forwardBridgePoint β s hs path x t) -
        parisiSpatialField β μ j (t, forwardBridgePoint β s hs path x t)))
    rw [norm_mul] at hh
    have hm := mul_le_mul hθ h2 (norm_nonneg _) zero_le_one
    simp only [one_mul] at hm
    linarith
  · simp only [sub_self, norm_zero]
    positivity

theorem tendsto_forwardBridgeExponentJet_of_weak {A : Type*} {l : Filter A}
    [l.IsCountablyGenerated] (β : ℝ) (μ : ParisiMeasure) (ν : A → ParisiMeasure)
    (hν : Tendsto ν l (𝓝 μ)) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (j : ℕ) (path : ForwardBridgePath) (x : ℝ) :
    Tendsto (fun a => forwardBridgeExponentJet β (ν a) s hs j path x) l
      (𝓝 (forwardBridgeExponentJet β μ s hs j path x)) := by
  let H : C(Overlap, ℝ) := ⟨_, continuous_forwardBridgeEndpointJet β μ s hs j path x⟩
  have hfixed := (ProbabilityMeasure.continuous_integral_continuousMap H).tendsto μ |>.comp hν
  have herr := tendsto_parisiSpatialMeasureError_of_weak β μ ν hν j
  have hzero : Tendsto (fun a => ‖forwardBridgeExponentJet β (ν a) s hs j path x -
      ∫ t, H t ∂(ν a : Measure Overlap)‖) l (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _) _ (by simpa using herr.const_mul 2)
    intro a
    have hi1 := integrable_forwardBridgeEndpointJet β (ν a) (ν a) s hs j path x
    have hi2 := integrable_forwardBridgeEndpointJet β μ (ν a) s hs j path x
    unfold forwardBridgeExponentJet
    dsimp only [H, ContinuousMap.coe_mk]
    rw [← integral_sub hi1 hi2]
    exact (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall
      (forwardBridgeEndpointJet_measure_error β μ (ν a) s hs j path x))).trans_eq (by simp)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hfixedzero := (hfixed.sub_const (forwardBridgeExponentJet β μ s hs j path x)).norm
  exact squeeze_zero (fun _ => norm_nonneg _) (fun a => norm_sub_le_norm_sub_add_norm_sub _ _ _)
    (by simpa [H, forwardBridgeExponentJet] using hzero.add hfixedzero)

end FRSB
