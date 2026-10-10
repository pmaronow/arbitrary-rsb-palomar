module

public import FRSB.ConstantMassGrowth
public import FRSB.ForwardIntegralSmooth
public import FRSB.ForwardExponentialBounds
public import FRSB.ForwardLogBounds
public import FRSB.UniformSpatialRegularity
public import Paper.CanonicalBrownian

@[expose] public section


/-! An explicit Gaussian-bridge Feynman--Kac forward gauge.  The analytical
construction uses the actual arbitrary-measure Parisi potential and the
actual canonical Wiener probability measure.  Its identification as the
diffusion density is a separate law theorem. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper Filter
open scoped ContDiff Topology
namespace FRSB

abbrev ForwardBridgePath := C(Overlap, ℝ)

def forwardBridgeFraction (s : ℝ) (t : Overlap) : ℝ := min ((t : ℝ) / s) 1

lemma forwardBridgeFraction_mem (s : ℝ) (hs : 0 < s) (t : Overlap) :
    forwardBridgeFraction s t ∈ Icc (0 : ℝ) 1 :=
  ⟨le_min (div_nonneg t.property.1 hs.le) zero_le_one, min_le_right _ _⟩

def forwardBridgePoint (β s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (path : ForwardBridgePath) (x : ℝ) (t : Overlap) : ℝ :=
  forwardBridgeFraction s t * x + β *
    (path t - forwardBridgeFraction s t * path ⟨s, hs.1.le, hs.2⟩)

lemma forwardBridgePoint_at_endpoint (β s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (path : ForwardBridgePath) (x : ℝ) :
    forwardBridgePoint β s hs path x ⟨s, hs.1.le, hs.2⟩ = x := by
  simp [forwardBridgePoint, forwardBridgeFraction, hs.1.ne']

lemma continuous_forwardBridgePoint (β s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    Continuous (fun p : (ForwardBridgePath × ℝ) × Overlap =>
      forwardBridgePoint β s hs p.1.1 p.1.2 p.2) := by
  unfold forwardBridgePoint forwardBridgeFraction
  have heval : Continuous (fun p : (ForwardBridgePath × ℝ) × Overlap => p.1.1 p.2) :=
    continuous_eval.comp (continuous_fst.fst.prodMk continuous_snd)
  have hevalS : Continuous (fun p : (ForwardBridgePath × ℝ) × Overlap =>
      p.1.1 ⟨s, hs.1.le, hs.2⟩) :=
    (continuous_eval_const _).comp continuous_fst.fst
  fun_prop

lemma norm_forwardBridgePoint_le (β s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (path : ForwardBridgePath) (x : ℝ) (t : Overlap) :
    ‖forwardBridgePoint β s hs path x t‖ ≤ |x| + 2 * |β| * ‖path‖ := by
  have hθ := forwardBridgeFraction_mem s hs.1 t
  have hθn : ‖forwardBridgeFraction s t‖ ≤ 1 := by
    rw [Real.norm_of_nonneg hθ.1]
    exact hθ.2
  unfold forwardBridgePoint
  calc
    _ ≤ ‖forwardBridgeFraction s t * x‖ + ‖β * (path t - forwardBridgeFraction s t * path ⟨s, hs.1.le, hs.2⟩)‖ := norm_add_le _ _
    _ ≤ 1 * ‖x‖ + ‖β‖ * (‖path t‖ + 1 * ‖path ⟨s, hs.1.le, hs.2⟩‖) := by
      rw [norm_mul, norm_mul]
      exact add_le_add (mul_le_mul_of_nonneg_right hθn (norm_nonneg _))
        (mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add le_rfl
          (by rw [norm_mul]; exact mul_le_mul_of_nonneg_right hθn (norm_nonneg _)))) (norm_nonneg _))
    _ ≤ _ := by
      have h1 := path.norm_coe_le_norm t
      have h2 := path.norm_coe_le_norm ⟨s, hs.1.le, hs.2⟩
      rw [Real.norm_eq_abs x, Real.norm_eq_abs β]
      nlinarith [abs_nonneg β]

def forwardBridgeJet (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (path : ForwardBridgePath) (x : ℝ) : ℝ :=
  ∫ t : Overlap, if (t : ℝ) ≤ s then
    forwardBridgeFraction s t ^ j * parisiSpatialField β μ j
      (t, forwardBridgePoint β s hs path x t) else 0 ∂(μ : Measure Overlap)

def forwardBridgeAction (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) : ℝ :=
  forwardBridgeJet β μ s hs 0 path x

lemma measurable_forwardBridgeJet_integrand (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (path : ForwardBridgePath) (x : ℝ) :
    Measurable (fun t : Overlap => if (t : ℝ) ≤ s then
      forwardBridgeFraction s t ^ j * parisiSpatialField β μ j
        (t, forwardBridgePoint β s hs path x t) else 0) := by
  have hc : Continuous (fun t : Overlap => forwardBridgePoint β s hs path x t) :=
    (continuous_forwardBridgePoint β s hs).comp (show Continuous
      (fun t : Overlap => ((path, x), t)) by fun_prop)
  apply Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
  · exact ((show Continuous (fun t : Overlap => forwardBridgeFraction s t) by
      unfold forwardBridgeFraction; fun_prop).pow j |>.mul
        ((continuous_parisiSpatialField β μ j).comp (continuous_subtype_val.prodMk hc))).measurable
  · exact measurable_const

lemma norm_forwardBridgeJet_integrand_succ_le (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (path : ForwardBridgePath) (x : ℝ) (t : Overlap) :
    ‖if (t : ℝ) ≤ s then forwardBridgeFraction s t ^ (j + 1) *
      parisiSpatialField β μ (j + 1) (t, forwardBridgePoint β s hs path x t) else 0‖ ≤
        uniformSpatialConstant β j := by
  split_ifs
  · rw [norm_mul, norm_pow, Real.norm_of_nonneg (forwardBridgeFraction_mem s hs.1 t).1]
    exact (mul_le_mul (pow_le_one₀ (forwardBridgeFraction_mem s hs.1 t).1
      (forwardBridgeFraction_mem s hs.1 t).2) (parisiSpatialField_uniform_bound β j μ _)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  · simpa using (uniformSpatialConstant_pos β j).le

lemma norm_forwardBridgeJet_integrand_zero_le (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) (t : Overlap) :
    ‖if (t : ℝ) ≤ s then forwardBridgeFraction s t ^ (0 : ℕ) *
      parisiSpatialField β μ 0 (t, forwardBridgePoint β s hs path x t) else 0‖ ≤
        β ^ 2 + |x| + 2 * |β| * ‖path‖ := by
  split_ifs
  · simp only [pow_zero, one_mul, parisiSpatialField, Real.norm_eq_abs]
    have hp := norm_forwardBridgePoint_le β s hs path x t
    rw [Real.norm_eq_abs] at hp
    have hu := parisiPotential_absolute_growth β μ t (forwardBridgePoint β s hs path x t) t.property
    linarith
  · simp only [norm_zero]
    positivity

lemma integrable_forwardBridgeJet_integrand (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (path : ForwardBridgePath) (x : ℝ) :
    Integrable (fun t : Overlap => if (t : ℝ) ≤ s then
      forwardBridgeFraction s t ^ j * parisiSpatialField β μ j
        (t, forwardBridgePoint β s hs path x t) else 0) (μ : Measure Overlap) := by
  cases j with
  | zero =>
    exact (integrable_const (β ^ 2 + |x| + 2 * |β| * ‖path‖)).mono'
      (measurable_forwardBridgeJet_integrand β μ s hs 0 path x).aestronglyMeasurable
      (Filter.Eventually.of_forall (norm_forwardBridgeJet_integrand_zero_le β μ s hs path x))
  | succ j =>
    exact (integrable_const (uniformSpatialConstant β j)).mono'
      (measurable_forwardBridgeJet_integrand β μ s hs (j + 1) path x).aestronglyMeasurable
      (Filter.Eventually.of_forall (norm_forwardBridgeJet_integrand_succ_le β μ s hs j path x))

theorem forwardBridgeAction_nonneg (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) :
    0 ≤ forwardBridgeAction β μ s hs path x := by
  apply integral_nonneg
  intro t
  change 0 ≤ if (t : ℝ) ≤ s then forwardBridgeFraction s t ^ 0 *
    parisiSpatialField β μ 0 (t, forwardBridgePoint β s hs path x t) else 0
  split_ifs
  · simpa only [pow_zero, one_mul, parisiSpatialField] using
      parisiPotential_nonneg β μ t (forwardBridgePoint β s hs path x t) t.property.2
  · exact le_rfl

theorem norm_forwardBridgeJet_succ_le (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (path : ForwardBridgePath) (x : ℝ) :
    ‖forwardBridgeJet β μ s hs (j + 1) path x‖ ≤ uniformSpatialConstant β j := by
  exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall
    (norm_forwardBridgeJet_integrand_succ_le β μ s hs j path x)) |>.trans_eq (by simp)

theorem continuous_forwardBridgeJet (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) :
    Continuous (fun p : ForwardBridgePath × ℝ => forwardBridgeJet β μ s hs j p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p₀
  let C := if j = 0 then β ^ 2 + (|p₀.2| + 1) + 2 * |β| * (‖p₀.1‖ + 1)
    else uniformSpatialConstant β (j - 1)
  apply continuousAt_of_dominated (μ := (μ : Measure Overlap))
    (F := fun (p : ForwardBridgePath × ℝ) (t : Overlap) => if (t : ℝ) ≤ s then
      forwardBridgeFraction s t ^ j * parisiSpatialField β μ j
        (t, forwardBridgePoint β s hs p.1 p.2 t) else 0)
    (bound := fun _ => C)
  · exact Filter.Eventually.of_forall fun p =>
      (measurable_forwardBridgeJet_integrand β μ s hs j p.1 p.2).aestronglyMeasurable
  · have hp := ((continuous_norm.comp continuous_fst).tendsto p₀).eventually
      (Iio_mem_nhds (lt_add_one ‖p₀.1‖))
    have hx := ((continuous_abs.comp continuous_snd).tendsto p₀).eventually
      (Iio_mem_nhds (lt_add_one |p₀.2|))
    filter_upwards [hp, hx] with p hp hx
    simp only [Function.comp_def] at hp hx
    exact Filter.Eventually.of_forall fun t => by
      cases j with
      | zero =>
        have hb := norm_forwardBridgeJet_integrand_zero_le β μ s hs p.1 p.2 t
        dsimp [C]
        exact hb.trans (by nlinarith [abs_nonneg β])
      | succ j =>
        simpa only [C, Nat.succ_ne_zero, ite_false, Nat.add_one_sub_one] using
          norm_forwardBridgeJet_integrand_succ_le β μ s hs j p.1 p.2 t
  · exact integrable_const C
  · exact Filter.Eventually.of_forall fun t => by
      by_cases ht : (t : ℝ) ≤ s
      · have hc : Continuous (fun p : ForwardBridgePath × ℝ =>
          forwardBridgeFraction s t ^ j * parisiSpatialField β μ j
            (t, forwardBridgePoint β s hs p.1 p.2 t)) :=
          continuous_const.mul ((continuous_parisiSpatialField β μ j).comp
            (continuous_const.prodMk ((continuous_forwardBridgePoint β s hs).comp
              (continuous_id.prodMk continuous_const))))
        simpa only [ht, ite_true] using hc.continuousAt
      · simpa only [ht, ite_false] using (continuous_const :
          Continuous (fun _ : ForwardBridgePath × ℝ => (0 : ℝ))).continuousAt

theorem hasDerivAt_forwardBridgeJet (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (path : ForwardBridgePath) (x : ℝ) :
    HasDerivAt (forwardBridgeJet β μ s hs j path)
      (forwardBridgeJet β μ s hs (j + 1) path x) x := by
  apply hasDerivAt_integral_uniform (μ : Measure Overlap)
    (fun y t => if (t : ℝ) ≤ s then forwardBridgeFraction s t ^ j *
      parisiSpatialField β μ j (t, forwardBridgePoint β s hs path y t) else 0)
    (fun y t => if (t : ℝ) ≤ s then forwardBridgeFraction s t ^ (j + 1) *
      parisiSpatialField β μ (j + 1) (t, forwardBridgePoint β s hs path y t) else 0)
    x (uniformSpatialConstant β j)
  · intro y
    exact (measurable_forwardBridgeJet_integrand β μ s hs j path y).aestronglyMeasurable
  · exact integrable_forwardBridgeJet_integrand β μ s hs j path x
  · exact (measurable_forwardBridgeJet_integrand β μ s hs (j + 1) path x).aestronglyMeasurable
  · exact norm_forwardBridgeJet_integrand_succ_le β μ s hs j path
  · intro y t
    by_cases ht : (t : ℝ) ≤ s
    · simp only [ht, ite_true]
      have hd := ((hasDerivAt_parisiSpatialField β μ j t
        (forwardBridgePoint β s hs path y t) t.property).comp y
        (((hasDerivAt_id y).const_mul (forwardBridgeFraction s t)).add_const
          (β * (path t - forwardBridgeFraction s t * path ⟨s, hs.1.le, hs.2⟩)))).const_mul
            (forwardBridgeFraction s t ^ j)
      convert hd using 1
      · rfl
      · rw [pow_succ]
        ring
    · simp only [ht, ite_false]
      exact hasDerivAt_const y 0

theorem iteratedDeriv_forwardBridgeAction (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (path : ForwardBridgePath) (x : ℝ) :
    iteratedDeriv j (forwardBridgeAction β μ s hs path) x =
      forwardBridgeJet β μ s hs j path x := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    have he : iteratedDeriv j (forwardBridgeAction β μ s hs path) =
        forwardBridgeJet β μ s hs j path := funext ih
    rw [iteratedDeriv_succ, he]
    exact (hasDerivAt_forwardBridgeJet β μ s hs j path x).deriv

theorem contDiff_forwardBridgeAction (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) :
    ContDiff ℝ ∞ (forwardBridgeAction β μ s hs path) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro j hj
  have he : iteratedDeriv j (forwardBridgeAction β μ s hs path) =
      forwardBridgeJet β μ s hs j path :=
    funext (iteratedDeriv_forwardBridgeAction β μ s hs j path)
  rw [he]
  exact fun x => (hasDerivAt_forwardBridgeJet β μ s hs j path x).differentiableAt

end FRSB
