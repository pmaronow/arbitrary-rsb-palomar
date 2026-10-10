module

public import DepthPaper.OriginalClockTimeEquation

@[expose] public section


/-! The recalled Parisi PDE, with its literal terminal condition, in the
original overlap coordinate. Every smooth compact test in the physical open
strip is admitted; no atom-free or classical-time assumption is imposed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff NNReal
namespace DepthPaper
set_option maxHeartbeats 1000000

theorem integrable_originalClockTimeField_mul_test (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) (φ : ℝ × ℝ → ℝ) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) :
    Integrable (fun p => originalClockTimeField Ξ μ p * φ p) Paper.parisiSpaceTime := by
  let F : ℝ × ℝ → ℝ := fun p => originalClockTimeField Ξ μ
    ((projIcc (0:ℝ) 1 zero_le_one p.1 : ℝ),p.2)
  obtain ⟨M,hM,hb⟩ := originalClockTimeField_bounded_strip Ξ μ
  have hFm : Measurable F := (measurable_originalClockTimeField Ξ μ).comp
    (((continuous_subtype_val.comp ((continuous_projIcc (a := (0:ℝ))
      (b := 1) (h := zero_le_one)).comp continuous_fst)).prodMk continuous_snd).measurable)
  have hFb (p : ℝ × ℝ) : ‖F p‖ ≤ M := hb _ (projIcc _ _ _ _).property _
  have hi := Paper.integrable_boundedField_mul_compactTest F φ hFm M hFb hφ hc
  have ha : ∀ᵐ p : ℝ × ℝ ∂Paper.parisiSpaceTime, p.1 ∈ Icc (0:ℝ) 1 := by
    unfold Paper.parisiSpaceTime
    apply (Measure.ae_prod_mem_iff_ae_ae_mem (measurable_fst measurableSet_Icc)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with q hq
    exact .of_forall fun _ => hq
  apply hi.congr
  filter_upwards [ha] with p hp
  dsimp only [F]
  rw [projIcc_of_mem _ hp]

theorem integral_potential_originalClock_byParts (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hs : tsupport φ ⊆ {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < 1}) (x : ℝ) :
    (∫ q in (0:ℝ)..1, potential Ξ μ q x * Paper.parisiTestT φ (q,x) +
      originalClockTimeField Ξ μ (q,x) * φ (q,x)) = 0 := by
  have hF := absolutelyContinuous_potential_originalClock Ξ μ x
  have hG : AbsolutelyContinuousOnInterval (fun q => φ (q,x)) 0 1 :=
    ((hφ.comp (contDiff_id.prodMk contDiff_const)).of_le
      (by simp : (1 : WithTop ℕ∞) ≤ ∞)).contDiffOn.absolutelyContinuousOnInterval
  have hz (q : ℝ) (hq : q = 0 ∨ q = 1) : φ (q,x) = 0 := by
    by_contra hn
    have hh := hs (subset_closure (show (q,x) ∈ Function.support φ from hn))
    rcases hq with rfl | rfl <;> norm_num at hh
  have hh := hF.integral_deriv_mul_eq_sub hG
  rw [hz 0 (Or.inl rfl),hz 1 (Or.inr rfl),mul_zero,mul_zero,sub_self] at hh
  calc
    _ = ∫ q in (0:ℝ)..1, deriv (fun s => potential Ξ μ s x) q * φ (q,x) +
        potential Ξ μ q x * deriv (fun s => φ (s,x)) q := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [ae_hasDerivAt_potential_originalClock Ξ μ x,
        (countable_singleton (1:ℝ)).ae_notMem volume] with q hq hn hqu
      have hu : q ∈ Ioo (0:ℝ) 1 := by
        have hqu' : q ∈ Ioc (0:ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using hqu
        exact ⟨hqu'.1,lt_of_le_of_ne hqu'.2 (by simpa only [mem_singleton_iff] using hn)⟩
      rw [(hq hu).deriv,(Paper.hasDerivAt_parisiTestT φ hφ q x).deriv]
      ring
    _ = 0 := hh

/-- The original-clock equation is distributional in time. Its source is
the actual Hessian and squared actual gradient, with the actual right CDF. -/
theorem originalClock_weak_PDE (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) :
    Paper.IsParisiWeakTimeDerivative (fun p => potential Ξ μ p.1 p.2)
      (originalClockTimeField Ξ μ) := by
  intro φ hφ hc hs
  have hu : Integrable (fun p => potential Ξ μ p.1 p.2 * Paper.parisiTestT φ p)
      Paper.parisiSpaceTime :=
    ((continuous_potential_originalClock Ξ μ).mul (Paper.continuous_parisiTestT φ hφ)).integrable_of_hasCompactSupport
      (Paper.hasCompactSupport_parisiTestT φ hφ hc).mul_left
  have hw := integrable_originalClockTimeField_mul_test Ξ μ φ hφ.continuous hc
  refine ⟨hu.add hw,?_⟩
  have hij : Integrable (fun p : ℝ × ℝ => potential Ξ μ p.1 p.2 * Paper.parisiTestT φ p +
      originalClockTimeField Ξ μ p * φ p) Paper.parisiSpaceTime := hu.add hw
  unfold Paper.parisiSpaceTime at hij ⊢
  change (∫ p : ℝ × ℝ, potential Ξ μ p.1 p.2 * Paper.parisiTestT φ p +
    originalClockTimeField Ξ μ p * φ p ∂(volume.restrict (Icc (0:ℝ) 1)).prod volume) = 0
  rw [integral_prod _ hij,integral_integral_swap hij]
  apply integral_eq_zero_of_ae
  filter_upwards with x
  rw [←restrict_Ioc_eq_restrict_Icc,←intervalIntegral.integral_of_le zero_le_one]
  exact integral_potential_originalClock_byParts Ξ μ φ hφ hs x

theorem originalClock_PDE_and_terminal (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) :
    Paper.IsParisiWeakTimeDerivative (fun p => potential Ξ μ p.1 p.2)
      (fun p => -(Ξ.second p.1/2) * (hessian Ξ μ p.1 p.2 +
        Paper.parisiCDF μ p.1 * gradient Ξ μ p.1 p.2 ^ 2)) ∧
    ∀ x, potential Ξ μ 1 x = Real.log (Real.cosh x) := by
  exact ⟨originalClock_weak_PDE Ξ μ,FourPapersCommon.mixedPotential_terminal Ξ.toEvenMixture μ⟩

end DepthPaper
