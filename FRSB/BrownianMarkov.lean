module

public import FRSB.FiniteJointLaw
public import Paper.DiracShift
public import Paper.StateDiffusion

@[expose] public section


/-! The actual Gaussian transition law of scaled canonical Brownian motion,
including an arbitrary measurable record of its past. No Markov law is
supplied as a hypothesis: it follows from Brownian independent increments. -/
noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace FRSB

/-- Translating an independent centered Gaussian increment gives the genuine
Gaussian state kernel joint law. -/
theorem joint_gaussianStateKernel_of_indep {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → A) (U : Ω → ℝ) (hY : Measurable Y) (hU : Measurable U)
    (hI : IndepFun Y U P) (v : ℝ≥0) (hUlaw : HasLaw U (gaussianReal 0 v) P)
    (ρ : A → ℝ) (hρ : Measurable ρ) :
    P.map (fun ω => (Y ω, ρ (Y ω) + U ω)) =
      (P.map Y) ⊗ₘ ((Paper.gaussianStateKernel v).comap ρ hρ) := by
  let F : A × ℝ → A × ℝ := fun p => (p.1, ρ p.1 + p.2)
  have hF : Measurable F := measurable_fst.prodMk
    ((hρ.comp measurable_fst).add measurable_snd)
  have hprod := hI.map_prod_eq_prod_map_map hY.aemeasurable hU.aemeasurable
  have hmap : P.map (fun ω => (Y ω, ρ (Y ω) + U ω)) =
      ((P.map Y).prod (gaussianReal 0 v)).map F := by
    rw [← hUlaw.map_eq, ← hprod, Measure.map_map hF (hY.prodMk hU)]
    rfl
  rw [hmap]
  ext s hs
  rw [Measure.map_apply hF hs, Measure.prod_apply (hF hs), Measure.compProd_apply hs]
  apply lintegral_congr
  intro y
  have hsection : MeasurableSet (Prod.mk y ⁻¹' s) := hs.preimage measurable_prodMk_left
  have hg : Measurable (fun z : ℝ => ρ y + z) := measurable_const.add measurable_id
  have hgauss := congrArg (fun Q : Measure ℝ => Q (Prod.mk y ⁻¹' s))
    (gaussianReal_map_const_add (μ := 0) (v := v) (ρ y))
  rw [Measure.map_apply hg hsection, zero_add] at hgauss
  exact hgauss

/-- The actual scaled canonical Brownian increment law, valid also for equal
times and zero scale. -/
theorem hasLaw_scaledBrownian_increment (β : ℝ) (r t : ℝ≥0) (hrt : r ≤ t) :
    HasLaw (fun ω : Paper.BrownianSample =>
      β * (Paper.canonicalBrownian t ω - Paper.canonicalBrownian r ω))
      (gaussianReal 0 (β ^ 2 * ((t : ℝ) - r)).toNNReal)
      Paper.canonicalBrownianMeasure := by
  have h := gaussianReal_const_mul
    (Paper.isBrownianReal_canonicalBrownian.toIsPreBrownianReal.hasLaw_sub t r) β
  have hrtR : (r : ℝ) ≤ (t : ℝ) := by exact_mod_cast hrt
  have hv : (NNReal.mk (β ^ 2) (sq_nonneg β)) * nndist (t : ℝ) (r : ℝ) =
      (β ^ 2 * ((t : ℝ) - r)).toNNReal := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_mul, NNReal.coe_mk, coe_nndist, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr hrtR), Real.coe_toNNReal _
        (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hrtR))]
  convert h using 1
  congr 1
  · simp
  · exact hv.symm

/-- The initial scaled Brownian marginal, without a positivity restriction
on either time or scale. -/
theorem hasLaw_scaledBrownian (β : ℝ) (t : ℝ≥0) :
    HasLaw (fun ω : Paper.BrownianSample => β * Paper.canonicalBrownian t ω)
      (gaussianReal 0 (β ^ 2 * (t : ℝ)).toNNReal)
      Paper.canonicalBrownianMeasure := by
  simpa only [Paper.canonicalBrownian_zero, sub_zero, NNReal.coe_zero] using
    hasLaw_scaledBrownian_increment β 0 t (by positivity)

/-- A measurable record of the Brownian past and the next scaled Brownian
state have exactly the Gaussian transition-kernel joint law. -/
theorem scaledBrownian_joint_transitionLaw {A : Type*} [MeasurableSpace A]
    (β : ℝ) (r t : ℝ≥0) (hrt : r ≤ t)
    (Y : Paper.BrownianSample → A)
    (hY : Measurable[Paper.canonicalBrownianFiltration r] Y)
    (ρ : A → ℝ) (hρ : Measurable ρ)
    (hρY : ∀ ω, ρ (Y ω) = β * Paper.canonicalBrownian r ω) :
    Paper.canonicalBrownianMeasure.map
        (fun ω => (Y ω, β * Paper.canonicalBrownian t ω)) =
      (Paper.canonicalBrownianMeasure.map Y) ⊗ₘ
        ((Paper.gaussianStateKernel (β ^ 2 * ((t : ℝ) - r)).toNNReal).comap ρ hρ) := by
  have hYg : Measurable Y := hY.mono (Paper.canonicalBrownianFiltration.le r) le_rfl
  have hFB := Paper.isBrownianReal_canonicalBrownian.toIsPreBrownianReal.isFilteredPreBrownian
    Paper.measurable_canonicalBrownian
  have hI : IndepFun (Paper.canonicalBrownian t - Paper.canonicalBrownian r) Y
      Paper.canonicalBrownianMeasure := by
    apply (IndepFun_iff_Indep _ _ _).2
    exact indep_of_indep_of_le_right (hFB.indep r t hrt) hY.comap_le
  have hscaled : IndepFun Y (fun ω =>
      β * (Paper.canonicalBrownian t ω - Paper.canonicalBrownian r ω))
      Paper.canonicalBrownianMeasure := by
    simpa only [Function.comp_def, Pi.sub_apply, Pi.mul_apply, id_eq] using
      (hI.comp (measurable_const.mul measurable_id) measurable_id).symm
  have hU : Measurable (fun ω : Paper.BrownianSample =>
      β * (Paper.canonicalBrownian t ω - Paper.canonicalBrownian r ω)) :=
    (Paper.measurable_canonicalBrownian t).sub (Paper.measurable_canonicalBrownian r)
      |>.const_mul β
  have h := joint_gaussianStateKernel_of_indep Paper.canonicalBrownianMeasure Y _ hYg hU
    hscaled _ (hasLaw_scaledBrownian_increment β r t hrt) ρ hρ
  convert h using 1
  congr 1
  funext ω
  rw [hρY ω]
  congr 1
  ring

end FRSB
