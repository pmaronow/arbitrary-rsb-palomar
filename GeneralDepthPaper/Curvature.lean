module

public import GeneralDepthPaper.Model

set_option backward.privateInPublic true

@[expose] public section


/-! Lemma 2.2, for the actual mixed Parisi solution and every Parisi measure.
The origin estimate retains the quadratic contribution and uses ξ″(0)<1. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 400000

def GammaPrime (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) (q : ℝ) : ℝ :=
  Ξ.second q*curvatureMoment Ξ μ q

theorem GammaPrime_nonneg (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    {q : ℝ} (hq : q∈Icc (0:ℝ) 1) : 0≤GammaPrime Ξ μ q :=
  mul_nonneg (Ξ.second_nonneg hq.1) (curvatureMoment_nonneg Ξ μ q)

theorem GammaPrime_le (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    GammaPrime Ξ μ q≤Ξ.second q*(1-Gamma Ξ μ q) :=
  mul_le_mul_of_nonneg_left (curvatureMoment_le_one_sub_Gamma Ξ μ hq)
    (Ξ.second_nonneg hq.1)

theorem derivWithin_Gamma (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    derivWithin (Gamma Ξ μ) (Icc (0:ℝ) 1) q=GammaPrime Ξ μ q :=
  (hasDerivWithinAt_Gamma Ξ μ hq).derivWithin (uniqueDiffOn_Icc (by norm_num) q hq)

theorem Gamma_le_first (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    {q : ℝ} (hq : q∈Icc (0:ℝ) 1) : Gamma Ξ μ q≤Ξ.first q := by
  have hm : MonotoneOn (fun s=>Ξ.first s-Gamma Ξ μ s) (Icc (0:ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (Ξ.continuous_first.continuousOn.sub (continuousOn_Gamma Ξ μ))
        (f':=fun s=>Ξ.second s-Ξ.second s*curvatureMoment Ξ μ s)
    · intro s hs
      rw [interior_Icc] at hs
      exact ((Ξ.hasDerivAt_first s).sub (hasDerivAt_Gamma Ξ μ hs)).hasDerivWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hn := Ξ.second_nonneg hs.1.le
      have hc := curvatureMoment_le_one Ξ μ s
      nlinarith
  have hh := hm (by norm_num : (0:ℝ)∈Icc (0:ℝ) 1) hq hq.1
  simpa only [Ξ.first_zero,Gamma_zero,sub_self,sub_nonneg] using hh

theorem norm_gradient_le_one (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (q x : ℝ) : ‖gradient Ξ μ q x‖≤1 :=
  FourPapersCommon.norm_mixedGradient_le_one Ξ.toEvenMixture μ (q,x)

theorem hessian_pos (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    {q : ℝ} (hq : q∈Icc (0:ℝ) 1) (x : ℝ) : 0<hessian Ξ μ q x :=
  FourPapersCommon.mixedHessian_pos Ξ.toEvenMixture μ q x hq

theorem hessian_le_one_sub_gradient_sq (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (q x : ℝ) : hessian Ξ μ q x≤1-gradient Ξ μ q x^2 := by
  have h := FourPapersCommon.mixedHessian_add_gradient_sq_le_one Ξ.toEvenMixture μ (q,x)
  change hessian Ξ μ q x+gradient Ξ μ q x^2≤1 at h
  linarith

private theorem firstVariation_source_continuousOn (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) :
    ContinuousOn (fun s=>Ξ.second s*(Gamma Ξ μ s-s)) (Icc (0:ℝ) 1) :=
  Ξ.continuous_second.continuousOn.mul ((continuousOn_Gamma Ξ μ).sub continuousOn_id)

theorem continuousOn_firstVariation (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) :
    ContinuousOn (firstVariation Ξ μ) (Icc (0:ℝ) 1) := by
  have hi : IntegrableOn (fun s=>Ξ.second s*(Gamma Ξ μ s-s)) (uIcc (0:ℝ) 1) := by
    rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)]
    exact (firstVariation_source_continuousOn Ξ μ).integrableOn_compact isCompact_Icc
  have hc := intervalIntegral.continuousOn_primitive_interval hi
  rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)] at hc
  have he : firstVariation Ξ μ=(fun q=>(1/2:ℝ)*∫s in 0..q,Ξ.second s*(Gamma Ξ μ s-s)) :=
    funext (firstVariation_eq Ξ μ)
  rw [he]
  exact hc.const_mul (1/2:ℝ)

theorem hasDerivAt_firstVariation (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    {q : ℝ} (hq : q∈Ioo (0:ℝ) 1) :
    HasDerivAt (firstVariation Ξ μ) ((1/2:ℝ)*Ξ.second q*(Gamma Ξ μ q-q)) q := by
  have hc := firstVariation_source_continuousOn Ξ μ
  have hi : IntervalIntegrable (fun s=>Ξ.second s*(Gamma Ξ μ s-s)) volume 0 q :=
    (hc.mono (Icc_subset_Icc_right hq.2.le)).intervalIntegrable_of_Icc hq.1.le
  have hca := hc.continuousAt (Icc_mem_nhds hq.1 hq.2)
  have hd := (intervalIntegral.integral_hasDerivAt_right hi
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
      (hc.mono Ioo_subset_Icc_self) q hq) hca).const_mul (1/2:ℝ)
  have he : firstVariation Ξ μ=(fun q=>(1/2:ℝ)*∫s in 0..q,Ξ.second s*(Gamma Ξ μ s-s)) :=
    funext (firstVariation_eq Ξ μ)
  rw [he]
  simpa only [mul_assoc] using hd

theorem first_eq_quadratic_add_higher (Ξ : AdmissibleCovariance) (q : ℝ) :
    Ξ.first q = Ξ.second 0*q +
      ∑p ∈ Ξ.degrees.erase 2, Ξ.coefficient p*(p:ℝ)*q^(p-1) := by
  have hs : Ξ.second 0 = if 2 ∈ Ξ.degrees then 2*Ξ.coefficient 2 else 0 := by
    unfold AdmissibleCovariance.second
    by_cases h2 : 2 ∈ Ξ.degrees
    · rw [Finset.sum_eq_single 2]
      · simp only [ite_eq_left h2]
        norm_num
        ring
      · intro p hp hpn
        have hn : p-2 ≠ 0 := by have := Ξ.degree_ge_two p hp; omega
        simp [hn]
      · exact fun h => (h h2).elim
    · rw [ite_eq_right h2]
      apply Finset.sum_eq_zero
      intro p hp
      have hp2 : p ≠ 2 := fun h => h2 (h ▸ hp)
      have hn : p-2 ≠ 0 := by have := Ξ.degree_ge_two p hp; omega
      simp [hn]
  rw [hs]
  unfold AdmissibleCovariance.first
  by_cases h2 : 2 ∈ Ξ.degrees
  · rw [ite_eq_left h2, ←Finset.sum_erase_add _ _ h2]
    norm_num
    ring
  · rw [ite_eq_right h2, Finset.erase_eq_self.mpr h2]
    simp

theorem first_le_quadratic_add_cubic (Ξ : AdmissibleCovariance)
    {q : ℝ} (hq : q∈Icc (0:ℝ) (1/2)) :
    Ξ.first q ≤ Ξ.second 0*q + (2*q)^3*Ξ.first (1/2) := by
  have hh : (∑p ∈ Ξ.degrees.erase 2, Ξ.coefficient p*(p:ℝ)*q^(p-1)) ≤
      (2*q)^3*(∑p ∈ Ξ.degrees.erase 2, Ξ.coefficient p*(p:ℝ)*(1/2:ℝ)^(p-1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hp' : p∈Ξ.degrees := Finset.mem_of_mem_erase hp
    have hpn : p≠2 := (Finset.mem_erase.mp hp).1
    have hge : 4≤p := by
      have htwo := Ξ.degree_ge_two p hp'
      rcases Ξ.degree_even p hp' with ⟨k,hk⟩
      omega
    have hn : 3≤p-1 := by omega
    have hbase0 : 0≤2*q := by linarith [hq.1]
    have hbase1 : 2*q≤1 := by linarith [hq.2]
    have hb := pow_le_pow_of_le_one hbase0 hbase1 hn
    have he : q^(p-1)=(1/2:ℝ)^(p-1)*(2*q)^(p-1) := by
      rw [←mul_pow]
      congr 1
      ring
    rw [he]
    have hc : 0≤Ξ.coefficient p*(p:ℝ)*(1/2:ℝ)^(p-1) := by
      exact mul_nonneg (mul_nonneg (Ξ.coefficient_pos p hp').le (Nat.cast_nonneg _))
        (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hb hc]
  have hhalf : (∑p ∈ Ξ.degrees.erase 2, Ξ.coefficient p*(p:ℝ)*(1/2:ℝ)^(p-1)) ≤
      Ξ.first (1/2) := by
    rw [first_eq_quadratic_add_higher Ξ (1/2)]
    have hn : 0≤Ξ.second 0 := Ξ.second_nonneg le_rfl
    linarith
  rw [first_eq_quadratic_add_higher Ξ q]
  exact add_le_add le_rfl (hh.trans
    (mul_le_mul_of_nonneg_left hhalf (pow_nonneg (by linarith [hq.1]) _)))

def originRadius (a C : ℝ) : ℝ :=
  min (1/2) (Real.sqrt ((1-a)/(16*C)))

theorem originRadius_pos {a C : ℝ} (ha : a<1) (hC : 0<C) :
    0<originRadius a C := by
  exact lt_min (by norm_num) (Real.sqrt_pos.mpr (by positivity))

theorem first_le_subcritical_overlap (Ξ : AdmissibleCovariance)
    {a C q : ℝ} (ha : Ξ.second 0≤a) (ha1 : a<1) (hC : Ξ.first (1/2)≤C)
    (hq : q∈Icc (0:ℝ) (originRadius a C)) :
    Ξ.first q ≤ ((1+a)/2)*q := by
  have hCp : 0<C := (Ξ.first_pos (by norm_num : (0:ℝ)<1/2)).trans_le hC
  have hqhalf : q≤1/2 := hq.2.trans (min_le_left _ _)
  have hs : 0≤(1-a)/(16*C) := by positivity
  have hqroot : q≤Real.sqrt ((1-a)/(16*C)) := hq.2.trans (min_le_right _ _)
  have hqsq := pow_le_pow_left₀ hq.1 hqroot 2
  rw [Real.sq_sqrt hs] at hqsq
  have hh := (le_div_iff₀ (by positivity : 0<16*C)).mp hqsq
  have hf := first_le_quadratic_add_cubic Ξ ⟨hq.1,hqhalf⟩
  have hlin := mul_le_mul_of_nonneg_right ha hq.1
  have hcub := mul_le_mul_of_nonneg_left hC
    (pow_nonneg (by linarith [hq.1] : 0≤2*q) 3)
  have hm := mul_le_mul_of_nonneg_left hh hq.1
  nlinarith

theorem Gamma_le_subcritical_overlap (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    {a C q : ℝ} (ha : Ξ.second 0≤a) (ha1 : a<1) (hC : Ξ.first (1/2)≤C)
    (hq : q∈Icc (0:ℝ) (originRadius a C)) :
    Gamma Ξ μ q ≤ ((1+a)/2)*q := by
  have hqone : q≤1 := (hq.2.trans (min_le_left _ _)).trans (by norm_num)
  exact (Gamma_le_first Ξ μ ⟨hq.1,hqone⟩).trans
    (first_le_subcritical_overlap Ξ ha ha1 hC hq)

theorem deriv_firstVariation_neg_near_origin (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    {a C q : ℝ} (ha : Ξ.second 0≤a) (ha1 : a<1) (hC : Ξ.first (1/2)≤C)
    (hq : q∈Ioc (0:ℝ) (originRadius a C)) :
    deriv (firstVariation Ξ μ) q<0 := by
  have hqhalf : q≤1/2 := hq.2.trans (min_le_left _ _)
  rw [(hasDerivAt_firstVariation Ξ μ ⟨hq.1,by linarith⟩).deriv]
  have hG := Gamma_le_subcritical_overlap Ξ μ ha ha1 hC ⟨hq.1.le,hq.2⟩
  have hm : ((1+a)/2)*q<q := by nlinarith [hq.1]
  exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) (Ξ.second_pos hq.1))
    (by linarith)

theorem firstVariation_neg_near_origin (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    {a C q : ℝ} (ha : Ξ.second 0≤a) (ha1 : a<1) (hC : Ξ.first (1/2)≤C)
    (hq : q∈Ioc (0:ℝ) (originRadius a C)) :
    firstVariation Ξ μ q<0 := by
  have hCp : 0<C := (Ξ.first_pos (by norm_num : (0:ℝ)<1/2)).trans_le hC
  have hR := originRadius_pos ha1 hCp
  have hm : StrictAntiOn (firstVariation Ξ μ) (Icc (0:ℝ) (originRadius a C)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      ((continuousOn_firstVariation Ξ μ).mono (Icc_subset_Icc_right
        ((min_le_left _ _).trans (by norm_num : (1/2:ℝ)≤1))))
    intro s hs
    rw [interior_Icc] at hs
    exact deriv_firstVariation_neg_near_origin Ξ μ ha ha1 hC ⟨hs.1,hs.2.le⟩
  simpa only [firstVariation_zero] using
    hm ⟨le_rfl,hR.le⟩ ⟨hq.1.le,hq.2⟩ hq.1


end GeneralDepthPaper
