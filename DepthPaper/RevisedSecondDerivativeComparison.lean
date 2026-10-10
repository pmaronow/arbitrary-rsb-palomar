module

public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

/-! Necessary second-derivative and touching-function comparison lemmas.
These compare actual derivatives; no convexity or positivity premise is
substituted for a second-order conclusion. -/
noncomputable section
open Set Filter SignType
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 1500000

theorem secondDerivative_nonneg_of_localMin {f : ℝ → ℝ} {x d : ℝ}
    (hmin : IsLocalMin f x)
    (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y)
    (h2 : HasDerivAt (deriv f) d x) : 0 ≤ d := by
  by_contra hn
  have hdneg : deriv (deriv f) x < 0 := by rw [h2.deriv]; exact lt_of_not_ge hn
  have hzero : deriv f x = 0 := hmin.deriv_eq_zero
  have hsign := eventually_nhdsWithin_sign_eq_of_deriv_neg hdneg hzero
  have hlocal : ∀ᶠ y in 𝓝 x, f x ≤ f y ∧ DifferentiableAt ℝ f y ∧
      sign (deriv f y) = sign (x-y) := hmin.and (hf.and hsign)
  obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff.mp hlocal
  let b := x + ε / 2
  have hxb : x < b := by dsimp only [b]; linarith
  have hmem (y : ℝ) (hy : y ∈ Icc x b) : dist y x < ε := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hy.1)]
    dsimp only [b] at hy
    linarith [hy.2]
  have hanti : StrictAntiOn f (Icc x b) :=
    strictAntiOn_of_deriv_neg (convex_Icc x b)
      (fun y hy => (hb (hmem y hy)).2.1.continuousAt.continuousWithinAt) (by
        intro y hy
        rw [interior_Icc] at hy
        have hs := (hb (hmem y ⟨hy.1.le, hy.2.le⟩)).2.2
        have hxyn : x-y < 0 := sub_neg.mpr hy.1
        rw [sign_eq_neg_one_iff.mpr hxyn] at hs
        exact sign_eq_neg_one_iff.mp hs)
  have hlt := hanti ⟨le_rfl, hxb.le⟩ ⟨hxb.le, le_rfl⟩ hxb
  have hle := (hb (hmem b ⟨hxb.le, le_rfl⟩)).1
  exact (not_lt_of_ge hle) hlt

theorem secondDerivative_le_of_touching {F G : ℝ → ℝ} {x dF dG : ℝ}
    (hFG : ∀ᶠ y in 𝓝 x, G y ≤ F y) (he : G x = F x)
    (hF : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ F y)
    (hG : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ G y)
    (hF2 : HasDerivAt (deriv F) dF x) (hG2 : HasDerivAt (deriv G) dG x) :
    dG ≤ dF := by
  have hmin : IsLocalMin (fun y => F y - G y) x := by
    filter_upwards [hFG] with y hy
    rw [← he, sub_self]
    exact sub_nonneg.mpr hy
  have hdiff : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (fun y => F y-G y) y := by
    filter_upwards [hF, hG] with y hyF hyG
    exact hyF.sub hyG
  have hederiv : deriv (fun y => F y-G y) =ᶠ[𝓝 x] fun y => deriv F y-deriv G y := by
    filter_upwards [hF, hG] with y hyF hyG
    exact deriv_sub hyF hyG
  have h2 : HasDerivAt (deriv (fun y => F y-G y)) (dF-dG) x :=
    (hF2.sub hG2).congr_of_eventuallyEq hederiv
  exact sub_nonneg.mp (secondDerivative_nonneg_of_localMin hmin hdiff h2)

theorem secondDerivative_nonneg_of_right_touch {f : ℝ → ℝ} {x d : ℝ}
    (hmin : ∀ᶠ y in 𝓝[>] x, f x ≤ f y)
    (hzero : deriv f x = 0)
    (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y)
    (h2 : HasDerivAt (deriv f) d x) : 0 ≤ d := by
  by_contra hn
  have hdneg : deriv (deriv f) x < 0 := by rw [h2.deriv]; exact lt_of_not_ge hn
  have hsign := eventually_nhdsWithin_sign_eq_of_deriv_neg hdneg hzero
  obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff.mp (hf.and hsign)
  have hmin' : ∀ᶠ y in 𝓝 x, x < y → f x ≤ f y := eventually_nhdsWithin_iff.mp hmin
  obtain ⟨δ, hδ, hminδ⟩ := Metric.eventually_nhds_iff.mp hmin'
  let b := x + min ε δ / 2
  have hεδ : 0 < min ε δ := lt_min hε hδ
  have hxb : x < b := by dsimp only [b]; linarith
  have hmem (y : ℝ) (hy : y ∈ Icc x b) : dist y x < ε := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hy.1)]
    dsimp only [b] at hy
    linarith [hy.2, min_le_left ε δ]
  have hanti : StrictAntiOn f (Icc x b) :=
    strictAntiOn_of_deriv_neg (convex_Icc x b)
      (fun y hy => (hb (hmem y hy)).1.continuousAt.continuousWithinAt) (by
        intro y hy
        rw [interior_Icc] at hy
        have hs := (hb (hmem y ⟨hy.1.le, hy.2.le⟩)).2
        rw [sign_eq_neg_one_iff.mpr (sub_neg.mpr hy.1)] at hs
        exact sign_eq_neg_one_iff.mp hs)
  have hlt := hanti ⟨le_rfl, hxb.le⟩ ⟨hxb.le, le_rfl⟩ hxb
  have hbd : dist b x < δ := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hxb)]
    dsimp only [b]
    linarith [min_le_right ε δ]
  exact (not_lt_of_ge (hminδ hbd hxb)) hlt

theorem secondDerivative_le_of_right_touching {F G : ℝ → ℝ} {x dF dG : ℝ}
    (hFG : ∀ᶠ y in 𝓝[>] x, G y ≤ F y) (he : G x = F x)
    (hF1 : deriv F x = deriv G x)
    (hF : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ F y)
    (hG : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ G y)
    (hF2 : HasDerivAt (deriv F) dF x) (hG2 : HasDerivAt (deriv G) dG x) :
    dG ≤ dF := by
  have hmin : ∀ᶠ y in 𝓝[>] x, (F x-G x) ≤ F y-G y := by
    filter_upwards [hFG] with y hy
    rw [← he, sub_self]
    exact sub_nonneg.mpr hy
  have hdiff : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (fun y => F y-G y) y := by
    filter_upwards [hF, hG] with y hyF hyG
    exact hyF.sub hyG
  have hederiv : deriv (fun y => F y-G y) =ᶠ[𝓝 x] fun y => deriv F y-deriv G y := by
    filter_upwards [hF, hG] with y hyF hyG
    exact deriv_sub hyF hyG
  have h2 : HasDerivAt (deriv (fun y => F y-G y)) (dF-dG) x :=
    (hF2.sub hG2).congr_of_eventuallyEq hederiv
  exact sub_nonneg.mp (secondDerivative_nonneg_of_right_touch hmin
    (by simpa only [hederiv.self_of_nhds, hF1, sub_self]) hdiff h2)

theorem hasDerivAt_deriv_affine_line {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : E → ℝ} {z v : E}
    (hF : ContDiffAt ℝ 2 F z) :
    HasDerivAt (deriv (fun t : ℝ => F (z+t • v)))
      (fderiv ℝ (fderiv ℝ F) z v v) 0 := by
  have hpath : HasDerivAt (fun t : ℝ => z+t • v) v 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have hgrad : DifferentiableAt ℝ (fderiv ℝ F) z :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hgrad0 : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) z) (z+(0 : ℝ) • v) := by
    simpa using hgrad.hasFDerivAt
  have hd := (hgrad0.comp_hasDerivAt (0 : ℝ) hpath).clm_apply
    (hasDerivAt_const (0 : ℝ) v)
  have he : deriv (fun t : ℝ => F (z+t • v)) =ᶠ[𝓝 (0 : ℝ)]
      fun t => fderiv ℝ F (z+t • v) v := by
    have hnear := hF.eventually (by norm_num : (2 : ℕ∞ω) ≠ ∞)
    have htend : Tendsto (fun t : ℝ => z+t • v) (𝓝 0) (𝓝 z) := by
      simpa using hpath.continuousAt.tendsto
    filter_upwards [htend.eventually hnear] with t ht
    have hp : HasDerivAt (fun t : ℝ => z+t • v) v t := by
      simpa only [id_eq, one_smul] using ((hasDerivAt_id t).smul_const v).const_add z
    exact ((ht.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t hp).deriv
  simpa only [map_zero, add_zero] using hd.congr_of_eventuallyEq he

theorem hasDerivAt_deriv_rescaled_affine_correction
    {H : ℝ → ℝ} {ε c d₀ d d₂ : ℝ}
    (hH : ∀t,DifferentiableAt ℝ H t) (hH₂ : HasDerivAt (deriv H) d₂ 0) :
    HasDerivAt (deriv (fun t : ℝ => c+H (t/ε)-(d₀+(t/ε)*d)/2))
      (d₂/ε^2) 0 := by
  have hline (t : ℝ) : HasDerivAt (fun s : ℝ => s/ε) (1/ε) t := by
    simpa only [id_eq] using (hasDerivAt_id t).div_const ε
  have he : deriv (fun t : ℝ => c+H (t/ε)-(d₀+(t/ε)*d)/2) =
      fun t => deriv H (t/ε)*(1/ε)-(1/ε)*d/2 := by
    funext t
    have hmain := ((hH (t/ε)).hasDerivAt.comp t (hline t)).const_add c
    have hcorr := (((hline t).mul_const d).const_add d₀).div_const 2
    have hd := (hmain.sub hcorr).deriv
    simp only [Function.comp_def] at hd
    have hfun : ((fun x : ℝ => c+H (x/ε))-(fun x : ℝ => (d₀+x/ε*d)/2)) =
        (fun x : ℝ => c+H (x/ε)-(d₀+x/ε*d)/2) := by funext x; rfl
    rw [hfun] at hd
    simpa only [Function.comp_def] using hd
  rw [he]
  have hbase : HasDerivAt (deriv H) d₂ ((0 : ℝ)/ε) := by simpa using hH₂
  convert ((hbase.comp (0 : ℝ) (hline 0)).mul_const (1/ε)).sub_const ((1/ε)*d/2) using 1
  · funext t
    simp only [Function.comp_def]
  · simp only [div_eq_mul_inv,one_mul,inv_pow,pow_two]
    ring

end DepthPaper
