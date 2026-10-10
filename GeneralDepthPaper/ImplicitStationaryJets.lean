module

public import GeneralDepthPaper.ConvexStationaryBall
public import GeneralDepthPaper.PointwiseDerivativeBounds
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

set_option backward.privateInPublic true

@[expose] public section


/-! Actual first and second differentiated stationarity equations.  These
are identities for genuine smooth functions, rather than prescribed jets. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GeneralDepthPaper
variable {Θ E : Type*}
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 64

private theorem eventually_stationary_differentiable {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X→Y} {x : X} (hf : ContDiffAt ℝ ∞ f x) :
    ∀ᶠy in 𝓝 x,DifferentiableAt ℝ f y := by
  have he : ∀ᶠy in 𝓝 x,ContDiffAt ℝ 1 f y :=
    (hf.of_le (show (1:ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)
  exact he.mono (fun _ hy=>hy.differentiableAt (by simp))

def stationaryGraph (q : Θ→E) (θ : Θ) : Θ×E := (θ,q θ)

theorem stationaryGraph_fderiv {q : Θ→E} {θ : Θ}
    (hq : DifferentiableAt ℝ q θ) :
    fderiv ℝ (stationaryGraph q) θ=
      ContinuousLinearMap.inl ℝ Θ E + (ContinuousLinearMap.inr ℝ Θ E).comp (fderiv ℝ q θ) := by
  rw [show stationaryGraph q=(fun u=>(id u,q u)) by rfl,
    DifferentiableAt.fderiv_prodMk differentiableAt_id hq,fderiv_id]
  ext v <;> simp

theorem stationaryGraph_first_norm_le {q : Θ→E} {θ : Θ}
    (hq : ContDiffAt ℝ ∞ q θ) :
    ‖fderiv ℝ (stationaryGraph q) θ‖ ≤ max 1 ‖fderiv ℝ q θ‖ := by
  change ‖fderiv ℝ (fun u=>(id u,q u)) θ‖ ≤ _
  rw [DifferentiableAt.fderiv_prodMk differentiableAt_id (hq.differentiableAt (by simp)),
    ContinuousLinearMap.opNorm_prod,Prod.norm_def,fderiv_id]
  exact max_le_max ContinuousLinearMap.norm_id_le le_rfl

theorem stationaryGraph_second_apply {q : Θ→E} {θ : Θ}
    (hq : ContDiffAt ℝ ∞ q θ) (v w : Θ) :
    fderiv ℝ (fderiv ℝ (stationaryGraph q)) θ v w=
      (0,fderiv ℝ (fderiv ℝ q) θ v w) := by
  have he : fderiv ℝ (stationaryGraph q) =ᶠ[𝓝 θ]
      (fun u=>ContinuousLinearMap.inl ℝ Θ E+
        (ContinuousLinearMap.inr ℝ Θ E).comp (fderiv ℝ q u)) := by
    filter_upwards [eventually_stationary_differentiable hq] with u hu
    exact stationaryGraph_fderiv hu
  have hdq : DifferentiableAt ℝ (fderiv ℝ q) θ :=
    (hq.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)
  have hc := (hasFDerivAt_const (𝕜:=ℝ) (x:=θ) (ContinuousLinearMap.inr ℝ Θ E)).clm_comp
    hdq.hasFDerivAt
  have ha := (hasFDerivAt_const (𝕜:=ℝ) (x:=θ) (ContinuousLinearMap.inl ℝ Θ E)).add hc
  simp only [Pi.add_def] at ha
  rw [he.fderiv_eq,ha.fderiv]
  simp

theorem eventually_stationary_differential
    {G : Θ×E→E→L[ℝ]ℝ} {q : Θ→E} {θ : Θ}
    (hG : ContDiffAt ℝ ∞ G (stationaryGraph q θ))
    (hq : ContDiffAt ℝ ∞ q θ)
    (heq : ∀ᶠu in 𝓝 θ,G (stationaryGraph q u)=0) :
    (fun u=>(fderiv ℝ G (stationaryGraph q u)).comp (fderiv ℝ (stationaryGraph q) u))
      =ᶠ[𝓝 θ] (fun _=>0) := by
  have hH : ContDiffAt ℝ ∞ (stationaryGraph q) θ := contDiffAt_id.prodMk hq
  have hGe : ∀ᶠz in 𝓝 (stationaryGraph q θ),DifferentiableAt ℝ G z :=
    eventually_stationary_differentiable hG
  have hGd := hH.continuousAt.eventually hGe
  have hHd := eventually_stationary_differentiable hH
  have he : G ∘ stationaryGraph q =ᶠ[𝓝 θ] (fun _=>0) := heq
  filter_upwards [he.fderiv (𝕜:=ℝ),hGd,hHd] with u hu hGu hHu
  rw [fderiv_comp u hGu hHu] at hu
  exact hu.trans (hasFDerivAt_const (𝕜:=ℝ) (x:=u) (c:=(0:E→L[ℝ]ℝ))).fderiv

theorem stationary_first_equation
    {G : Θ×E→E→L[ℝ]ℝ} {q : Θ→E} {θ : Θ}
    (hG : ContDiffAt ℝ ∞ G (stationaryGraph q θ))
    (hq : ContDiffAt ℝ ∞ q θ)
    (heq : ∀ᶠu in 𝓝 θ,G (stationaryGraph q u)=0) (v : Θ) :
    (fderiv ℝ G (stationaryGraph q θ) (0,fderiv ℝ q θ v))=
      -fderiv ℝ G (stationaryGraph q θ) (v,0) := by
  have he := congrArg (fun L : Θ→L[ℝ] (E→L[ℝ]ℝ)=>L v)
    (eventually_stationary_differential hG hq heq).eq_of_nhds
  rw [stationaryGraph_fderiv (hq.differentiableAt (by simp))] at he
  change (fderiv ℝ G (stationaryGraph q θ)) ((v,0)+(0,fderiv ℝ q θ v))=0 at he
  rw [map_add] at he
  exact eq_neg_of_add_eq_zero_right he

theorem stationary_second_equation
    {G : Θ×E→E→L[ℝ]ℝ} {q : Θ→E} {θ : Θ}
    (hG : ContDiffAt ℝ ∞ G (stationaryGraph q θ))
    (hq : ContDiffAt ℝ ∞ q θ)
    (heq : ∀ᶠu in 𝓝 θ,G (stationaryGraph q u)=0) (v w : Θ) :
    fderiv ℝ G (stationaryGraph q θ) (0,fderiv ℝ (fderiv ℝ q) θ v w)=
      -fderiv ℝ (fderiv ℝ G) (stationaryGraph q θ)
        (v,fderiv ℝ q θ v) (w,fderiv ℝ q θ w) := by
  let H := stationaryGraph q
  let U := fun u=>fderiv ℝ G (H u)
  let V := fderiv ℝ H
  have hH : ContDiffAt ℝ ∞ H θ := contDiffAt_id.prodMk hq
  have hDG := hG.fderiv_right (m:=∞) (by simp)
  have hU : DifferentiableAt ℝ U θ :=
    (hDG.comp θ hH).differentiableAt (by simp)
  have hV : DifferentiableAt ℝ V θ :=
    (hH.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)
  have hd := hU.hasFDerivAt.clm_comp hV.hasFDerivAt
  have he := (eventually_stationary_differential hG hq heq).fderiv_eq (𝕜:=ℝ)
  have hz : fderiv ℝ (fun u=>(U u).comp (V u)) θ=0 := by simpa [U,V,H] using he
  rw [hd.fderiv] at hz
  have heval := congrArg (fun L : Θ→L[ℝ] (Θ→L[ℝ] (E→L[ℝ]ℝ))=>L v w) hz
  have hdu : fderiv ℝ U θ=(fderiv ℝ (fderiv ℝ G) (H θ)).comp (fderiv ℝ H θ) :=
    fderiv_comp θ (hDG.differentiableAt (by simp)) (hH.differentiableAt (by simp))
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply,zero_apply] at heval
  rw [hdu] at heval
  change fderiv ℝ G (H θ) (fderiv ℝ (fderiv ℝ H) θ v w)+
    fderiv ℝ (fderiv ℝ G) (H θ) (fderiv ℝ H θ v) (fderiv ℝ H θ w)=0 at heval
  rw [stationaryGraph_second_apply hq,
    stationaryGraph_fderiv (hq.differentiableAt (by simp))] at heval
  simp [H] at heval
  exact eq_neg_of_add_eq_zero_left heval

/-- Quantitative inversion of a coercive map into the continuous dual. -/
theorem coercive_linear_vector_bound (B : E→L[ℝ] E→L[ℝ]ℝ) {κ : ℝ}
    (hκ : 0<κ) (hB : ∀v:E,κ*‖v‖^2 ≤ B v v) (v : E) :
    ‖v‖ ≤ ‖B v‖/κ := by
  have hb := (hB v).trans ((le_abs_self _).trans ((by
    simpa only [Real.norm_eq_abs] using (B v).le_opNorm v)))
  apply (le_div_iff₀ hκ).mpr
  by_cases hv : ‖v‖=0
  · simp only [hv,zero_mul];exact norm_nonneg _
  · have hp : 0<‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    nlinarith

theorem norm_curried_bilinear_apply_le {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (M : X→L[ℝ] Y→L[ℝ] Z) (x : X) (y : Y) :
    ‖M x y‖ ≤ ‖M‖*‖x‖*‖y‖ :=
  ((M x).le_opNorm y).trans (mul_le_mul_of_nonneg_right (M.le_opNorm x) (norm_nonneg y))

/-- A true first stationary jet is bounded by the inverse coercivity. -/
theorem stationary_first_norm_bound
    {G : Θ×E→E→L[ℝ]ℝ} {q : Θ→E} {θ : Θ} {κ : ℝ}
    (hG : ContDiffAt ℝ ∞ G (stationaryGraph q θ))
    (hq : ContDiffAt ℝ ∞ q θ)
    (heq : ∀ᶠu in 𝓝 θ,G (stationaryGraph q u)=0)
    (hκ : 0<κ)
    (hB : ∀z:E,κ*‖z‖^2 ≤ fderiv ℝ G (stationaryGraph q θ) (0,z) z) :
    ‖fderiv ℝ q θ‖ ≤ ‖fderiv ℝ G (stationaryGraph q θ)‖/κ := by
  apply (fderiv ℝ q θ).opNorm_le_bound (by positivity)
  intro v
  let B := (fderiv ℝ G (stationaryGraph q θ)).comp (ContinuousLinearMap.inr ℝ Θ E)
  have hc := coercive_linear_vector_bound B hκ hB (fderiv ℝ q θ v)
  have he := stationary_first_equation hG hq heq v
  change ‖fderiv ℝ q θ v‖ ≤ ‖fderiv ℝ G (stationaryGraph q θ) (0,fderiv ℝ q θ v)‖/κ at hc
  rw [he,norm_neg] at hc
  calc
    _ ≤ _ := hc
    _ ≤ (‖fderiv ℝ G (stationaryGraph q θ)‖*‖v‖)/κ := by
      apply div_le_div_of_nonneg_right _ hκ.le
      simpa only [Prod.norm_def,norm_zero,max_eq_left (norm_nonneg v)] using
        (fderiv ℝ G (stationaryGraph q θ)).le_opNorm (v,0)
    _ = _ := by ring

/-- The second stationary jet is obtained from the actual twice-differentiated
equation and has a uniform quantitative bound. -/
theorem stationary_second_norm_bound
    {G : Θ×E→E→L[ℝ]ℝ} {q : Θ→E} {θ : Θ} {κ D : ℝ}
    (hG : ContDiffAt ℝ ∞ G (stationaryGraph q θ))
    (hq : ContDiffAt ℝ ∞ q θ)
    (heq : ∀ᶠu in 𝓝 θ,G (stationaryGraph q u)=0)
    (hκ : 0<κ) (hD : 0≤D)
    (hB : ∀z:E,κ*‖z‖^2 ≤ fderiv ℝ G (stationaryGraph q θ) (0,z) z)
    (h1 : ‖fderiv ℝ G (stationaryGraph q θ)‖ ≤ D)
    (h2 : ‖fderiv ℝ (fderiv ℝ G) (stationaryGraph q θ)‖ ≤ D) :
    ‖fderiv ℝ (fderiv ℝ q) θ‖ ≤ D*(max 1 (D/κ))^2/κ := by
  let A := max 1 (D/κ)
  have hA : 0≤A := (show (0:ℝ)≤1 by norm_num).trans (le_max_left _ _)
  have hq1 := (stationary_first_norm_bound hG hq heq hκ hB).trans
    (div_le_div_of_nonneg_right h1 hκ.le)
  have hg : ‖fderiv ℝ (stationaryGraph q) θ‖ ≤ A :=
    (stationaryGraph_first_norm_le hq).trans (max_le_max le_rfl hq1)
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro w hw
  let B := (fderiv ℝ G (stationaryGraph q θ)).comp (ContinuousLinearMap.inr ℝ Θ E)
  have hc := coercive_linear_vector_bound B hκ hB (fderiv ℝ (fderiv ℝ q) θ v w)
  have he := stationary_second_equation hG hq heq v w
  change ‖fderiv ℝ (fderiv ℝ q) θ v w‖ ≤
    ‖fderiv ℝ G (stationaryGraph q θ) (0,fderiv ℝ (fderiv ℝ q) θ v w)‖/κ at hc
  rw [he,norm_neg] at hc
  have hvb : ‖(v,fderiv ℝ q θ v)‖ ≤ A := by
    have hh := (fderiv ℝ (stationaryGraph q) θ).le_opNorm v
    have hh' := hh.trans (mul_le_mul_of_nonneg_right hg (norm_nonneg v))
    simpa [stationaryGraph_fderiv (hq.differentiableAt (by simp)),hv] using hh'
  have hwb : ‖(w,fderiv ℝ q θ w)‖ ≤ A := by
    have hh := (fderiv ℝ (stationaryGraph q) θ).le_opNorm w
    have hh' := hh.trans (mul_le_mul_of_nonneg_right hg (norm_nonneg w))
    simpa [stationaryGraph_fderiv (hq.differentiableAt (by simp)),hw] using hh'
  apply hc.trans
  apply div_le_div_of_nonneg_right _ hκ.le
  apply (norm_curried_bilinear_apply_le _ _ _).trans
  have hp := mul_le_mul h2 hvb (norm_nonneg _) hD
  have hp' := mul_le_mul hp hwb (norm_nonneg _) (mul_nonneg hD hA)
  simpa only [pow_two,mul_assoc] using hp'

end GeneralDepthPaper
