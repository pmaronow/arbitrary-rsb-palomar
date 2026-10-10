module

public import GeneralDepthPaper.EndpointTermExpression
public import GeneralDepthPaper.ProductJetBounds

@[expose] public section


/-! Quadratic endpoint-distance bounds, including every genuine lower
parameter derivative. The correction is independent of atomic coordinates. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace GeneralDepthPaper
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 64

theorem norm_weighted_endpoint_integral_le {f : ℝ→ℝ} {Q C : ℝ}
    (hQ : Q∈Icc (0:ℝ) 1) (hC : 0 ≤ C) (hb : ∀q∈Icc (0:ℝ) 1,‖f q‖ ≤ C) :
    ‖∫q in Q..1,(1-q)*f q‖ ≤ C*(1-Q)^2 := by
  have H := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=Q) (b:=1) (C:=(1-Q)*C) (f:=fun q=>(1-q)*f q) (by
      intro q hq
      have hq' : q∈Ioc Q 1 := by simpa only [uIoc_of_le hQ.2] using hq
      have hq1 := hq'.1
      have hQ2 := hQ.2
      rw [norm_mul,Real.norm_of_nonneg (sub_nonneg.mpr hq'.2)]
      exact mul_le_mul (by linarith : 1-q ≤ 1-Q)
        (hb q ⟨hQ.1.trans hq'.1.le,hq'.2⟩) (norm_nonneg _) (by linarith))
  rw [abs_of_nonneg (sub_nonneg.mpr hQ.2)] at H
  convert H using 1 <;> ring

theorem endpointBaseIntegral_quadratic_bound (Ξ : AdmissibleCovariance) :
    ∃C:ℝ,0 ≤ C ∧ ∀Q∈Icc (0:ℝ) 1,
      ‖endpointBaseIntegral Ξ Q‖ ≤ C*(1-Q)^2 := by
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn Ξ.continuous_second.continuousOn
  refine ⟨max B 0,le_max_right _ _,?_⟩
  intro Q hQ
  rw [endpointBaseIntegral_eq_integral]
  exact norm_weighted_endpoint_integral_le hQ (le_max_right _ _)
    (fun q hq=>(hB q hq).trans (le_max_left _ _))

theorem endpointPowerIntegral_quadratic_bound (p : ℕ) (hp : 2 ≤ p)
    {Q : ℝ} (hQ : Q∈Icc (0:ℝ) 1) :
    ‖endpointPowerIntegral p Q‖ ≤ (p:ℝ)^2*(1-Q)^2 := by
  rw [endpointPowerIntegral_eq_integral p hp]
  have he : (fun q:ℝ=>(1-q)*(p:ℝ)*(p-1:ℕ)*q^(p-2))=
      (fun q=>(1-q)*((p:ℝ)*(p-1:ℕ)*q^(p-2))) := by funext q;ring
  rw [he]
  apply norm_weighted_endpoint_integral_le hQ (sq_nonneg _)
  intro q hq
  have hq0 := hq.1
  rw [Real.norm_of_nonneg (by positivity)]
  have hp1 : ((p-1:ℕ):ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
  have hpow := pow_le_one₀ hq.1 hq.2 (n:=p-2)
  calc
    _ ≤ (p:ℝ)*(p:ℝ)*1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp1 (Nat.cast_nonneg _)) hpow
        (pow_nonneg hq.1 _) (by positivity)
    _ = _ := by ring

theorem norm_iteratedFDeriv_affine_contraction {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (L : E→L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (a b : ℝ) {x : E} {B : ℝ} (hx : ‖L x‖ ≤ B) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y=>a+b*L y) x‖ ≤ ‖a‖+‖b‖*max B 1 := by
  have hf : ContDiff ℝ ∞ (fun r:ℝ=>a+b*r) := by fun_prop
  apply (norm_iteratedFDeriv_comp_contraction L hL _ hf j x).trans
  cases j with
  | zero=>
    simp only [iteratedDeriv_zero]
    exact (norm_add_le _ _).trans (by rw [norm_mul];gcongr;exact hx.trans (le_max_left _ _))
  | succ j=>
    rw [iteratedDeriv_const_add (by omega),iteratedDeriv_const_mul_field]
    change ‖b*iteratedDeriv (j+1) id (L x)‖ ≤ _
    cases j with
    | zero=>
      simp only [iteratedDeriv_id,zero_add,one_ne_zero,↓reduceIte,mul_one]
      calc
        ‖b‖ ≤ ‖b‖*max B 1 := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left (le_max_right B 1) (norm_nonneg b)
        _ ≤ _ := le_add_of_nonneg_left (norm_nonneg a)
    | succ j=>
      simp only [iteratedDeriv_id,show j+1+1≠0 by omega,show j+1+1≠1 by omega,
        ↓reduceIte,mul_zero,norm_zero]
      have hm : 0 ≤ max B 1 := zero_le_one.trans (le_max_right _ _)
      positivity

def lowerMassProjection {r : ℕ} : HighDegreeLowerParameter r→L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    (ContinuousLinearMap.snd ℝ (AtomicPoint r) (ℝ×ℝ))

def lowerLambdaProjection {r : ℕ} : HighDegreeLowerParameter r→L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
    (ContinuousLinearMap.snd ℝ (AtomicPoint r) (ℝ×ℝ))

theorem norm_lowerMassProjection_le {r : ℕ} : ‖lowerMassProjection (r:=r)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  exact (norm_fst_le x.2).trans (by simpa only [one_mul] using norm_snd_le x)

theorem norm_lowerLambdaProjection_le {r : ℕ} : ‖lowerLambdaProjection (r:=r)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  exact (norm_snd_le x.2).trans (by simpa only [one_mul] using norm_snd_le x)

theorem endpointTerm_pure_core_jet_bound (Ξ : AdmissibleCovariance) {r : ℕ}
    (L : ℝ) (N : ℕ) :
    ∃C:ℝ,0 ≤ C ∧ ∀p:ℕ,2 ≤ p→∀Q∈Icc (0:ℝ) 1,
      ∀θ:HighDegreeLowerParameter r,θ.2.1∈Icc (0:ℝ) 1→θ.2.2∈Icc (0:ℝ) L→
        ∀j:ℕ,j ≤ N→
          ‖iteratedFDeriv ℝ j
            (fun u:HighDegreeLowerParameter r=>endpointTermExpression Ξ p (u.1,(u.2.1,(u.2.2,Q)))) θ‖ ≤
              C*(p:ℝ)^2*(1-Q)^2 := by
  obtain ⟨B,hB,hbase⟩ := endpointBaseIntegral_quadratic_bound Ξ
  let D := max L 1
  have hD : 1 ≤ D := le_max_right _ _
  refine ⟨(2:ℝ)^N*(B+D),by dsimp only [D];positivity,?_⟩
  intro p hp Q hQ θ hm hl j hj
  let f : HighDegreeLowerParameter r→ℝ := fun u=>(1-u.2.1)/2
  let g : HighDegreeLowerParameter r→ℝ := fun u=>endpointBaseIntegral Ξ Q+
    u.2.2*endpointPowerIntegral p Q
  have hf : ContDiff ℝ ∞ f := by dsimp only [f];fun_prop
  have hg : ContDiff ℝ ∞ g := by dsimp only [g];fun_prop
  have hfB (i:ℕ) : ‖iteratedFDeriv ℝ i f θ‖ ≤ 1 := by
    have h := norm_iteratedFDeriv_affine_contraction (lowerMassProjection (r:=r))
      norm_lowerMassProjection_le (1/2) (-1/2)
      (x:=θ) (B:=1) (by change ‖θ.2.1‖ ≤ 1;rw [Real.norm_of_nonneg hm.1];exact hm.2) i
    have he : f=(fun u=>1/2+(-1/2)*lowerMassProjection u) := by funext u;dsimp [f,lowerMassProjection];ring
    rw [he]
    norm_num at h ⊢
    exact h
  have hgB (i:ℕ) : ‖iteratedFDeriv ℝ i g θ‖ ≤ (B+D)*(p:ℝ)^2*(1-Q)^2 := by
    have h := norm_iteratedFDeriv_affine_contraction (lowerLambdaProjection (r:=r))
      norm_lowerLambdaProjection_le (endpointBaseIntegral Ξ Q) (endpointPowerIntegral p Q)
      (x:=θ) (B:=L) (by change ‖θ.2.2‖ ≤ L;rw [Real.norm_of_nonneg hl.1];exact hl.2) i
    have he : g=(fun u=>endpointBaseIntegral Ξ Q+endpointPowerIntegral p Q*lowerLambdaProjection u) := by
      funext u;dsimp [g,lowerLambdaProjection];ring
    rw [he]
    apply h.trans
    have hpR : (1:ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
    have hpow : 1 ≤ (p:ℝ)^2 := one_le_pow₀ hpR
    have hbasep := mul_le_mul_of_nonneg_right hpow (mul_nonneg hB (sq_nonneg (1-Q)))
    have hpw := mul_le_mul_of_nonneg_right (endpointPowerIntegral_quadratic_bound p hp hQ) (hD.trans' zero_le_one)
    have hbq := hbase Q hQ
    dsimp only [D] at hpw
    nlinarith
  have H := norm_iteratedFDeriv_mul_bound_at hf.contDiffAt hg.contDiffAt j 1
    ((B+D)*(p:ℝ)^2*(1-Q)^2) zero_le_one (by positivity) (fun i _=>hfB i) (fun i _=>hgB i)
  change ‖iteratedFDeriv ℝ j (fun u=>f u*g u) θ‖ ≤ _
  apply H.trans
  have h2pow : (2:ℝ)^j ≤ (2:ℝ)^N := pow_le_pow_right₀ (by norm_num) hj
  simpa only [mul_one,mul_assoc] using mul_le_mul_of_nonneg_right h2pow
    (show 0 ≤ (B+D)*(p:ℝ)^2*(1-Q)^2 by positivity)

end GeneralDepthPaper
