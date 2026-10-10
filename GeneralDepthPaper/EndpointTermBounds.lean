module

public import GeneralDepthPaper.EndpointTermGapBounds

@[expose] public section


/-! Uniform polynomial bounds on all full parameter jets of the actual
endpoint correction. The lower-parameter estimates retain the quadratic
endpoint gap in EndpointTermGapBounds. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace GeneralDepthPaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 64

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iteratedFDeriv_endpointPowerIntegral_unit
    (L : E→L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (p : ℕ) (hp : 1 ≤ p)
    {x : E} (hx : L x∈Icc (0:ℝ) 1) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y=>endpointPowerIntegral p (L y)) x‖ ≤ 3*(p:ℝ)^(j+1) := by
  let f : E→ℝ := fun y=>(L y)^p
  let g : E→ℝ := fun y=>(L y)^(p-1)
  have hf : ContDiff ℝ ∞ f := L.contDiff.pow p
  have hg : ContDiff ℝ ∞ g := L.contDiff.pow (p-1)
  have hfp := (norm_iteratedFDeriv_comp_contraction L hL (fun q:ℝ=>q^p)
    (contDiff_id.pow p) j x).trans (norm_iteratedDeriv_pow_unit p j hx)
  have hgp := (norm_iteratedFDeriv_comp_contraction L hL (fun q:ℝ=>q^(p-1))
    (contDiff_id.pow (p-1)) j x).trans ((norm_iteratedDeriv_pow_unit (p-1) j hx).trans
      (pow_le_pow_left₀ (Nat.cast_nonneg _)
        (by exact_mod_cast Nat.sub_le p 1 : ((p-1:ℕ):ℝ) ≤ (p:ℝ)) j))
  have hc : ‖iteratedFDeriv ℝ j (fun _:E=>(1:ℝ)) x‖ ≤ 1 := by
    cases j with
    | zero=>simp
    | succ j=>simp only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero];norm_num
  have he : (fun y=>endpointPowerIntegral p (L y))=
      (fun y=>(1:ℝ)+((p-1:ℕ):ℝ) • f y-(p:ℝ) • g y) := by
    funext y;rfl
  rw [he,fun_iteratedFDeriv_sub_apply
    ((contDiff_const.add (hf.const_smul _)).of_le (by simp)).contDiffAt
    ((hg.const_smul _).of_le (by simp)).contDiffAt,
    fun_iteratedFDeriv_add_apply contDiffAt_const
    ((hf.const_smul _).of_le (by simp)).contDiffAt,
    iteratedFDeriv_const_smul_apply' (hf.of_le (by simp)).contDiffAt,
    iteratedFDeriv_const_smul_apply' (hg.of_le (by simp)).contDiffAt]
  have hpm : ‖((p-1:ℕ):ℝ)‖ ≤ p := by
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast Nat.sub_le p 1
  have hp0 : 0 ≤ (p:ℝ) := Nat.cast_nonneg _
  have hpf : ‖((p-1:ℕ):ℝ) • iteratedFDeriv ℝ j f x‖ ≤ (p:ℝ)*(p:ℝ)^j := by
    rw [norm_smul]
    exact mul_le_mul hpm hfp (norm_nonneg _) hp0
  have hpg : ‖(p:ℝ) • iteratedFDeriv ℝ j g x‖ ≤ (p:ℝ)*(p:ℝ)^j := by
    rw [norm_smul,Real.norm_of_nonneg hp0]
    exact mul_le_mul_of_nonneg_left hgp hp0
  have hpow : 1 ≤ (p:ℝ)^(j+1) := one_le_pow₀ (by exact_mod_cast hp)
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (fun _:E=>(1:ℝ)) x‖+
        ‖((p-1:ℕ):ℝ) • iteratedFDeriv ℝ j f x‖+
        ‖(p:ℝ) • iteratedFDeriv ℝ j g x‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 1+(p:ℝ)*(p:ℝ)^j+(p:ℝ)*(p:ℝ)^j := add_le_add (add_le_add hc hpf) hpg
    _ ≤ _ := by rw [pow_succ] at hpow ⊢;nlinarith

def fullMassProjection {r : ℕ} : CutoffInputParameter r→L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ (ℝ×ℝ)).comp
    (ContinuousLinearMap.snd ℝ (AtomicPoint r) (ℝ×(ℝ×ℝ)))

def fullLambdaProjection {r : ℕ} : CutoffInputParameter r→L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp endpointPairProjection

def fullQProjection {r : ℕ} : CutoffInputParameter r→L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp endpointPairProjection

theorem norm_fullMassProjection_le {r : ℕ} : ‖fullMassProjection (r:=r)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  exact (norm_fst_le x.2).trans (by simpa only [one_mul] using norm_snd_le x)

theorem norm_fullLambdaProjection_le {r : ℕ} : ‖fullLambdaProjection (r:=r)‖ ≤ 1 := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  exact (mul_le_mul (ContinuousLinearMap.norm_fst_le ..) norm_endpointPairProjection_le
    (norm_nonneg _) zero_le_one).trans_eq (mul_one _)

theorem norm_fullQProjection_le {r : ℕ} : ‖fullQProjection (r:=r)‖ ≤ 1 := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  exact (mul_le_mul (ContinuousLinearMap.norm_snd_le ..) norm_endpointPairProjection_le
    (norm_nonneg _) zero_le_one).trans_eq (mul_one _)

theorem endpointTerm_full_jet_bound (Ξ : AdmissibleCovariance) {r : ℕ}
    (L : ℝ) (N : ℕ) :
    ∃C:ℝ,1 ≤ C ∧ ∀p:ℕ,2 ≤ p→∀x:CutoffInputParameter r,
      x.2.1∈Icc (0:ℝ) 1→x.2.2.1∈Icc (0:ℝ) L→x.2.2.2∈Icc (0:ℝ) 1→
        ∀j:ℕ,j ≤ N→‖iteratedFDeriv ℝ j (endpointTermExpression Ξ p) x‖ ≤ C*(p:ℝ)^(N+1) := by
  obtain ⟨B,hB,hBb⟩ := (BoundedSmoothOn.of_compact (s:=Icc (0:ℝ) 1) isCompact_Icc
    (fun Q _=>(contDiff_endpointBaseIntegral Ξ).contDiffAt)).all_orders_up_to_bound N
  let D := max L 1
  have hD : 1 ≤ D := le_max_right _ _
  let C := (2:ℝ)^N*(B+(2:ℝ)^N*D*3)
  have hC : 1 ≤ C := by
    have h2 : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
    have hh : 1 ≤ B+(2:ℝ)^N*D*3 := hB.trans (le_add_of_nonneg_right (by positivity))
    dsimp only [C]
    simpa only [one_mul] using mul_le_mul h2 hh zero_le_one (zero_le_one.trans h2)
  refine ⟨C,hC,?_⟩
  intro p hp x hm hl hQ j hj
  have hpR : (1:ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hpow : 1 ≤ (p:ℝ)^(N+1) := one_le_pow₀ hpR
  let f : CutoffInputParameter r→ℝ := fun y=>(1-y.2.1)/2
  let b : CutoffInputParameter r→ℝ := fun y=>endpointBaseIntegral Ξ y.2.2.2
  let l : CutoffInputParameter r→ℝ := fun y=>y.2.2.1
  let w : CutoffInputParameter r→ℝ := fun y=>endpointPowerIntegral p y.2.2.2
  let g : CutoffInputParameter r→ℝ := fun y=>b y+l y*w y
  have hf : ContDiff ℝ ∞ f := by dsimp only [f];fun_prop
  have hb : ContDiff ℝ ∞ b := (contDiff_endpointBaseIntegral Ξ).comp (by fun_prop)
  have hlc : ContDiff ℝ ∞ l := by dsimp only [l];fun_prop
  have hw : ContDiff ℝ ∞ w := (contDiff_endpointPowerIntegral p).comp (by fun_prop)
  have hg : ContDiff ℝ ∞ g := hb.add (hlc.mul hw)
  have hfB (i:ℕ) : ‖iteratedFDeriv ℝ i f x‖ ≤ 1 := by
    have h := norm_iteratedFDeriv_affine_contraction (fullMassProjection (r:=r))
      norm_fullMassProjection_le (1/2) (-1/2)
      (x:=x) (B:=1) (by change ‖x.2.1‖ ≤ 1;rw [Real.norm_of_nonneg hm.1];exact hm.2) i
    have he : f=(fun u=>1/2+(-1/2)*fullMassProjection u) := by
      funext u;dsimp [f,fullMassProjection];ring
    rw [he]
    norm_num at h ⊢
    exact h
  have hbB (i:ℕ) (hi:i ≤ N) : ‖iteratedFDeriv ℝ i b x‖ ≤ B :=
    (norm_iteratedFDeriv_comp_contraction fullQProjection norm_fullQProjection_le
      _ (contDiff_endpointBaseIntegral Ξ) i x).trans
      (by rw [←norm_iteratedFDeriv_eq_norm_iteratedDeriv];exact hBb _ hQ i hi)
  have hlB (i:ℕ) : ‖iteratedFDeriv ℝ i l x‖ ≤ D := by
    have h := norm_iteratedFDeriv_affine_contraction (fullLambdaProjection (r:=r))
      norm_fullLambdaProjection_le 0 1
      (x:=x) (B:=L) (by change ‖x.2.2.1‖ ≤ L;rw [Real.norm_of_nonneg hl.1];exact hl.2) i
    simpa [l,D,fullLambdaProjection,endpointPairProjection] using h
  have hwB (i:ℕ) (hi:i ≤ N) : ‖iteratedFDeriv ℝ i w x‖ ≤ 3*(p:ℝ)^(N+1) :=
    (norm_iteratedFDeriv_endpointPowerIntegral_unit fullQProjection norm_fullQProjection_le
      p (by omega) hQ i).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hpR (by omega)) (by norm_num))
  have hgB (i:ℕ) (hi:i ≤ N) : ‖iteratedFDeriv ℝ i g x‖ ≤
      (B+(2:ℝ)^N*D*3)*(p:ℝ)^(N+1) := by
    have H := norm_iteratedFDeriv_mul_bound_at hlc.contDiffAt hw.contDiffAt i D
      (3*(p:ℝ)^(N+1)) (zero_le_one.trans hD) (by positivity)
      (fun j _=>hlB j) (fun j hj=>hwB j (hj.trans hi))
    change ‖iteratedFDeriv ℝ i (fun y=>b y+l y*w y) x‖ ≤ _
    rw [fun_iteratedFDeriv_add_apply (hb.of_le (by simp)).contDiffAt
      ((hlc.mul hw).of_le (by simp)).contDiffAt]
    apply (norm_add_le _ _).trans
    have hpB := mul_le_mul_of_nonneg_left hpow (zero_le_one.trans hB)
    have h2 : (2:ℝ)^i ≤ (2:ℝ)^N := pow_le_pow_right₀ (by norm_num) hi
    have hprod := mul_le_mul_of_nonneg_right h2 (by positivity : 0 ≤ D*(3*(p:ℝ)^(N+1)))
    have H' := H.trans (by simpa only [mul_assoc] using hprod)
    have bb := hbB i hi
    nlinarith
  have H := norm_iteratedFDeriv_mul_bound_at hf.contDiffAt hg.contDiffAt j 1
    ((B+(2:ℝ)^N*D*3)*(p:ℝ)^(N+1)) zero_le_one (by positivity)
    (fun i _=>hfB i) (fun i hi=>hgB i (hi.trans hj))
  change ‖iteratedFDeriv ℝ j (fun y=>f y*g y) x‖ ≤ _
  apply H.trans
  have h2 : (2:ℝ)^j ≤ (2:ℝ)^N := pow_le_pow_right₀ (by norm_num) hj
  have HH := mul_le_mul_of_nonneg_right h2
    (show 0 ≤ (B+(2:ℝ)^N*D*3)*(p:ℝ)^(N+1) by positivity)
  simpa only [mul_one,C,mul_assoc] using HH

end GeneralDepthPaper
