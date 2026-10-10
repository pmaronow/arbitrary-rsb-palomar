module

public import DepthPaper.CompositionDifferenceBounds

@[expose] public section


/-! Local versions of quantitative derivative inequalities. This avoids
requiring a positive-variance kernel to be smooth at nonpositive variance. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
namespace RevisedFiniteCalculus
universe u
variable {E F G H : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
set_option maxSynthPendingDepth 64

theorem revised_norm_iteratedFDeriv_bilinear_le_at (B : F→L[ℝ] G→L[ℝ] H)
    {f : E→F} {g : E→G} {x : E} (n : ℕ) (hf : ContDiffAt ℝ n f x)
    (hg : ContDiffAt ℝ n g x) :
    ‖iteratedFDeriv ℝ n (fun y=>B (f y) (g y)) x‖ ≤
      ‖B‖*∑i∈Finset.range (n+1),(n.choose i:ℝ)*
        ‖iteratedFDeriv ℝ i f x‖*‖iteratedFDeriv ℝ (n-i) g x‖ := by
  obtain ⟨u,hu,hxu,hfu⟩ := (hf.contDiffWithinAt (s:=univ)).contDiffOn' (m:=(n:ℕ∞ω)) le_rfl (by simp)
  obtain ⟨v,hv,hxv,hgv⟩ := (hg.contDiffWithinAt (s:=univ)).contDiffOn' (m:=(n:ℕ∞ω)) le_rfl (by simp)
  have hfu' : ContDiffOn ℝ n f u := by simpa using hfu
  have hgv' : ContDiffOn ℝ n g v := by simpa using hgv
  have hs : IsOpen (u∩v) := hu.inter hv
  have hx : x∈u∩v := ⟨hxu,hxv⟩
  have h := B.norm_iteratedFDerivWithin_le_of_bilinear
    (hfu'.mono inter_subset_left) (hgv'.mono inter_subset_right) hs.uniqueDiffOn hx le_rfl
  have heq (j:ℕ) : iteratedFDerivWithin ℝ j f (u∩v) x=iteratedFDeriv ℝ j f x :=
    iteratedFDerivWithin_of_isOpen j hs hx
  have geq (j:ℕ) : iteratedFDerivWithin ℝ j g (u∩v) x=iteratedFDeriv ℝ j g x :=
    iteratedFDerivWithin_of_isOpen j hs hx
  have beq : iteratedFDerivWithin ℝ n (fun y=>B (f y) (g y)) (u∩v) x=
      iteratedFDeriv ℝ n (fun y=>B (f y) (g y)) x :=
    iteratedFDerivWithin_eq_iteratedFDeriv hs.uniqueDiffOn
      (B.isBoundedBilinearMap.contDiff.contDiffAt.comp₂ hf hg) hx
  simpa only [heq,geq,beq] using h

theorem revised_norm_iteratedFDeriv_comp_le_at {g : F→G} {f : E→F} {x : E}
    (n : ℕ) (hg : ContDiffAt ℝ n g (f x)) (hf : ContDiffAt ℝ n f x) (C D : ℝ)
    (hC : ∀ i : ℕ, i ≤ n → ‖iteratedFDeriv ℝ i g (f x)‖≤C)
    (hD : ∀ i : ℕ, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖≤D^i) :
    ‖iteratedFDeriv ℝ n (g∘f) x‖≤(n.factorial:ℝ)*C*D^n := by
  obtain ⟨u,hu,hxu,hfu⟩ := (hf.contDiffWithinAt (s:=univ)).contDiffOn' (m:=(n:ℕ∞ω)) le_rfl (by simp)
  obtain ⟨v,hv,hxv,hgv⟩ := (hg.contDiffWithinAt (s:=univ)).contDiffOn' (m:=(n:ℕ∞ω)) le_rfl (by simp)
  have hfu' : ContDiffOn ℝ n f u := by simpa using hfu
  have hgv' : ContDiffOn ℝ n g v := by simpa using hgv
  have hpre : f ⁻¹' v∩u∈𝓝 x :=
    inter_mem (hf.continuousAt.preimage_mem_nhds (hv.mem_nhds hxv)) (hu.mem_nhds hxu)
  obtain ⟨w,hwsub,hw,hxw⟩ := mem_nhds_iff.mp hpre
  have hfW : ContDiffOn ℝ n f w := hfu'.mono (hwsub.trans inter_subset_right)
  have hmaps : MapsTo f w v := fun y hy=> (hwsub hy).1
  have h := norm_iteratedFDerivWithin_comp_le hgv' hfW le_rfl
    hv.uniqueDiffOn hw.uniqueDiffOn hmaps hxw (C:=C) (D:=D)
  have feq (j:ℕ) : iteratedFDerivWithin ℝ j f w x=iteratedFDeriv ℝ j f x :=
    iteratedFDerivWithin_of_isOpen j hw hxw
  have geq (j:ℕ) : iteratedFDerivWithin ℝ j g v (f x)=iteratedFDeriv ℝ j g (f x) :=
    iteratedFDerivWithin_of_isOpen j hv hxv
  have ceq : iteratedFDerivWithin ℝ n (g∘f) w x=iteratedFDeriv ℝ n (g∘f) x :=
    iteratedFDerivWithin_eq_iteratedFDeriv hw.uniqueDiffOn
      (hg.comp x hf) hxw
  simpa only [feq,geq,ceq] using h (by simpa only [geq] using hC)
    (by simpa only [feq] using hD)

theorem revised_eventually_differentiableAt_of_contDiffAt
    {f:E→F} {x:E} (hf:ContDiffAt ℝ 1 f x) :
    ∀ᶠy in 𝓝 x,DifferentiableAt ℝ f y := by
  have he:∀ᶠy in 𝓝 x,ContDiffAt ℝ 1 f y :=
    hf.eventually (by simp)
  exact he.mono (fun _ hy=>hy.differentiableAt (by norm_num))

theorem revised_eventually_fderiv_sub_formula {f g:E→F} {x:E}
    (n:ℕ) (hf:ContDiffAt ℝ (n+1) f x) (hg:ContDiffAt ℝ (n+1) g x) :
    (fun y=>fderiv ℝ (fun z=>f z-g z) y)=ᶠ[𝓝 x]
      (fun y=>fderiv ℝ f y-fderiv ℝ g y) := by
  filter_upwards [revised_eventually_differentiableAt_of_contDiffAt (hf.of_le (by norm_cast; omega)),
    revised_eventually_differentiableAt_of_contDiffAt (hg.of_le (by norm_cast; omega))] with y hyf hyg
  exact fderiv_sub hyf hyg

theorem revised_norm_iteratedFDeriv_fderiv_difference {f g:E→F} {x:E}
    (n:ℕ) (hf:ContDiffAt ℝ (n+1) f x) (hg:ContDiffAt ℝ (n+1) g x) :
    ‖iteratedFDeriv ℝ n (fun y=>fderiv ℝ f y-fderiv ℝ g y) x‖=
      ‖iteratedFDeriv ℝ (n+1) (fun y=>f y-g y) x‖ := by
  rw [←((revised_eventually_fderiv_sub_formula n hf hg).iteratedFDeriv (𝕜:=ℝ) n).eq_of_nhds,
    norm_iteratedFDeriv_fderiv]

theorem revised_eventually_fderiv_composition_difference {H:F→G} {f g:E→F} {x:E}
    (hF:ContDiffAt ℝ ∞ H (f x)) (hG:ContDiffAt ℝ ∞ H (g x))
    (n:ℕ) (hf:ContDiffAt ℝ (n+1) f x) (hg:ContDiffAt ℝ (n+1) g x) :
    (fun y=>fderiv ℝ (fun z=>H (f z)-H (g z)) y)=ᶠ[𝓝 x]
      (fun y=>(fderiv ℝ H (f y)-fderiv ℝ H (g y)).comp (fderiv ℝ f y)+
        (fderiv ℝ H (g y)).comp (fderiv ℝ f y-fderiv ℝ g y)) := by
  have eF:=hf.continuousAt.eventually (revised_eventually_differentiableAt_of_contDiffAt (hF.of_le (by simp)))
  have eG:=hg.continuousAt.eventually (revised_eventually_differentiableAt_of_contDiffAt (hG.of_le (by simp)))
  filter_upwards [eF,eG,revised_eventually_differentiableAt_of_contDiffAt (hf.of_le (by norm_cast; omega)),
    revised_eventually_differentiableAt_of_contDiffAt (hg.of_le (by norm_cast; omega))] with y hyF hyG hyf hyg
  change fderiv ℝ ((H ∘ f)-(H ∘ g)) y=_
  rw [fderiv_sub (hyF.comp y hyf) (hyG.comp y hyg),
    fderiv_comp y hyF hyf,fderiv_comp y hyG hyg]
  ext v
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply,map_sub]
  abel

theorem revised_norm_iteratedFDeriv_bilinear_uniform_bound
    {J:Type u} [NormedAddCommGroup J] [NormedSpace ℝ J]
    (B:F→L[ℝ] G→L[ℝ] J) {f:E→F} {g:E→G} {x:E}
    (n:ℕ) (hf:ContDiffAt ℝ n f x) (hg:ContDiffAt ℝ n g x) {A C:ℝ} (hA:0≤A) (hC:0≤C)
    (ha:∀i,i≤n→‖iteratedFDeriv ℝ i f x‖≤A)
    (hc:∀i,i≤n→‖iteratedFDeriv ℝ i g x‖≤C) :
    ‖iteratedFDeriv ℝ n (fun y=>B (f y) (g y)) x‖≤‖B‖*(2:ℝ)^n*A*C := by
  apply (revised_norm_iteratedFDeriv_bilinear_le_at B n hf hg).trans
  have hsum:(∑i∈Finset.range (n+1),(n.choose i:ℝ)*A*C)=(2:ℝ)^n*A*C := by
    rw [←Finset.sum_mul,←Finset.sum_mul,←Nat.cast_sum,Nat.sum_range_choose,
      Nat.cast_pow,Nat.cast_ofNat]
  have hle:(∑i∈Finset.range (n+1),(n.choose i:ℝ)*
      ‖iteratedFDeriv ℝ i f x‖*‖iteratedFDeriv ℝ (n-i) g x‖)≤
        ∑i∈Finset.range (n+1),(n.choose i:ℝ)*A*C := by
    apply Finset.sum_le_sum
    intro i hi
    have hin:i≤n:=by have hh:=Finset.mem_range.mp hi;omega
    exact mul_le_mul (mul_le_mul_of_nonneg_left (ha i hin) (Nat.cast_nonneg _))
      (hc (n-i) (Nat.sub_le _ _)) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hA)
  have hm:=mul_le_mul_of_nonneg_left hle (norm_nonneg B)
  rw [hsum] at hm
  exact hm.trans_eq (by ring)

theorem revised_norm_iteratedFDeriv_composition_uniform_low_order
    {H:F→G} {g:E→F} {x:E} (hH:ContDiffAt ℝ ∞ H (g x))
    (n:ℕ) (hg:ContDiffAt ℝ n g x) {A D:ℝ} (hA:0≤A) (hD:1≤D)
    (ha:∀i,i≤n→‖iteratedFDeriv ℝ i H (g x)‖≤A)
    (hd:∀i,i≤n→‖iteratedFDeriv ℝ i g x‖≤D) :
    ∀i,i≤n→‖iteratedFDeriv ℝ i (H∘g) x‖≤(n.factorial:ℝ)*A*D^n := by
  intro i hi
  have hh:=revised_norm_iteratedFDeriv_comp_le_at i (hH.of_le (by simp))
    (hg.of_le (by exact_mod_cast hi)) A D
    (fun j hj=>ha j (hj.trans hi))
    (fun j hj hji=>(hd j (hji.trans hi)).trans (le_self_pow₀ hD (by omega)))
  exact hh.trans (mul_le_mul
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hi) hA)
    (pow_le_pow_right₀ hD hi) (by positivity) (by positivity))

theorem revised_composition_difference_bounds_up_to (n:ℕ)
    {H:F→G} {s:Set F} (hH:BoundedSmoothOn H s) (hs:Convex ℝ s)
    (D:ℝ) (hD:1≤D) :
    ∃C:ℝ,0≤C ∧ ∀f g:E→F,∀x:E,∀ε:ℝ,0≤ε→
      ContDiffAt ℝ n f x→ContDiffAt ℝ n g x→f x∈s→g x∈s→
      (∀i,i≤n→‖iteratedFDeriv ℝ i f x‖≤D)→
      (∀i,i≤n→‖iteratedFDeriv ℝ i g x‖≤D)→
      (∀i,i≤n→‖iteratedFDeriv ℝ i (fun y=>f y-g y) x‖≤ε)→
      ∀j,j≤n→‖iteratedFDeriv ℝ j (fun y=>H (f y)-H (g y)) x‖≤C*ε := by
  classical
  induction n generalizing G with
  | zero=>
    obtain ⟨C,hC,hb⟩:=hH.value_lipschitz hs
    refine ⟨C,hC,?_⟩
    intro f g x ε hε hf hg hfx hgx hfj hgj hdj j hj
    have hj0:j=0:=by omega
    subst j
    rw [norm_iteratedFDeriv_zero]
    have hh:=hb (g x) hgx (f x) hfx
    have hd:=hdj 0 le_rfl
    rw [norm_iteratedFDeriv_zero] at hd
    exact hh.trans (mul_le_mul_of_nonneg_left hd hC)
  | succ n ih=>
    obtain ⟨Cprev,hCprev,hprev⟩:=ih hH
    obtain ⟨Cdiff,hCdiff,hdiff⟩:=ih hH.fderiv
    choose c hc hb using hH.fderiv.bound
    let A:ℝ:=∑i∈Finset.range (n+1),c i
    have hA:0≤A:=Finset.sum_nonneg (fun i _=>hc i)
    have hAbound:∀i,i≤n→∀y∈s,‖iteratedFDeriv ℝ i (fderiv ℝ H) y‖≤A := by
      intro i hi y hy
      exact (hb i y hy).trans
        (Finset.single_le_sum (fun j _=>hc j) (Finset.mem_range.mpr (by omega)))
    let B:ℝ:=(n.factorial:ℝ)*A*D^n
    have hB:0≤B:=by dsimp only [B];positivity
    let L:=ContinuousLinearMap.compL ℝ E F G
    let K:ℝ:=‖L‖*(2:ℝ)^n*(Cdiff*D+B)
    have hK:0≤K:=by dsimp only [K];positivity
    refine ⟨max Cprev K,hCprev.trans (le_max_left _ _),?_⟩
    intro f g x ε hε hf hg hfx hgx hfj hgj hdj j hj
    by_cases hjn:j≤n
    · exact (hprev f g x ε hε (hf.of_le (by norm_cast; omega))
        (hg.of_le (by norm_cast; omega)) hfx hgx
        (fun i hi=>hfj i (by omega)) (fun i hi=>hgj i (by omega))
        (fun i hi=>hdj i (by omega)) j hjn).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hε)
    · have hjEq:j=n+1:=by omega
      subst j
      let U:E→F→L[ℝ] G:=fun y=>fderiv ℝ H (f y)-fderiv ℝ H (g y)
      let V:E→E→L[ℝ] F:=fderiv ℝ f
      let P:E→F→L[ℝ] G:=fun y=>fderiv ℝ H (g y)
      let Q:E→E→L[ℝ] F:=fun y=>fderiv ℝ f y-fderiv ℝ g y
      have hHF:ContDiffAt ℝ ∞ (fderiv ℝ H) (f x):=hH.fderiv.smooth (f x) hfx
      have hHG:ContDiffAt ℝ ∞ (fderiv ℝ H) (g x):=hH.fderiv.smooth (g x) hgx
      have hU:ContDiffAt ℝ n U x:=(hHF.of_le (by simp) |>.comp x (hf.of_le (by norm_cast; omega))).sub
          (hHG.of_le (by simp) |>.comp x (hg.of_le (by norm_cast; omega)))
      have hV:ContDiffAt ℝ n V x:=hf.fderiv_right (m:=n) (by simp)
      have hP:ContDiffAt ℝ n P x:=(hHG.of_le (by simp)).comp x (hg.of_le (by norm_cast; omega))
      have hQ:ContDiffAt ℝ n Q x:=
        (hf.fderiv_right (m:=n) (by simp)).sub (hg.fderiv_right (m:=n) (by simp))
      have hUb:∀i,i≤n→‖iteratedFDeriv ℝ i U x‖≤Cdiff*ε :=
        hdiff f g x ε hε (hf.of_le (by norm_cast; omega))
          (hg.of_le (by norm_cast; omega)) hfx hgx
          (fun i hi=>hfj i (by omega)) (fun i hi=>hgj i (by omega))
          (fun i hi=>hdj i (by omega))
      have hVb:∀i,i≤n→‖iteratedFDeriv ℝ i V x‖≤D := by
        intro i hi
        rw [norm_iteratedFDeriv_fderiv]
        exact hfj (i+1) (by omega)
      have hPb:∀i,i≤n→‖iteratedFDeriv ℝ i P x‖≤B :=
        revised_norm_iteratedFDeriv_composition_uniform_low_order hHG n
          (hg.of_le (by norm_cast; omega)) hA hD
          (fun i hi=>hAbound i hi (g x) hgx) (fun i hi=>hgj i (by omega))
      have hQb:∀i,i≤n→‖iteratedFDeriv ℝ i Q x‖≤ε := by
        intro i hi
        change ‖iteratedFDeriv ℝ i (fun y => fderiv ℝ f y-fderiv ℝ g y) x‖ ≤ ε
        rw [revised_norm_iteratedFDeriv_fderiv_difference i
          (hf.of_le (by norm_cast; omega)) (hg.of_le (by norm_cast; omega))]
        exact hdj (i+1) (by omega)
      have hUV:=revised_norm_iteratedFDeriv_bilinear_uniform_bound L n hU hV
        (mul_nonneg hCdiff hε) (zero_le_one.trans hD) hUb hVb
      have hPQ:=revised_norm_iteratedFDeriv_bilinear_uniform_bound L n hP hQ hB hε hPb hQb
      have hsmooth1:ContDiffAt ℝ n (fun y=>L (U y) (V y)) x:=
        L.isBoundedBilinearMap.contDiff.contDiffAt.comp₂ hU hV
      have hsmooth2:ContDiffAt ℝ n (fun y=>L (P y) (Q y)) x:=
        L.isBoundedBilinearMap.contDiff.contDiffAt.comp₂ hP hQ
      have he:=revised_eventually_fderiv_composition_difference (hH.smooth (f x) hfx)
        (hH.smooth (g x) hgx) n hf hg
      have heq:‖iteratedFDeriv ℝ (n+1) (fun y=>H (f y)-H (g y)) x‖=
          ‖iteratedFDeriv ℝ n (fun y=>L (U y) (V y)+L (P y) (Q y)) x‖ := by
        rw [←norm_iteratedFDeriv_fderiv]
        exact congrArg norm ((he.iteratedFDeriv (𝕜:=ℝ) n).eq_of_nhds)
      rw [heq,fun_iteratedFDeriv_add_apply hsmooth1 hsmooth2]
      have hsum:‖iteratedFDeriv ℝ n (fun y=>L (U y) (V y)) x‖+
          ‖iteratedFDeriv ℝ n (fun y=>L (P y) (Q y)) x‖≤K*ε := by
        convert add_le_add hUV hPQ using 1 <;> dsimp only [K] <;> ring
      exact (norm_add_le _ _).trans (hsum.trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hε))

end RevisedFiniteCalculus
end DepthPaper
