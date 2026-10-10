module

public import GeneralDepthPaper.ConvexRecursionBounds

@[expose] public section


/-! Quantitative stability of genuine finite-order compositions on a
convex Banach-space input set. The hypotheses bound actual input jets and
their difference; no composition-difference conclusion is assumed. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
namespace GeneralDepthPaper
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 64
universe u
variable {E F G:Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem eventually_differentiableAt_of_contDiffAt
    {f:E→F} {x:E} (hf:ContDiffAt ℝ ∞ f x) :
    ∀ᶠy in 𝓝 x,DifferentiableAt ℝ f y := by
  have he:∀ᶠy in 𝓝 x,ContDiffAt ℝ 1 f y :=
    (hf.of_le (show (1:ℕ∞ω)≤∞ by simp)).eventually (by simp)
  exact he.mono (fun _ hy=>hy.differentiableAt (by norm_num))

theorem eventually_fderiv_sub_formula {f g:E→F} {x:E}
    (hf:ContDiffAt ℝ ∞ f x) (hg:ContDiffAt ℝ ∞ g x) :
    (fun y=>fderiv ℝ (fun z=>f z-g z) y)=ᶠ[𝓝 x]
      (fun y=>fderiv ℝ f y-fderiv ℝ g y) := by
  filter_upwards [eventually_differentiableAt_of_contDiffAt hf,
    eventually_differentiableAt_of_contDiffAt hg] with y hyf hyg
  exact fderiv_sub hyf hyg

theorem norm_iteratedFDeriv_fderiv_difference {f g:E→F} {x:E}
    (hf:ContDiffAt ℝ ∞ f x) (hg:ContDiffAt ℝ ∞ g x) (n:ℕ) :
    ‖iteratedFDeriv ℝ n (fun y=>fderiv ℝ f y-fderiv ℝ g y) x‖=
      ‖iteratedFDeriv ℝ (n+1) (fun y=>f y-g y) x‖ := by
  rw [←((eventually_fderiv_sub_formula hf hg).iteratedFDeriv (𝕜:=ℝ) n).eq_of_nhds,
    norm_iteratedFDeriv_fderiv]

theorem eventually_fderiv_composition_difference {H:F→G} {f g:E→F} {x:E}
    (hF:ContDiffAt ℝ ∞ H (f x)) (hG:ContDiffAt ℝ ∞ H (g x))
    (hf:ContDiffAt ℝ ∞ f x) (hg:ContDiffAt ℝ ∞ g x) :
    (fun y=>fderiv ℝ (fun z=>H (f z)-H (g z)) y)=ᶠ[𝓝 x]
      (fun y=>(fderiv ℝ H (f y)-fderiv ℝ H (g y)).comp (fderiv ℝ f y)+
        (fderiv ℝ H (g y)).comp (fderiv ℝ f y-fderiv ℝ g y)) := by
  have eF:=hf.continuousAt.eventually (eventually_differentiableAt_of_contDiffAt hF)
  have eG:=hg.continuousAt.eventually (eventually_differentiableAt_of_contDiffAt hG)
  filter_upwards [eF,eG,eventually_differentiableAt_of_contDiffAt hf,
    eventually_differentiableAt_of_contDiffAt hg] with y hyF hyG hyf hyg
  change fderiv ℝ ((H ∘ f)-(H ∘ g)) y=_
  rw [fderiv_sub (hyF.comp y hyf) (hyG.comp y hyg),
    fderiv_comp y hyF hyf,fderiv_comp y hyG hyg]
  ext v
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply,map_sub]
  abel

theorem norm_iteratedFDeriv_bilinear_uniform_bound
    {J:Type u} [NormedAddCommGroup J] [NormedSpace ℝ J]
    (B:F→L[ℝ] G→L[ℝ] J) {f:E→F} {g:E→G} {x:E}
    (hf:ContDiffAt ℝ ∞ f x) (hg:ContDiffAt ℝ ∞ g x)
    (n:ℕ) {A C:ℝ} (hA:0≤A) (hC:0≤C)
    (ha:∀i,i≤n→‖iteratedFDeriv ℝ i f x‖≤A)
    (hc:∀i,i≤n→‖iteratedFDeriv ℝ i g x‖≤C) :
    ‖iteratedFDeriv ℝ n (fun y=>B (f y) (g y)) x‖≤‖B‖*(2:ℝ)^n*A*C := by
  apply (norm_iteratedFDeriv_bilinear_le_at B hf hg n).trans
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

theorem norm_iteratedFDeriv_composition_uniform_low_order
    {H:F→G} {g:E→F} {x:E} (hH:ContDiffAt ℝ ∞ H (g x))
    (hg:ContDiffAt ℝ ∞ g x) (n:ℕ) {A D:ℝ} (hA:0≤A) (hD:1≤D)
    (ha:∀i,i≤n→‖iteratedFDeriv ℝ i H (g x)‖≤A)
    (hd:∀i,i≤n→‖iteratedFDeriv ℝ i g x‖≤D) :
    ∀i,i≤n→‖iteratedFDeriv ℝ i (H∘g) x‖≤(n.factorial:ℝ)*A*D^n := by
  intro i hi
  have hh:=norm_iteratedFDeriv_comp_le_at hH hg i A D
    (fun j hj=>ha j (hj.trans hi))
    (fun j hj hji=>(hd j (hji.trans hi)).trans (le_self_pow₀ hD (by omega)))
  exact hh.trans (mul_le_mul
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hi) hA)
    (pow_le_pow_right₀ hD hi) (by positivity) (by positivity))

theorem composition_difference_bounds_up_to (n:ℕ)
    {H:F→G} {s:Set F} (hH:BoundedSmoothOn H s) (hs:Convex ℝ s)
    (D:ℝ) (hD:1≤D) :
    ∃C:ℝ,0≤C ∧ ∀f g:E→F,∀x:E,∀ε:ℝ,0≤ε→
      ContDiffAt ℝ ∞ f x→ContDiffAt ℝ ∞ g x→f x∈s→g x∈s→
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
    · exact (hprev f g x ε hε hf hg hfx hgx
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
      have hU:ContDiffAt ℝ ∞ U x:=(hHF.comp x hf).sub (hHG.comp x hg)
      have hV:ContDiffAt ℝ ∞ V x:=hf.fderiv_right (m:=∞) (by simp)
      have hP:ContDiffAt ℝ ∞ P x:=hHG.comp x hg
      have hQ:ContDiffAt ℝ ∞ Q x:=
        (hf.fderiv_right (m:=∞) (by simp)).sub (hg.fderiv_right (m:=∞) (by simp))
      have hUb:∀i,i≤n→‖iteratedFDeriv ℝ i U x‖≤Cdiff*ε :=
        hdiff f g x ε hε hf hg hfx hgx
          (fun i hi=>hfj i (by omega)) (fun i hi=>hgj i (by omega))
          (fun i hi=>hdj i (by omega))
      have hVb:∀i,i≤n→‖iteratedFDeriv ℝ i V x‖≤D := by
        intro i hi
        rw [norm_iteratedFDeriv_fderiv]
        exact hfj (i+1) (by omega)
      have hPb:∀i,i≤n→‖iteratedFDeriv ℝ i P x‖≤B :=
        norm_iteratedFDeriv_composition_uniform_low_order hHG hg n hA hD
          (fun i hi=>hAbound i hi (g x) hgx) (fun i hi=>hgj i (by omega))
      have hQb:∀i,i≤n→‖iteratedFDeriv ℝ i Q x‖≤ε := by
        intro i hi
        rw [norm_iteratedFDeriv_fderiv_difference hf hg]
        exact hdj (i+1) (by omega)
      have hUV:=norm_iteratedFDeriv_bilinear_uniform_bound L hU hV n
        (mul_nonneg hCdiff hε) (zero_le_one.trans hD) hUb hVb
      have hPQ:=norm_iteratedFDeriv_bilinear_uniform_bound L hP hQ n hB hε hPb hQb
      have hsmooth1:ContDiffAt ℝ ∞ (fun y=>L (U y) (V y)) x:=
        L.isBoundedBilinearMap.contDiff.contDiffAt.comp₂ hU hV
      have hsmooth2:ContDiffAt ℝ ∞ (fun y=>L (P y) (Q y)) x:=
        L.isBoundedBilinearMap.contDiff.contDiffAt.comp₂ hP hQ
      have he:=eventually_fderiv_composition_difference (hH.smooth (f x) hfx)
        (hH.smooth (g x) hgx) hf hg
      have heq:‖iteratedFDeriv ℝ (n+1) (fun y=>H (f y)-H (g y)) x‖=
          ‖iteratedFDeriv ℝ n (fun y=>L (U y) (V y)+L (P y) (Q y)) x‖ := by
        rw [←norm_iteratedFDeriv_fderiv]
        exact congrArg norm ((he.iteratedFDeriv (𝕜:=ℝ) n).eq_of_nhds)
      rw [heq,fun_iteratedFDeriv_add_apply (hsmooth1.of_le (by simp)) (hsmooth2.of_le (by simp))]
      have hsum:‖iteratedFDeriv ℝ n (fun y=>L (U y) (V y)) x‖+
          ‖iteratedFDeriv ℝ n (fun y=>L (P y) (Q y)) x‖≤K*ε := by
        convert add_le_add hUV hPQ using 1 <;> dsimp only [K] <;> ring
      exact (norm_add_le _ _).trans (hsum.trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hε))

end GeneralDepthPaper
