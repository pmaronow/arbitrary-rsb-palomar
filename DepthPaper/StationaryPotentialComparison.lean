module

public import DepthPaper.StationaryJetComparison
public import DepthPaper.PartialGradientJets

@[expose] public section


/-! Linear C² stability of actual stationary branches from C³ scalar errors
and a fourth-jet bound for the fixed comparison potential. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
variable {Θ E : Type*}
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 64

theorem norm_iteratedFDeriv_one_sub_eq {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f g : X→Y) (x y : X) :
    ‖iteratedFDeriv ℝ 1 f x-iteratedFDeriv ℝ 1 g y‖ = ‖fderiv ℝ f x-fderiv ℝ g y‖ := by
  let T := continuousMultilinearCurryFin1 ℝ X Y
  have hf : T (iteratedFDeriv ℝ 1 f x)=fderiv ℝ f x := by ext v;simp [T]
  have hg : T (iteratedFDeriv ℝ 1 g y)=fderiv ℝ g y := by ext v;simp [T]
  rw [←T.norm_map, map_sub, hf,hg]

theorem norm_iteratedFDeriv_two_sub_eq {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f g : X→Y) (x y : X) :
    ‖iteratedFDeriv ℝ 2 f x-iteratedFDeriv ℝ 2 g y‖ =
      ‖fderiv ℝ (fderiv ℝ f) x-fderiv ℝ (fderiv ℝ g) y‖ := by
  let T := (continuousMultilinearCurryRightEquiv' ℝ 1 X Y).symm
  rw [iteratedFDeriv_succ_eq_comp_right (n:=1),iteratedFDeriv_succ_eq_comp_right (n:=1)]
  simp only [Function.comp_apply]
  rw [←T.map_sub,T.norm_map]
  exact norm_iteratedFDeriv_one_sub_eq _ _ x y

/-- This theorem compares actual branches and actual scalar jets. Both local
stationarity equations are true equalities; no formula for branch derivatives
or desired convergence estimate is supplied as an input. -/
theorem stationary_potential_C2_comparison
    (f g : Θ×E→ℝ) (s : Set E) (hs : Convex ℝ s)
    {q r : Θ→E} {θ : Θ} {κ D ε : ℝ}
    (hq : ContDiffAt ℝ ∞ q θ) (hr : ContDiffAt ℝ ∞ r θ)
    (hqs : q θ∈s) (hrs : r θ∈s)
    (hf : ∀z∈s,ContDiffAt ℝ ∞ f (θ,z))
    (hg : ∀z∈s,ContDiffAt ℝ ∞ g (θ,z))
    (heq : ∀ᶠu in 𝓝 θ,partialGradient f u (q u)=0)
    (her : ∀ᶠu in 𝓝 θ,partialGradient g u (r u)=0)
    (hκ : 0<κ) (hD : 0≤D) (hε : ε∈Icc (0:ℝ) 1)
    (hBF : ∀z∈s,∀v:E,κ*‖v‖^2 ≤ fderiv ℝ (partialGradient f θ) z v v)
    (hBG : ∀z∈s,∀v:E,κ*‖v‖^2 ≤ fderiv ℝ (partialGradient g θ) z v v)
    (hb : ∀z∈s,∀j:ℕ,2 ≤ j→j ≤ 4→‖iteratedFDeriv ℝ j g (θ,z)‖ ≤ D)
    (he : ∀z∈s,∀j:ℕ,1 ≤ j→j ≤ 3→‖iteratedFDeriv ℝ j (fun u=>f u-g u) (θ,z)‖ ≤ ε) :
    ‖q θ-r θ‖ ≤ ε/κ ∧
    ‖iteratedFDeriv ℝ 1 q θ-iteratedFDeriv ℝ 1 r θ‖ ≤
      ε*(1+D/κ)*max 1 ((D+1)/κ)/κ ∧
    ‖iteratedFDeriv ℝ 2 q θ-iteratedFDeriv ℝ 2 r θ‖ ≤
      ε*(1+D/κ)*(max 1 ((D+1)/κ))^2/κ*(1+3*(D+1)/κ) := by
  let F := fun p:Θ×E=>partialGradient f p.1 p.2
  let G := fun p:Θ×E=>partialGradient g p.1 p.2
  have hF : ContDiffAt ℝ ∞ F (stationaryGraph q θ) := contDiffAt_partialGradient f (hf _ hqs)
  have hG : ContDiffAt ℝ ∞ G (stationaryGraph r θ) := contDiffAt_partialGradient g (hg _ hrs)
  have hff : ∀z∈s,ContDiffAt ℝ ∞ (fun w=>f (θ,w)) z := fun z hz=>
    (hf z hz).comp z (contDiffAt_const.prodMk contDiffAt_id)
  have hnorm : ‖q θ-r θ‖ ≤ ε/κ := by
    have her' : (fun u=>partialGradient g u (r u))=ᶠ[𝓝 θ] (fun _=>0) := her
    have heq' : (fun u=>partialGradient f u (q u))=ᶠ[𝓝 θ] (fun _=>0) := heq
    have hrzero := her'.eq_of_nhds
    have hfzero := heq'.eq_of_nhds
    have hsmall := (norm_iteratedFDeriv_partialGradient_sub_le f g (hf _ hrs) (hg _ hrs) 0).trans
      (he (r θ) hrs 1 le_rfl (by omega))
    have hsmall' : ‖partialGradient f θ (r θ)‖ ≤ ε := by
      have hid : iteratedFDeriv ℝ 0 F (θ,r θ)-iteratedFDeriv ℝ 0 G (θ,r θ)=
          iteratedFDeriv ℝ 0 (fun _ : Θ×E=>partialGradient f θ (r θ)) (θ,r θ) := by
        ext v
        simp only [sub_apply,iteratedFDeriv_zero_apply,F,G,hrzero,sub_zero]
      rw [hid,norm_iteratedFDeriv_zero] at hsmall
      exact hsmall
    exact (coercive_stationary_displacement (fun z=>f (θ,z)) hs hff hκ hBF hrs hqs hfzero).trans
      (div_le_div_of_nonneg_right hsmall' hκ.le)
  have hBF' : ∀v:E,κ*‖v‖^2 ≤ fderiv ℝ F (stationaryGraph q θ) (0,v) v := by
    intro v
    have hh := hBF (q θ) hqs v
    rw [←partialGradient_partial_hessian f (hf _ hqs)] at hh
    exact hh
  have hBG' : ∀v:E,κ*‖v‖^2 ≤ fderiv ℝ G (stationaryGraph r θ) (0,v) v := by
    intro v
    have hh := hBG (r θ) hrs v
    rw [←partialGradient_partial_hessian g (hg _ hrs)] at hh
    exact hh
  have hF2 : ‖iteratedFDeriv ℝ 2 f (θ,q θ)‖ ≤ D+1 := by
    have hsub : ‖iteratedFDeriv ℝ 2 f (θ,q θ)-iteratedFDeriv ℝ 2 g (θ,q θ)‖ ≤ ε := by
      rw [←fun_iteratedFDeriv_sub_apply ((hf _ hqs).of_le (by simp)) ((hg _ hqs).of_le (by simp))]
      exact he _ hqs 2 (by omega) (by omega)
    have hadd := norm_add_le (iteratedFDeriv ℝ 2 f (θ,q θ)-iteratedFDeriv ℝ 2 g (θ,q θ))
      (iteratedFDeriv ℝ 2 g (θ,q θ))
    rw [sub_add_cancel] at hadd
    exact hadd.trans ((add_le_add hsub (hb _ hqs 2 (by omega) (by omega))).trans (by linarith [hε.2]))
  have hF1 : ‖fderiv ℝ F (stationaryGraph q θ)‖ ≤ D+1 := by
    simpa only [norm_iteratedFDeriv_one,F,G,stationaryGraph] using
      (norm_iteratedFDeriv_partialGradient_le f (hf _ hqs) 1).trans hF2
  have hG1 : ‖fderiv ℝ G (stationaryGraph r θ)‖ ≤ D+1 := by
    have hh := (norm_iteratedFDeriv_partialGradient_le g (hg _ hrs) 1).trans
      (hb _ hrs 2 (by omega) (by omega))
    exact (by simpa only [norm_iteratedFDeriv_one,F,G,stationaryGraph] using hh : ‖fderiv ℝ G (stationaryGraph r θ)‖ ≤ D).trans (by linarith)
  have hG2 : ‖fderiv ℝ (fderiv ℝ G) (stationaryGraph r θ)‖ ≤ D+1 := by
    have hh := (norm_iteratedFDeriv_partialGradient_le g (hg _ hrs) 2).trans
      (hb _ hrs 3 (by omega) (by omega))
    have hid : ‖fderiv ℝ (fderiv ℝ G) (stationaryGraph r θ)‖ = ‖iteratedFDeriv ℝ 2 G (stationaryGraph r θ)‖ := by
      rw [←norm_iteratedFDeriv_fderiv (n:=1),norm_iteratedFDeriv_one]
    rw [hid]
    exact hh.trans (by linarith)
  let η := ε*(1+D/κ)
  have hη : 0≤η := by
    dsimp [η]
    exact mul_nonneg hε.1 (by positivity)
  have herrors (j:ℕ) (hj:1 ≤ j) (hj2:j ≤ 2) :
      ‖iteratedFDeriv ℝ j F (stationaryGraph q θ)-iteratedFDeriv ℝ j G (stationaryGraph r θ)‖ ≤ η := by
    have hh := partialGradient_jet_graph_error f g hs θ j hf hg
      (fun z hz=>hb z hz (j+2) (by omega) (by omega))
      (fun z hz=>he z hz (j+1) (by omega) (by omega)) hrs hqs
    apply hh.trans
    dsimp only [η]
    have hmul := mul_le_mul_of_nonneg_left hnorm hD
    have hid : ε*(1+D/κ)=ε+D*(ε/κ) := by ring
    rw [hid]
    exact add_le_add_right hmul ε
  have herr1 : ‖fderiv ℝ F (stationaryGraph q θ)-fderiv ℝ G (stationaryGraph r θ)‖ ≤ η := by
    simpa only [norm_iteratedFDeriv_one_sub_eq] using herrors 1 le_rfl (by omega)
  have herr2 : ‖fderiv ℝ (fderiv ℝ F) (stationaryGraph q θ)-
      fderiv ℝ (fderiv ℝ G) (stationaryGraph r θ)‖ ≤ η := by
    simpa only [norm_iteratedFDeriv_two_sub_eq] using herrors 2 (by omega) le_rfl
  have hfirst := stationary_first_comparison hF hG hq hr heq her hκ
    (show 0≤D+1 by linarith) hη hBF' hBG' hG1 herr1
  have hsecond := stationary_second_comparison hF hG hq hr heq her hκ
    (show 0≤D+1 by linarith) hη hBF' hBG' hF1 hG1 hG2 herr1 herr2
  exact ⟨hnorm,by simpa only [norm_iteratedFDeriv_one_sub_eq,η] using hfirst,
    by simpa only [norm_iteratedFDeriv_two_sub_eq,η] using hsecond⟩

end DepthPaper
