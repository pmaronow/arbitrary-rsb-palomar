module

public import GeneralDepthPaper.RevisedSectionFourEnvelopeComparison
public import GeneralDepthPaper.RevisedSectionFourEnvelopeIdentity

@[expose] public section

/-! Revised Proposition 4.5(ii): the actual optimized scalar objectives
converge in full C³, including all mixed coupling/mass derivatives. The
full envelope formula removes derivatives of the stationary coordinates,
so C² branch errors and C³ scalar errors suffice. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 64
namespace LimitingStandingData
variable {Ξ : AdmissibleCovariance} {r : ℕ} {seed : AtomicPoint r}

theorem revisedScalarObjective_fullDerivative_eventually (d : LimitingStandingData Ξ seed) :
    ∀ᶠp : ℕ in atTop,∀_heven : Even p,∀θ∈d.parameterWindow,
      HasFDerivAt (d.revisedScalarObjective p)
        (revisedParameterGradientProjection
          (fderiv ℝ (stationaryReducedObjective Ξ p d.cutoff d.stripRateLower d.stripRateUpper)
            (θ,d.stationaryBranch p θ))) θ := by
  obtain ⟨_,_,_,_,_,Hr⟩ := d.stationaryBranch_regular_error_eventually
  obtain ⟨_,_,_,_,_,Hs⟩ := d.stationaryBranch_eventually
  filter_upwards [Hr,Hs] with p hr hs heven θ hθ
  let f := stationaryReducedObjective Ξ (r:=r) p d.cutoff d.stripRateLower d.stripRateUpper
  have hreg := hr heven θ hθ
  have hsel := hs heven θ hθ
  have hfs : ContDiffAt ℝ ∞ f (θ,d.stationaryBranch p θ) :=
    hreg.2.1 _ (ball_subset_closedBall hsel.1)
  have hJp : DifferentiableAt ℝ (d.revisedScalarObjective p) θ :=
    (hfs.comp θ (contDiffAt_id.prodMk hreg.1)).differentiableAt (by simp)
  have he := revised_fderiv_stationary_graph (hfs.differentiableAt (by simp))
    (hreg.1.differentiableAt (by simp)) hsel.2.1
  have heJp : fderiv ℝ (d.revisedScalarObjective p) θ=
      revisedParameterGradientProjection
        (fderiv ℝ (stationaryReducedObjective Ξ p d.cutoff d.stripRateLower d.stripRateUpper)
          (θ,d.stationaryBranch p θ)) := he
  rw [←heJp]
  exact hJp.hasFDerivAt

theorem revisedScalarObjective_C3_exponential_error (d : LimitingStandingData Ξ seed) :
    ∃C : ℝ,0<C ∧ ∃A : ℕ,∃c : ℝ,0<c ∧
      ∀ᶠp : ℕ in atTop,∀_heven : Even p,∀θ∈d.parameterWindow,
        ContDiffAt ℝ ∞ (d.revisedScalarObjective p) θ ∧
        ∀j : ℕ,j≤3 → ‖iteratedFDeriv ℝ j
          (fun u=>d.revisedScalarObjective p u-revisedLimitingScalarObjective Ξ u) θ‖≤
            C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) := by
  obtain ⟨Cf,hCf,Af,cf,hcf,Hf⟩ := d.stationaryBranch_regular_error_eventually
  obtain ⟨Cz,hCz,Az,cz,hcz,Hz⟩ := d.stationaryBranch_C2_exponential_error
  obtain ⟨_,_,_,_,_,Hs⟩ := d.stationaryBranch_eventually
  obtain ⟨D0,hD0,HD0⟩ := bounded_smooth_finite_jet_bound d.limiting_graph_bounded_smooth 2
  let D : ℝ := D0+1
  have hD : 1≤D := by dsimp [D];linarith
  obtain ⟨Kg,hKg,HKg⟩ := revised_full_derivative_C2_comparison (E:=ℝ×ℝ)
    (stationaryLimitingObjective Ξ) d.stationaryInputWindow
    d.boundedSmoothOn_stationaryLimitingObjective d.stationaryInputWindow_convex D hD
  obtain ⟨Kv,hKv,HKv⟩ :=
    d.boundedSmoothOn_stationaryLimitingObjective.value_lipschitz d.stationaryInputWindow_convex
  obtain ⟨C,hC,A,c,hc,Hsum⟩ := three_degree_exp_envelope
    (C1:=(1+Kg)*Cf) (C2:=(1+Kv+Kg)*Cz) (C3:=0) (A1:=Af) (A2:=Az) (A3:=0)
    (by positivity) (by positivity) (by norm_num) hcf hcz (show (0:ℝ)<1 by norm_num)
  have Hsmall : ∀ᶠp : ℕ in atTop,Cz*(p:ℝ)^Az*Real.exp (-cz*(p:ℝ))≤1 :=
    (tendsto_nat_polynomial_exp Cz cz Az hcz).eventually
      (eventually_le_nhds (show (0:ℝ)<1 by norm_num))
  refine ⟨C,hC,A,c,hc,?_⟩
  filter_upwards [Hf,Hz,Hs,Hsmall,eventually_ge_atTop 1] with p hf hz hs hsmall hp1
  intro heven θ hθ
  let a : ℝ×ℝ→(ℝ×ℝ)×AtomicPoint r := fun u=>(u,d.stationaryBranch p u)
  let b : ℝ×ℝ→(ℝ×ℝ)×AtomicPoint r := fun u=>(u,d.branch u.2)
  let f := stationaryReducedObjective Ξ (r:=r) p d.cutoff d.stripRateLower d.stripRateUpper
  let g := stationaryLimitingObjective Ξ (r:=r)
  let ε : ℝ := Cf*(p:ℝ)^Af*Real.exp (-cf*(p:ℝ))
  let η : ℝ := Cz*(p:ℝ)^Az*Real.exp (-cz*(p:ℝ))
  have hε : 0≤ε := by dsimp [ε];positivity
  have hη : 0≤η := by dsimp [η];positivity
  have hreg := hf heven θ hθ
  have hsel := hs heven θ hθ
  have hq := hreg.1
  have hr : ContDiffAt ℝ ∞ (fun u : ℝ×ℝ=>d.branch u.2) θ :=
    d.limiting_branch_bounded_smooth.smooth θ hθ
  have ha : ContDiffAt ℝ ∞ a θ := contDiffAt_id.prodMk hq
  have hb : ContDiffAt ℝ ∞ b θ := contDiffAt_id.prodMk hr
  have hqs : d.stationaryBranch p θ∈closedBall seed d.radius := ball_subset_closedBall hsel.1
  have hrs : d.branch θ.2∈closedBall seed d.radius := by
    rw [mem_closedBall]
    linarith [d.branch_close θ.2 hθ.2,d.radius_pos]
  have hax : a θ∈d.stationaryInputWindow := ⟨hθ,hqs⟩
  have hbx : b θ∈d.stationaryInputWindow := ⟨hθ,hrs⟩
  have hgraph (i : ℕ) (hi : i≤2) :
      ‖iteratedFDeriv ℝ i (fun u=>a u-b u) θ‖≤η :=
    (norm_stationary_graph_difference_jet_le hq hr i).trans (hz heven θ hθ i hi)
  have hbj (i : ℕ) (hi : i≤2) : ‖iteratedFDeriv ℝ i b θ‖≤D :=
    (HD0 θ hθ i hi).trans (by dsimp [D];linarith)
  have haj (i : ℕ) (hi : i≤2) : ‖iteratedFDeriv ℝ i a θ‖≤D := by
    have hsub : ‖iteratedFDeriv ℝ i a θ-iteratedFDeriv ℝ i b θ‖≤η := by
      rw [←fun_iteratedFDeriv_sub_apply (ha.of_le (by simp)) (hb.of_le (by simp))]
      exact hgraph i hi
    have htri := norm_add_le (iteratedFDeriv ℝ i a θ-iteratedFDeriv ℝ i b θ)
      (iteratedFDeriv ℝ i b θ)
    rw [sub_add_cancel] at htri
    exact htri.trans ((add_le_add (hsub.trans hsmall) (HD0 θ hθ i hi)).trans_eq
      (by dsimp [D];ring))
  have hfs : ContDiffAt ℝ ∞ f (a θ) := hreg.2.1 _ hqs
  have hgsa : ContDiffAt ℝ ∞ g (a θ) := d.boundedSmoothOn_stationaryLimitingObjective.smooth _ hax
  have hgsb : ContDiffAt ℝ ∞ g (b θ) := d.boundedSmoothOn_stationaryLimitingObjective.smooth _ hbx
  have hscalar (i : ℕ) (_hi : 1 ≤ i) (hi : i ≤ 3) :
      ‖iteratedFDeriv ℝ i (fun w=>f w-g w) (a θ)‖≤ε := hreg.2.2.2.1 _ hqs i hi
  have Herr := HKg f a b θ ε η hε hη ha hb hax hbx hfs haj hbj hgraph hscalar
  have hJp : ContDiffAt ℝ ∞ (d.revisedScalarObjective p) θ := hfs.comp θ ha
  have hJ : ContDiffAt ℝ ∞ (revisedLimitingScalarObjective Ξ) θ :=
    d.revisedLimitingScalarObjective_smooth θ hθ
  have heF := revised_eventually_fderiv_stationary_graph hfs hq
    (hreg.2.2.2.2.mono (fun _ hu=>hu.2))
  have heG := revised_eventually_fderiv_stationary_graph hgsb hr
    (d.limitingBranch_eventually_stationary θ hθ)
  have heValue := d.revisedLimitingScalarObjective_eventuallyEq θ hθ
  let P := revisedParameterGradientProjection (Θ:=ℝ×ℝ) (Z:=AtomicPoint r)
  let R : ℝ×ℝ→((ℝ×ℝ)×AtomicPoint r)→L[ℝ]ℝ :=
    fun u=>fderiv ℝ f (a u)-fderiv ℝ g (b u)
  have hR : ContDiffAt ℝ ∞ R θ :=
    ((hfs.fderiv_right (m:=∞) (by simp)).comp θ ha).sub
      ((hgsb.fderiv_right (m:=∞) (by simp)).comp θ hb)
  have heD : (fun u=>fderiv ℝ (d.revisedScalarObjective p) u-
      fderiv ℝ (revisedLimitingScalarObjective Ξ) u)=ᶠ[𝓝 θ] (P∘R) := by
    filter_upwards [heF,heG,heValue.fderiv (𝕜:=ℝ)] with u huF huG huV
    change fderiv ℝ (fun t=>f (t,d.stationaryBranch p t)) u-
      fderiv ℝ (revisedLimitingScalarObjective Ξ) u=_
    rw [huF,←huV,huG]
    exact (P.map_sub _ _).symm
  have hP : ‖P‖≤1 := revisedParameterGradientProjection_norm_le
  have hsum : (1+Kg)*ε+(1+Kv+Kg)*η≤C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) := by
    convert Hsum p hp1 using 1
    dsimp only [ε,η]
    ring
  refine ⟨hJp,?_⟩
  intro j hj
  cases j with
  | zero =>
    rw [norm_iteratedFDeriv_zero]
    have hv := heValue.eq_of_nhds
    have hzero : ‖f (a θ)-g (a θ)‖≤ε := by
      simpa only [norm_iteratedFDeriv_zero] using hreg.2.2.2.1 _ hqs 0 (by omega)
    have hdisp : ‖a θ-b θ‖≤η := by
      simpa only [norm_iteratedFDeriv_zero] using hgraph 0 (by omega)
    have hfixed : ‖g (a θ)-g (b θ)‖≤Kv*η :=
      (HKv (b θ) hbx (a θ) hax).trans (mul_le_mul_of_nonneg_left hdisp hKv)
    have hbound : ‖f (a θ)-g (b θ)‖≤ε+Kv*η := by
      calc
        _=‖(f (a θ)-g (a θ))+(g (a θ)-g (b θ))‖ := by congr 1;ring
        _≤‖f (a θ)-g (a θ)‖+‖g (a θ)-g (b θ)‖ := norm_add_le _ _
        _≤ε+Kv*η := add_le_add hzero hfixed
    change ‖f (a θ)-revisedLimitingScalarObjective Ξ θ‖≤_
    rw [←hv]
    exact hbound.trans ((by
      have h1 := mul_nonneg hKg hε
      have h2 := mul_nonneg (by linarith : 0≤1+Kg) hη
      nlinarith : ε+Kv*η≤(1+Kg)*ε+(1+Kv+Kg)*η).trans hsum)
  | succ i =>
    have hi : i≤2 := by omega
    rw [←norm_iteratedFDeriv_fderiv,
      ((eventually_fderiv_sub_formula hJp hJ).iteratedFDeriv (𝕜:=ℝ) i).eq_of_nhds,
      (heD.iteratedFDeriv (𝕜:=ℝ) i).eq_of_nhds]
    have hn := P.norm_iteratedFDeriv_comp_left hR (show (i:ℕ∞ω)≤∞ by simp)
    have hbound : ‖iteratedFDeriv ℝ i (P∘R) θ‖≤Kg*(ε+η) :=
      hn.trans ((mul_le_mul_of_nonneg_right hP (norm_nonneg _)).trans
        (by simpa only [one_mul] using Herr i hi))
    exact hbound.trans ((by
      have h1 := mul_nonneg hε (show (0:ℝ)≤1 by norm_num)
      have h2 := mul_nonneg (by linarith : 0≤1+Kv) hη
      nlinarith : Kg*(ε+η)≤(1+Kg)*ε+(1+Kv+Kg)*η).trans hsum)

theorem revisedScalarObjective_C3_uniform_limit (d : LimitingStandingData Ξ seed)
    (j : ℕ) (hj : j≤3) :
    TendstoUniformlyOn
      (fun p θ=>iteratedFDeriv ℝ j
        (fun u=>d.revisedScalarObjective p u-revisedLimitingScalarObjective Ξ u) θ)
      (fun _=>0) (atTop⊓𝓟 {p : ℕ|Even p}) d.parameterWindow := by
  obtain ⟨C,hC,A,c,hc,H⟩ := d.revisedScalarObjective_C3_exponential_error
  have H' : ∀ᶠp : ℕ in atTop⊓𝓟 {p : ℕ|Even p},∀θ∈d.parameterWindow,
      ‖iteratedFDeriv ℝ j
        (fun u=>d.revisedScalarObjective p u-revisedLimitingScalarObjective Ξ u) θ‖≤
          C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) := by
    rw [eventually_inf_principal]
    filter_upwards [H] with p hp heven θ hθ
    exact (hp heven θ hθ).2 j hj
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have Hsmall : ∀ᶠp : ℕ in atTop,C*(p:ℝ)^A*Real.exp (-c*(p:ℝ))<ε :=
    (tendsto_nat_polynomial_exp C c A hc).eventually (eventually_lt_nhds hε)
  filter_upwards [H',Hsmall.filter_mono inf_le_left] with p hp hsmall θ hθ
  simpa only [dist_eq_norm,zero_sub,norm_neg] using (hp θ hθ).trans_lt hsmall

end LimitingStandingData
end GeneralDepthPaper
