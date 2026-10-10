module

public import GeneralDepthPaper.EndpointDeficitIdentity
public import GeneralDepthPaper.EndpointMixedJetBounds
public import GeneralDepthPaper.EndpointVarianceJets
public import GeneralDepthPaper.PointwiseDerivativeBounds
public import GeneralDepthPaper.InverseDerivativeBounds

@[expose] public section


/-! Actual covariance curvature and its reciprocal on the endpoint strip.
Their parameter jets have polynomial degree bounds. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
namespace GeneralDepthPaper
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 64

theorem contDiff_highDegreeSecondExpression (Ξ : AdmissibleCovariance) (p : ℕ) :
    ContDiff ℝ ∞ (highDegreeSecondExpression Ξ p) := by
  have hs : ContDiff ℝ ∞ Ξ.second := by
    unfold AdmissibleCovariance.second
    fun_prop
  exact (hs.comp contDiff_snd).add
    (((contDiff_fst.mul contDiff_const).mul contDiff_const).mul (contDiff_snd.pow (p-2)))

theorem highDegreeSecondExpression_eq_variance_derivative (Ξ : AdmissibleCovariance)
    (p : ℕ) (hp : 2 ≤ p) (qc : ℝ) (w : ℝ×ℝ) :
    highDegreeSecondExpression Ξ p w=fderiv ℝ (endpointVarianceExpression Ξ p qc) w (0,1) := by
  have hd : HasDerivAt (fun s:ℝ=> endpointVarianceExpression Ξ p qc (w.1,w.2+s))
      (highDegreeSecondExpression Ξ p w) 0 := by
    have hQ : HasDerivAt (fun s:ℝ=> w.2+s) 1 0 := (hasDerivAt_id 0).const_add _
    have hfirst := (by simpa only [add_zero] using Ξ.hasDerivAt_first w.2 :
      HasDerivAt Ξ.first (Ξ.second w.2) (w.2+0)).comp 0 hQ
    have hpow := hQ.pow (p-1)
    have he : p-1-1=p-2 := by omega
    convert (hfirst.sub_const (Ξ.first qc)).add
      ((hpow.sub_const (qc^(p-1))).const_mul (w.1*(p:ℝ))) using 1
    · funext s
      simp [endpointVarianceExpression,highDegreeSecondExpression,he,Function.comp_def]
    · simp [highDegreeSecondExpression,he]
      ring
  have hl : HasDerivAt (fun s:ℝ=> w+s • ((0,1):ℝ×ℝ)) ((0,1):ℝ×ℝ) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const ((0,1):ℝ×ℝ)).const_add w
  have H := ((contDiff_endpointVarianceExpression Ξ p qc).differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hl
  have H' : HasDerivAt (fun s:ℝ=> endpointVarianceExpression Ξ p qc (w.1,w.2+s))
      (fderiv ℝ (endpointVarianceExpression Ξ p qc) w (0,1)) 0 := by
    convert H using 1
    · funext s
      congr 1
      ext <;> simp
    · simp
  exact hd.unique H'

theorem highDegreeSecondExpression_jet_bound (Ξ : AdmissibleCovariance) {qc L : ℝ}
    (hc : qc∈Icc (0:ℝ) 1) (j : ℕ) :
    ∃C:ℝ,0 ≤ C ∧ ∀p:ℕ,2 ≤ p→∀w:ℝ×ℝ,w.1∈Icc (0:ℝ) L→w.2∈Icc (0:ℝ) 1→
      ‖iteratedFDeriv ℝ j (highDegreeSecondExpression Ξ p) w‖ ≤ C*(p:ℝ)^(j+2) := by
  obtain ⟨C,hC,hb⟩ := endpointVarianceExpression_jet_bound Ξ hc (j+1) (L:=L)
  refine ⟨C,hC,?_⟩
  intro p hp w hl hQ
  have he : highDegreeSecondExpression Ξ p=(fun y=> fderiv ℝ (endpointVarianceExpression Ξ p qc) y (0,1)) := by
    funext y
    exact highDegreeSecondExpression_eq_variance_derivative Ξ p hp qc y
  rw [he]
  exact (norm_iteratedFDeriv_directional_derivative_le
    (contDiff_endpointVarianceExpression Ξ p qc).contDiffAt ((0,1):ℝ×ℝ)
      (by simp [Prod.norm_def]) j).trans (hb p (by omega) w hl hQ)

def endpointPairProjection {r : ℕ} : CutoffInputParameter r→L[ℝ]ℝ×ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ (ℝ×ℝ)).comp
    (ContinuousLinearMap.snd ℝ (AtomicPoint r) (ℝ×(ℝ×ℝ)))

theorem norm_endpointPairProjection_le {r : ℕ} : ‖endpointPairProjection (r:=r)‖ ≤ 1 := by
  apply (endpointPairProjection (r:=r)).opNorm_le_bound zero_le_one
  intro x
  change ‖x.2.2‖ ≤ 1*‖x‖
  rw [one_mul]
  exact (norm_snd_le x.2).trans (norm_snd_le x)

theorem highDegreeSecondExpression_full_jet_bound (Ξ : AdmissibleCovariance) {r : ℕ}
    {qc L : ℝ} (hc : qc∈Icc (0:ℝ) 1) (N : ℕ) :
    ∃C:ℝ,1 ≤ C ∧ ∀p:ℕ,2 ≤ p→∀x:CutoffInputParameter r,x.2.2.1∈Icc (0:ℝ) L→
      x.2.2.2∈Icc (0:ℝ) 1→∀j:ℕ,j ≤ N→
        ‖iteratedFDeriv ℝ j (fun y:CutoffInputParameter r=> highDegreeSecondExpression Ξ p y.2.2) x‖ ≤ C*(p:ℝ)^(N+2) := by
  choose C hC hb using fun j=> highDegreeSecondExpression_jet_bound Ξ hc j (L:=L)
  let D := 1+∑j∈Finset.range (N+1),C j
  have hD : 1 ≤ D := by dsimp only [D];exact le_add_of_nonneg_right (Finset.sum_nonneg (fun j _=> hC j))
  refine ⟨D,hD,?_⟩
  intro p hp x hl hQ j hj
  have h := norm_iteratedFDeriv_comp_CLM_contraction (x:=x) (endpointPairProjection (r:=r))
    norm_endpointPairProjection_le (contDiff_highDegreeSecondExpression Ξ p).contDiffAt j
  have hjC : C j ≤ D := by
    have H : C j ≤ ∑k∈Finset.range (N+1),C k :=
      Finset.single_le_sum (fun k _=> hC k) (Finset.mem_range.mpr (by omega))
    exact H.trans (by dsimp only [D];linarith)
  exact h.trans ((hb j p hp x.2.2 hl hQ).trans
    (mul_le_mul hjC (pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ p by omega))
      (by omega)) (pow_nonneg (Nat.cast_nonneg _) _) (zero_le_one.trans hD)))

theorem endpoint_curvature_at_least_one_eventually (Ξ : AdmissibleCovariance)
    {lo hi cQ CQ : ℝ} (hlo : 0 < lo) (hcQ : 0 < cQ) :
    ∀ᶠp:ℕ in atTop,4 ≤ p ∧ ∀w:ℝ×ℝ,w.1∈Icc lo hi→w.2∈endpointStrip cQ CQ p→
      1 ≤ highDegreeSecondExpression Ξ p w := by
  have he := tendsto_nat_polynomial_exp 1 cQ 1 hcQ
  have hp := tendsto_natCast_atTop_atTop (R:=ℝ)
  filter_upwards [he.eventually (gt_mem_nhds (show (0:ℝ) < 1/2 by norm_num)),
    hp.eventually (eventually_ge_atTop (2/lo)),
    eventually_ge_atTop (4:ℕ)] with p he hp hp4
  refine ⟨hp4,?_⟩
  intro w hl hQ
  have hQu : w.2∈Icc (0:ℝ) 1 :=
    ⟨(endpointStrip_mem_unit hcQ p hQ).1,(endpointStrip_mem_unit hcQ p hQ).2.le⟩
  have hpow : 1/2 ≤ w.2^(p-2) := by
    have hn : ((p-2:ℕ):ℝ) ≤ (p:ℝ) := by exact_mod_cast Nat.sub_le p 2
    have hgap := (one_sub_pow_bound hQu (p-2)).trans
      (mul_le_mul hn (endpointStrip_distance_bound p hQ)
        (sub_nonneg.mpr hQu.2) (Nat.cast_nonneg p))
    norm_num only [one_mul,pow_one] at he
    linarith
  have hpp : 1 ≤ ((p-1:ℕ):ℝ) := by exact_mod_cast (show 1 ≤ p-1 by omega)
  have hlarge : 2 ≤ lo*(p:ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ hlo).mp hp
  have hpos : 0 ≤ Ξ.second w.2 := Ξ.second_nonneg hQu.1
  have H := mul_le_mul
    (mul_le_mul_of_nonneg_right hl.1 (Nat.cast_nonneg p)) hpp (by norm_num)
      (mul_nonneg (hlo.le.trans hl.1) (Nat.cast_nonneg p))
  have H2 := mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (mul_nonneg (hlo.le.trans hl.1) (Nat.cast_nonneg p)) (Nat.cast_nonneg (p-1)))
  dsimp only [highDegreeSecondExpression]
  nlinarith

end GeneralDepthPaper
