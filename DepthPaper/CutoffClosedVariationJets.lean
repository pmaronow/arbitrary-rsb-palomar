module

public import DepthPaper.CutoffDataHighDegreeConvergence
public import DepthPaper.VariationRegularity

@[expose] public section


/-! Identifying intrinsic closed-interval jets with the actual compatible
cutoff moment jets. Equality on the closed interval is sufficient; no
differentiability of an arbitrary extension outside that interval is used. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 800000

theorem closedJet_succ (bar : ℝ) (j : ℕ) (f : ℝ→ℝ) :
    closedJet bar (j+1) f=derivWithin (closedJet bar j f) (Icc (0:ℝ) bar) := by
  simp only [closedJet,Function.iterate_succ_apply']

theorem closedJet_two_of_mem_Ioo {bar x : ℝ} (f : ℝ→ℝ)
    (hx : x∈Ioo (0:ℝ) bar) : closedJet bar 2 f x=deriv (deriv f) x := by
  change derivWithin (derivWithin f (Icc (0:ℝ) bar)) (Icc (0:ℝ) bar) x=deriv (deriv f) x
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  exact derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)

theorem closedJet_congr_interval {bar : ℝ} {f g : ℝ→ℝ}
    (he : EqOn f g (Icc (0:ℝ) bar)) (j : ℕ) :
    EqOn (closedJet bar j f) (closedJet bar j g) (Icc (0:ℝ) bar) := by
  induction j with
  | zero=>simpa only [closedJet,Function.iterate_zero_apply] using he
  | succ j ih=>
    intro x hx
    rw [closedJet_succ,closedJet_succ]
    exact derivWithin_congr ih (ih hx)

theorem closedJet_const_mul (bar c : ℝ) (j : ℕ) (f : ℝ→ℝ) :
    closedJet bar j (fun x=>c*f x)=(fun x=>c*closedJet bar j f x) := by
  induction j with
  | zero=>rfl
  | succ j ih=>
    funext x
    rw [closedJet_succ,closedJet_succ]
    rw [ih,derivWithin_const_mul_field]

theorem closedJet_eq_truncatedVariationJets {r : ℕ} {qc : ℝ}
    (d : TruncatedParisiData r qc) (f : ℝ→ℝ)
    (he : EqOn f d.firstVariation (Icc (0:ℝ) qc))
    (j : Fin 3) (q : ℝ) (hq : q∈Icc (0:ℝ) qc) :
    closedJet qc j f q=d.firstVariationJets j ⟨q,hq⟩ := by
  have hu : UniqueDiffOn ℝ (Icc (0:ℝ) qc):=uniqueDiffOn_Icc d.qc_pos
  have h1 : EqOn (derivWithin f (Icc (0:ℝ) qc)) d.firstVariationPrime (Icc (0:ℝ) qc) := by
    intro t ht
    exact ((d.hasDerivAt_firstVariation t).hasDerivWithinAt.congr he (he ht)).derivWithin (hu t ht)
  fin_cases j
  · exact he hq
  · change derivWithin f (Icc (0:ℝ) qc) q=d.firstVariationPrimeMap ⟨q,hq⟩
    rw [TruncatedParisiData.firstVariationPrimeMap_apply]
    exact h1 hq
  · change derivWithin (derivWithin f (Icc (0:ℝ) qc)) (Icc (0:ℝ) qc) q=
      d.firstVariationSecondMap ⟨q,hq⟩
    rw [TruncatedParisiData.firstVariationSecondMap_apply]
    exact ((d.hasDerivWithinAt_firstVariationPrime q hq).congr h1 (h1 hq)).derivWithin (hu q hq)

theorem closedVariationJets_uniform_convergence {r : ℕ} {qc : ℝ}
    (d : ℕ→TruncatedParisiData r qc) (d0 : TruncatedParisiData r qc)
    (h : TruncatedDataConvergence d d0) (f : ℕ→ℝ→ℝ) (F : ℝ→ℝ)
    (he : ∀n,EqOn (f n) (d n).firstVariation (Icc (0:ℝ) qc))
    (hF : EqOn F d0.firstVariation (Icc (0:ℝ) qc)) :
    ∀j≤2,TendstoUniformlyOn (fun n=>closedJet qc j (f n))
      (closedJet qc j F) atTop (Icc (0:ℝ) qc) := by
  intro j hj
  let jj : Fin 3:=⟨j,by omega⟩
  have ht:=(tendsto_pi_nhds.mp h.firstVariation_C2) jj
  have hn : Tendsto (fun n=>‖(d n).firstVariationJets jj-d0.firstVariationJets jj‖)
      atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero] using
      (ht.sub (tendsto_const_nhds (x:=d0.firstVariationJets jj))).norm
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hn.eventually (eventually_lt_nhds hε)] with n hne q hq
  rw [Real.dist_eq,←Real.norm_eq_abs]
  rw [show j=(jj:ℕ) from rfl,
    closedJet_eq_truncatedVariationJets (d n) (f n) (he n) jj q hq,
    closedJet_eq_truncatedVariationJets d0 F hF jj q hq,norm_sub_rev]
  exact (ContinuousMap.norm_coe_le_norm
    ((d n).firstVariationJets jj-d0.firstVariationJets jj) ⟨q,hq⟩).trans_lt hne

end DepthPaper
