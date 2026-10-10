module

public import GeneralDepthPaper.CutoffInputPerturbation
public import GeneralDepthPaper.ConvexRecursionBounds

@[expose] public section


/-! Uniform geometric input windows are derived from a compact set of
actual lower atomic configurations. Positive variance increments and
terminal/parameter jet bounds are consequences, not supplied estimates. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff BigOperators
namespace GeneralDepthPaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

def cutoffParameterWindow {r : ℕ} (K : Set (AtomicPoint r)) (ε lamlo lamhi : ℝ) :
    Set (CutoffInputParameter r) := K ×ˢ (Icc ε 1 ×ˢ (Icc lamlo lamhi ×ˢ Icc (0:ℝ) 1))

theorem isCompact_cutoffParameterWindow {r : ℕ} {K : Set (AtomicPoint r)}
    (hK : IsCompact K) (ε lamlo lamhi : ℝ) :
    IsCompact (cutoffParameterWindow K ε lamlo lamhi) :=
  hK.prod (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))

theorem contDiffAt_cutoffComparisonInput (Ξ : AdmissibleCovariance) {r : ℕ} (qc : ℝ)
    (x : CutoffInputParameter r) (hm : x.2.1∈Ioo (0:ℝ) 2) :
    ContDiffAt ℝ ∞ (cutoffComparisonInput Ξ qc) x := by
  have hs := (contDiff_cutoffRecursionSteps_parameter Ξ qc).contDiffAt.comp x
    cutoffVarianceProjection.contDiff.contDiffAt
  have ht := (contDiffAt_scaledLogCoshTerminal hm).comp x
    (show ContDiffAt ℝ ∞ (fun x : CutoffInputParameter r => x.2.1) x by fun_prop)
  exact hs.prodMk ht

theorem cutoffComparisonInput_low_order_bound (Ξ : AdmissibleCovariance) {r : ℕ}
    {K : Set (AtomicPoint r)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε)
    (lamlo lamhi qc : ℝ) (N : ℕ) :
    ∃D:ℝ,1 ≤ D ∧ ∀x∈cutoffParameterWindow K ε lamlo lamhi,
      ∀j:ℕ,j ≤ N → ‖iteratedFDeriv ℝ j (cutoffComparisonInput Ξ qc) x‖ ≤ D :=
  (BoundedSmoothOn.of_compact (isCompact_cutoffParameterWindow hK ε lamlo lamhi)
    (fun x hx => contDiffAt_cutoffComparisonInput Ξ qc x
      ⟨hε.trans_le hx.2.1.1,hx.2.1.2.trans_lt (by norm_num)⟩)).all_orders_up_to_bound N

theorem cutoffVariance_comparison_window (Ξ : AdmissibleCovariance) {r : ℕ}
    {K : Set (AtomicPoint r)} (hK : IsCompact K)
    (hvalid : ∀z∈K,IsAtomicPoint z) (qc : ℝ)
    (hc : ∀z∈K,atomicLocation z (Fin.last r)<qc) :
    ∃Vlo Vhi:ℝ,0 < Vlo ∧ Vlo ≤ Vhi ∧ ∀z∈K,∀m:ℝ,∀i:Fin (r+1),
      Vlo ≤ (cutoffRecursionSteps Ξ z m qc i).2 ∧
      (cutoffRecursionSteps Ξ z m qc i).2 ≤ Vhi := by
  classical
  by_cases hne : K.Nonempty
  · have hv (i : Fin (r+1)) : Continuous (fun z : AtomicPoint r =>
        Ξ.first (cutoffAtomicNode z qc i.succ)-Ξ.first (cutoffAtomicNode z qc i.castSucc)) :=
      ((Ξ.contDiff_first.comp (contDiff_cutoffAtomicNode qc i.succ)).sub
        (Ξ.contDiff_first.comp (contDiff_cutoffAtomicNode qc i.castSucc))).continuous
    have hmin (i : Fin (r+1)) := hK.exists_isMinOn hne (hv i).continuousOn
    choose zm hzm hm using hmin
    let a : Fin (r+1)→ℝ := fun i =>
      Ξ.first (cutoffAtomicNode (zm i) qc i.succ)-Ξ.first (cutoffAtomicNode (zm i) qc i.castSucc)
    have ha (i : Fin (r+1)) : 0 < a i :=
      cutoffRecursionSteps_variance_pos Ξ (zm i) (hvalid _ (hzm i)) 0 qc (hc _ (hzm i)) i
    let Vlo : ℝ := Finset.univ.inf' Finset.univ_nonempty a
    have hVlo : 0 < Vlo := (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun i _ => ha i)
    have hmax (i : Fin (r+1)) := hK.exists_bound_of_continuousOn (hv i).continuousOn
    choose b hb using hmax
    let Vhi : ℝ := max Vlo (∑i:Fin (r+1),max (b i) 0)
    refine ⟨Vlo,Vhi,hVlo,le_max_left _ _,fun z hz m i => ⟨?_,?_⟩⟩
    · exact (Finset.inf'_le a (Finset.mem_univ i)).trans (hm i hz)
    · have hh := hb i z hz
      have hsum : max (b i) 0 ≤ ∑k:Fin (r+1),max (b k) 0 :=
        Finset.single_le_sum (fun k _ => le_max_right _ _) (Finset.mem_univ i)
      exact (le_abs_self _).trans (hh.trans ((le_max_left _ _).trans
        (hsum.trans (le_max_right _ _))))
  · refine ⟨1,1,by norm_num,le_rfl,?_⟩
    intro z hz
    exact False.elim (hne ⟨z,hz⟩)

theorem cutoffComparisonInput_mem_ball (Ξ : AdmissibleCovariance) {r : ℕ}
    {K : Set (AtomicPoint r)} (hK : IsCompact K) (hvalid : ∀z∈K,IsAtomicPoint z)
    {ε : ℝ} (hε : 0 < ε) (lamlo lamhi qc : ℝ)
    (hc : ∀z∈K,atomicLocation z (Fin.last r)<qc) :
    ∃Vlo Vhi B:ℝ,0 < Vlo ∧ Vlo ≤ Vhi ∧ 0 ≤ B ∧
      ∀x∈cutoffParameterWindow K ε lamlo lamhi,
        cutoffComparisonInput Ξ qc x∈coleHopfRecursionBall (r+1) 1 Vlo Vhi B := by
  obtain ⟨Vlo,Vhi,hlo,hLH,hv⟩ := cutoffVariance_comparison_window Ξ hK hvalid qc hc
  obtain ⟨D,hD,hd⟩ := cutoffComparisonInput_low_order_bound Ξ hK hε lamlo lamhi qc 0
  refine ⟨Vlo,Vhi,D,hlo,hLH,zero_le_one.trans hD,fun x hx => ⟨fun i => ⟨?_,hv x.1 hx.1 x.2.1 i⟩,?_⟩⟩
  · change ‖x.2.1*atomicLevel x.1 i‖ ≤ 1
    have hm := hx.2.1
    have ha := atomicLevel_mem_unit x.1 (hvalid _ hx.1) i
    rw [Real.norm_of_nonneg (mul_nonneg (hε.le.trans hm.1) ha.1)]
    exact (mul_le_mul_of_nonneg_left ha.2 (hε.le.trans hm.1)).trans (by simpa using hm.2)
  · have hnorm : ‖cutoffComparisonInput Ξ qc x‖ ≤ D := by
      simpa only [norm_iteratedFDeriv_zero] using hd x hx 0 le_rfl
    exact (norm_snd_le (cutoffComparisonInput Ξ qc x)).trans hnorm

end GeneralDepthPaper
