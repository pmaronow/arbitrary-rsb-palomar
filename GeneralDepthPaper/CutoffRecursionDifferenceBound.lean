module

public import GeneralDepthPaper.CutoffCandidateWindow
public import GeneralDepthPaper.CompositionDifferenceBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section


/-! Exponential propagation of the genuine cutoff input perturbation
through the actual finite Cole–Hopf recursion. All constants are derived
from the covariance and a compact lower atomic parameter window. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff BigOperators
namespace GeneralDepthPaper
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 64

def cutoffRecursionDifferenceRaw (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (qc : ℝ) (x : CutoffInputParameter r) : TerminalSpace :=
  coleHopfRecursion (r+1) (cutoffHighDegreeInput Ξ p qc x)-
    coleHopfRecursion (r+1) (cutoffComparisonInput Ξ qc x)

theorem tendsto_nat_polynomial_exp (C c : ℝ) (A : ℕ) (hc : 0<c) :
    Tendsto (fun p : ℕ => C*(p:ℝ)^A*Real.exp (-c*(p:ℝ))) atTop (𝓝 0) := by
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (A:ℝ) c hc).comp
    tendsto_natCast_atTop_atTop
  simpa only [Real.rpow_natCast,Function.comp_def,mul_assoc,mul_zero] using
    tendsto_const_nhds.mul hh

theorem cutoff_recursion_difference_exponential_bound (Ξ : AdmissibleCovariance) {r : ℕ}
    {K : Set (AtomicPoint r)} (hK : IsCompact K) (hvalid : ∀z∈K,IsAtomicPoint z)
    {ε lamlo lamhi qc cQ CQ : ℝ} (hε : 0<ε) (hlo : 0<lamlo)
    (hLH : lamlo≤lamhi) (hc : qc∈Ioo (0:ℝ) 1)
    (hcut : ∀z∈K,atomicLocation z (Fin.last r)<qc) (hcQ : 0<cQ) (N : ℕ) :
    ∃C:ℝ,0<C ∧ ∃A:ℕ,∃c:ℝ,0<c ∧ ∃p0:ℕ,1≤p0 ∧
      ∀p:ℕ,p0≤p→∀x:CutoffInputParameter r,x.1∈K→
        x.2.1∈Icc ε 1→x.2.2.1∈Icc lamlo lamhi→x.2.2.2∈endpointStrip cQ CQ p→
        ContDiffAt ℝ ∞ (cutoffRecursionDifferenceRaw Ξ p qc) x ∧
        ∀j:ℕ,j≤N→‖iteratedFDeriv ℝ j (cutoffRecursionDifferenceRaw Ξ p qc) x‖≤
          C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) := by
  obtain ⟨B,hB⟩ := (isCompact_cutoffParameterWindow hK ε lamlo lamhi).exists_bound_of_continuousOn
    cutoffVarianceProjection.continuous.continuousOn
  obtain ⟨D,hD,hd⟩ := cutoffComparisonInput_low_order_bound Ξ hK hε lamlo lamhi qc N
  obtain ⟨Vlo,Vhi,Bt,hVlo,hV,hBt,hball⟩ :=
    cutoffComparisonInput_mem_ball Ξ hK hvalid hε lamlo lamhi qc hcut
  let s := coleHopfRecursionBall (r+1) 1 Vlo (Vhi+1) (Bt+1)
  have houter : BoundedSmoothOn (coleHopfRecursion (r+1)) s :=
    boundedSmoothOn_coleHopfRecursion (r+1) 1 Vlo (Vhi+1) (Bt+1)
      zero_le_one hVlo (by linarith) (by linarith)
  obtain ⟨Co,hCo,ho⟩ := composition_difference_bounds_up_to (E:=CutoffInputParameter r) N houter
    (convex_coleHopfRecursionBall ..) (D+1) (by linarith)
  obtain ⟨Ci,hCi,A,c,hc',pi,hpi,hi⟩ :=
    cutoff_input_low_order_exponential_bound Ξ hε hlo hLH hc hcQ B N
  have hes : ∀ᶠp:ℕ in atTop,Ci*(p:ℝ)^A*Real.exp (-c*(p:ℝ))<1 :=
    (tendsto_nat_polynomial_exp Ci c A hc').eventually (Iio_mem_nhds zero_lt_one)
  obtain ⟨ps,hps⟩ := eventually_atTop.mp hes
  refine ⟨(Co+1)*Ci,mul_pos (by linarith) hCi,A,c,hc',max pi ps,
    hpi.trans (le_max_left _ _),?_⟩
  intro p hp x hx hm hlam hQ
  have hw : x∈cutoffParameterWindow K ε lamlo lamhi :=
    ⟨hx,hm,hlam,(endpointStrip_mem_unit hcQ p hQ).1,(endpointStrip_mem_unit hcQ p hQ).2.le⟩
  have hcore : cutoffVarianceProjection x∈closedBall 0 B := by
    simpa only [mem_closedBall,dist_zero_right] using hB x hw
  have hloc : ∀i:Fin (r+1),atomicLocation x.1 i∈Icc (0:ℝ) qc := fun i =>
    ⟨(atomicLocation_mem_unit (hvalid _ hx) i).1,
      ((hvalid _ hx).1.monotone (Fin.le_last i)).trans (hcut _ hx).le⟩
  obtain ⟨hW,he,hej⟩ := hi p ((le_max_left _ _).trans hp) x hcore hloc hm hlam hQ
  let e : ℝ := Ci*(p:ℝ)^A*Real.exp (-c*(p:ℝ))
  have hepos : 0≤e := by dsimp only [e];positivity
  have hesmall : e≤1 := (hps p ((le_max_right _ _).trans hp)).le
  have hg := contDiffAt_cutoffComparisonInput Ξ qc x
    ⟨hε.trans_le hm.1,hm.2.trans_lt (by norm_num)⟩
  have hinput := norm_input_jet_le_of_difference he hg 0 (hd x hw 0 (Nat.zero_le _))
    (hej 0 (Nat.zero_le _))
  have hfx : cutoffHighDegreeInput Ξ p qc x∈s :=
    cutoffHighDegreeInput_mem_enlarged_ball Ξ p x (hvalid _ hx) (hcut _ hx)
      (hlo.le.trans hlam.1) (hball x hw)
      (by simpa only [norm_iteratedFDeriv_zero] using
        (hej 0 (Nat.zero_le _)).trans hesmall)
  have hgx : cutoffComparisonInput Ξ qc x∈s :=
    ⟨fun i=>⟨((hball x hw).1 i).1,((hball x hw).1 i).2.1,
      ((hball x hw).1 i).2.2.trans (le_add_of_nonneg_right zero_le_one)⟩,
      (hball x hw).2.trans (le_add_of_nonneg_right zero_le_one)⟩
  have hfj : ∀i,i≤N→‖iteratedFDeriv ℝ i (cutoffHighDegreeInput Ξ p qc) x‖≤D+1 := by
    intro i hin
    exact (norm_input_jet_le_of_difference he hg i (hd x hw i hin) (hej i hin)).2.trans
      (add_le_add le_rfl hesmall)
  have hgj : ∀i,i≤N→‖iteratedFDeriv ℝ i (cutoffComparisonInput Ξ qc) x‖≤D+1 :=
    fun i hin=>(hd x hw i hin).trans (le_add_of_nonneg_right zero_le_one)
  refine ⟨((houter.smooth _ hfx).comp x hinput.1).sub
    ((houter.smooth _ hgx).comp x hg),fun j hj=>?_⟩
  have HH := ho (cutoffHighDegreeInput Ξ p qc) (cutoffComparisonInput Ξ qc) x e hepos
    hinput.1 hg hfx hgx hfj hgj hej j hj
  change ‖iteratedFDeriv ℝ j (fun y=>coleHopfRecursion (r+1) (cutoffHighDegreeInput Ξ p qc y)-
    coleHopfRecursion (r+1) (cutoffComparisonInput Ξ qc y)) x‖≤_ at HH ⊢
  exact HH.trans ((mul_le_mul_of_nonneg_right
    (le_add_of_nonneg_right zero_le_one : Co≤Co+1) hepos).trans_eq (by
      dsimp only [e]
      ring))

end GeneralDepthPaper
