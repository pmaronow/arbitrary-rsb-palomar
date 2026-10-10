module

public import GeneralDepthPaper.LogErrorTerminalMixed

@[expose] public section


/-! Uniform exponential bounds for the genuine compatible mixed terminal
jets, in the exact sum norm of the manuscript as well as the inherited norm. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal BoundedContinuousFunction BigOperators
namespace GeneralDepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem LogDeficitExpr.small_massDV_iterate
    (e : LogDeficitExpr MassResidualNormalizerExpr) (he : e.Small) (k : ℕ) :
    (LogDeficitExpr.massDV^[k] e).Small :=
  e.small_iterate_differentiate MassResidualNormalizerExpr.dV deficitBaseExpr.lift.dV 0 k he

theorem four_logarithmic_sections_exponential_bound
    (E : Fin 4→LogDeficitExpr MassResidualNormalizerExpr) (hE : ∀i,(E i).Small)
    {ε : ℝ} (hε : 0<ε) :
    ∃C:ℝ,0<C ∧ ∃D:ℕ,∀m∈Icc ε 1,∀V≥1,∀i:Fin 4,∀x:ℝ,
      ‖(E i).physicalEval m V x‖≤C*V^D*Real.exp (-(ε^2)*V/2) := by
  classical
  have hb (i : Fin 4):=(E i).small_exponential_bound hε (hE i)
  choose c hc d hbound using hb
  let C : ℝ:=1+∑i:Fin 4,c i
  let D : ℕ:=∑i:Fin 4,d i
  have hC : 0<C := by
    have hs:0≤∑i:Fin 4,c i:=Finset.sum_nonneg (fun i _=>(hc i).le)
    dsimp only [C]
    linarith
  refine ⟨C,hC,D,?_⟩
  intro m hm V hV i x
  have hci:c i≤C := by
    have hi:=Finset.single_le_sum (fun k (_:k∈(Finset.univ:Finset (Fin 4)))=>(hc k).le)
      (Finset.mem_univ i)
    dsimp only [C]
    linarith
  have hdi:d i≤D:=Finset.single_le_sum (fun k (_:k∈(Finset.univ:Finset (Fin 4)))=>Nat.zero_le _)
    (Finset.mem_univ i)
  have hd:V^(d i)≤V^D := by
    rw [←Real.rpow_natCast,←Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hV (by exact_mod_cast hdi)
  exact (hbound i m hm V hV x).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul hci hd (by positivity) hC.le)
      (Real.exp_pos _).le)

theorem LogDeficitExpr.parameterTerminalJet_exponential_bound
    (e : LogDeficitExpr MassResidualNormalizerExpr) (he : e.Small)
    {ε : ℝ} (hε : 0<ε) (hε1 : ε<1) (j k : ℕ) :
    ∃C:ℝ,0<C ∧ ∃D:ℕ,∀V:ℝ,∀hV:1≤V,∀m∈Icc ε 1,
      ‖e.parameterTerminalJet ε hε V hV j k m‖≤C*V^D*Real.exp (-(ε^2)*V/2) := by
  let E (i : Fin 4):=LogDeficitExpr.dm^[j]
    (LogDeficitExpr.massDV^[k] (LogDeficitExpr.massDx^[(i:ℕ)] e))
  have hE (i : Fin 4):(E i).Small:=
    (LogDeficitExpr.massDV^[k] (LogDeficitExpr.massDx^[(i:ℕ)] e)).small_dm_iterate
      ((LogDeficitExpr.massDx^[(i:ℕ)] e).small_massDV_iterate
        (e.small_massDx_iterate he i) k) j
  obtain ⟨C,hC,D,hb⟩:=four_logarithmic_sections_exponential_bound E hE hε
  refine ⟨C,hC,D,?_⟩
  intro V hV m hm
  let B:=C*V^D*Real.exp (-(ε^2)*V/2)
  have hB:0≤B:=by dsimp only [B];positivity
  change ‖(e.parameterTerminalJet ε hε V hV j k m:TerminalJetData)‖≤B
  rw [e.parameterTerminalJet_coe hε hε1 hV j k hm]
  apply norm_prod_le_iff.mpr
  constructor
  · change ‖(LogDeficitExpr.dm^[j] (LogDeficitExpr.massDV^[k] e)).massBCF ε hε V hV m 0‖≤B
    rw [LogDeficitExpr.massBCF_apply _ hε hV hm]
    exact hb m hm V hV 0 0
  · apply (pi_norm_le_iff_of_nonneg hB).mpr
    intro i
    apply (BoundedContinuousFunction.norm_le hB).mpr
    intro x
    change ‖(LogDeficitExpr.dm^[j] (LogDeficitExpr.massDV^[k]
      (LogDeficitExpr.massDx^[((i:ℕ)+1)] e))).massBCF ε hε V hV m x‖≤B
    rw [LogDeficitExpr.massBCF_apply _ hε hV hm]
    exact hb m hm V hV ⟨i+1,by omega⟩ x

theorem LogDeficitExpr.parameterTerminalJet_sumNorm_exponential_bound
    (e : LogDeficitExpr MassResidualNormalizerExpr) (he : e.Small)
    {ε : ℝ} (hε : 0<ε) (hε1 : ε<1) (j k : ℕ) :
    ∃C:ℝ,0<C ∧ ∃D:ℕ,∀V:ℝ,∀hV:1≤V,∀m∈Icc ε 1,
      terminalSumNorm (e.parameterTerminalJet ε hε V hV j k m)≤
        C*V^D*Real.exp (-(ε^2)*V/2) := by
  obtain ⟨C,hC,D,hb⟩:=e.parameterTerminalJet_exponential_bound he hε hε1 j k
  refine ⟨4*C,by positivity,D,?_⟩
  intro V hV m hm
  exact (terminalSumNorm_le_four_norm _).trans
    ((mul_le_mul_of_nonneg_left (hb V hV m hm) (by norm_num : (0:ℝ)≤4)).trans_eq (by ring))

end GeneralDepthPaper
