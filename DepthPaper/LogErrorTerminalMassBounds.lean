module

public import DepthPaper.LogErrorTerminalMass

@[expose] public section


/-! Genuine exponentially small Banach mass jets of the logarithmic error.
The inherited maximum norm and the manuscript's sum norm are both bounded. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal BoundedContinuousFunction BigOperators
namespace DepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem LogDeficitExpr.small_massDx_iterate
    (e : LogDeficitExpr MassResidualNormalizerExpr) (he : e.Small) (i : ℕ) :
    (LogDeficitExpr.massDx^[i] e).Small :=
  e.small_iterate_differentiate MassResidualNormalizerExpr.dx deficitBaseExpr.lift.dx 0 i he

theorem LogDeficitExpr.small_dm_iterate
    (e : LogDeficitExpr MassResidualNormalizerExpr) (he : e.Small) (j : ℕ) :
    (LogDeficitExpr.dm^[j] e).Small :=
  e.small_iterate_differentiate MassResidualNormalizerExpr.dm deficitBaseExpr.lift.dm 1 j he

theorem LogDeficitExpr.massTerminalJet_exponential_bound
    (e : LogDeficitExpr MassResidualNormalizerExpr) (he : e.Small)
    {ε : ℝ} (hε : 0<ε) (hε1 : ε<1) (j : ℕ) :
    ∃C:ℝ,0<C ∧ ∃d:ℕ,∀V:ℝ,∀hV:1≤V,∀m∈Icc ε 1,
      ‖e.massTerminalJet ε hε V hV j m‖≤C*V^d*Real.exp (-(ε^2)*V/2) := by
  classical
  let E (i : Fin 4) : LogDeficitExpr MassResidualNormalizerExpr :=
    LogDeficitExpr.dm^[j] (LogDeficitExpr.massDx^[(i:ℕ)] e)
  have hE (i : Fin 4) : (E i).Small :=
    (LogDeficitExpr.massDx^[(i:ℕ)] e).small_dm_iterate (e.small_massDx_iterate he i) j
  have hb (i : Fin 4) := (E i).small_exponential_bound hε (hE i)
  choose c hc d hbound using hb
  let C : ℝ := 1+∑i:Fin 4,c i
  let D : ℕ := ∑i:Fin 4,d i
  have hC : 0<C := by
    have hs : 0≤∑i:Fin 4,c i := Finset.sum_nonneg (fun i _=>(hc i).le)
    dsimp only [C]
    linarith
  have hci (i : Fin 4) : c i≤C := by
    have hi:=Finset.single_le_sum (fun k (_:k∈(Finset.univ:Finset (Fin 4)))=>(hc k).le)
      (Finset.mem_univ i)
    dsimp only [C]
    linarith
  have hdi (i : Fin 4) : d i≤D :=
    Finset.single_le_sum (fun k (_:k∈(Finset.univ:Finset (Fin 4)))=>Nat.zero_le _)
      (Finset.mem_univ i)
  refine ⟨C,hC,D,?_⟩
  intro V hV m hm
  let B := C*V^D*Real.exp (-(ε^2)*V/2)
  have hB : 0≤B := by dsimp only [B]; positivity
  have hp (i : Fin 4) (x : ℝ) : ‖(E i).physicalEval m V x‖≤B := by
    have hd : V^(d i)≤V^D := by
      rw [←Real.rpow_natCast,←Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hV (by exact_mod_cast hdi i)
    exact (hbound i m hm V hV x).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul (hci i) hd (by positivity) hC.le)
        (Real.exp_pos _).le)
  change ‖(e.massTerminalJet ε hε V hV j m:TerminalJetData)‖≤B
  rw [e.massTerminalJet_coe hε hε1 hV j hm]
  apply norm_prod_le_iff.mpr
  constructor
  · change ‖(LogDeficitExpr.dm^[j] e).massBCF ε hε V hV m 0‖≤B
    rw [LogDeficitExpr.massBCF_apply _ hε hV hm]
    exact hp 0 0
  · apply (pi_norm_le_iff_of_nonneg hB).mpr
    intro i
    apply (BoundedContinuousFunction.norm_le hB).mpr
    intro x
    change ‖(LogDeficitExpr.dm^[j] (LogDeficitExpr.massDx^[((i:ℕ)+1)] e)).massBCF ε hε V hV m x‖≤B
    rw [LogDeficitExpr.massBCF_apply _ hε hV hm]
    exact hp ⟨i+1,by omega⟩ x

theorem LogDeficitExpr.massTerminalJet_sumNorm_exponential_bound
    (e : LogDeficitExpr MassResidualNormalizerExpr) (he : e.Small)
    {ε : ℝ} (hε : 0<ε) (hε1 : ε<1) (j : ℕ) :
    ∃C:ℝ,0<C ∧ ∃d:ℕ,∀V:ℝ,∀hV:1≤V,∀m∈Icc ε 1,
      terminalSumNorm (e.massTerminalJet ε hε V hV j m)≤
        C*V^d*Real.exp (-(ε^2)*V/2) := by
  obtain ⟨C,hC,d,hb⟩:=e.massTerminalJet_exponential_bound he hε hε1 j
  refine ⟨4*C,by positivity,d,?_⟩
  intro V hV m hm
  exact (terminalSumNorm_le_four_norm _).trans
    ((mul_le_mul_of_nonneg_left (hb V hV m hm) (by norm_num : (0:ℝ)≤4)).trans_eq (by ring))

end DepthPaper
