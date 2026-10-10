module

public import GeneralDepthPaper.CoordinateWordJets

@[expose] public section


/-! A real two-parameter multilinear operator is bounded by its actual
coordinate-word evaluations. The proof expands every input vector in the
two coordinate axes; it uses the product sup norm of the parameter space. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
namespace GeneralDepthPaper
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 64

theorem two_parameter_multilinear_norm_bound {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ)
    (A : ContinuousMultilinearMap ℝ (fun _:Fin n=>ℝ×ℝ) F)
    {C : ℝ} (hC : 0≤C)
    (hA : ∀r:Fin n→Fin 2,‖A (fun i=>parameterAxis (r i))‖≤C) :
    ‖A‖≤(2:ℝ)^n*C := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  let c (i : Fin n) (j : Fin 2) : ℝ:=if j=0 then (v i).1 else (v i).2
  have hv : v=(fun i=>∑j:Fin 2,c i j • parameterAxis j) := by
    funext i
    simp [c,parameterAxis,Fin.sum_univ_two]
  have hc (i : Fin n) (j : Fin 2) : ‖c i j‖≤‖v i‖ := by
    fin_cases j
    · exact norm_fst_le (v i)
    · exact norm_snd_le (v i)
  have hterm (r : Fin n→Fin 2) :
      ‖A (fun i=>c i (r i) • parameterAxis (r i))‖≤C*(∏i:Fin n,‖v i‖) := by
    rw [A.map_smul_univ,norm_smul,norm_prod]
    exact (mul_le_mul (Finset.prod_le_prod₀ (fun i _=>norm_nonneg _) (fun i _=>hc i (r i)))
      (hA r) (norm_nonneg _) (Finset.prod_nonneg (fun i _=>norm_nonneg (v i)))).trans_eq (mul_comm _ _)
  calc
    ‖A v‖=‖∑r:Fin n→Fin 2,A (fun i=>c i (r i) • parameterAxis (r i))‖ := by
      conv_lhs => rw [hv]
      rw [A.map_sum]
    _ ≤ ∑r:Fin n→Fin 2,‖A (fun i=>c i (r i) • parameterAxis (r i))‖ := norm_sum_le _ _
    _ ≤ ∑_r:Fin n→Fin 2,C*(∏i:Fin n,‖v i‖) := Finset.sum_le_sum (fun r _=>hterm r)
    _ = ((2:ℝ)^n*C)*(∏i:Fin n,‖v i‖) := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,
        nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
      ring

end GeneralDepthPaper
