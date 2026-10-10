module

public import GeneralDepthPaper.CutoffComparisonWindow

@[expose] public section


/-! A fixed convex recursion domain for the actual high-degree inputs.
The small input perturbation controls the upper bounds; monotonicity of
the actual added covariance controls the positive variance lower bound. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff BigOperators
namespace GeneralDepthPaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

theorem cutoffVariancePerturbation_nonneg {r : ℕ} (p : ℕ) {qc : ℝ}
    (x : HighDegreeLowerParameter r) (hz : IsAtomicPoint x.1)
    (hc : atomicLocation x.1 (Fin.last r)<qc) (hlam : 0≤x.2.2)
    (i : Fin (r+1)) : 0≤cutoffVariancePerturbation p qc x i := by
  apply mul_nonneg (mul_nonneg hlam (Nat.cast_nonneg _))
  apply sub_nonneg.mpr
  exact pow_le_pow_left₀ (cutoffAtomicNode_mem x.1 hz qc hc i.castSucc).1
    ((cutoffAtomicNode_strictMono x.1 hz qc hc).monotone i.castSucc_lt_succ.le) _

theorem cutoffHighDegreeInput_mem_enlarged_ball (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) {qc Vlo Vhi B : ℝ} (x : CutoffInputParameter r)
    (hz : IsAtomicPoint x.1) (hc : atomicLocation x.1 (Fin.last r)<qc)
    (hlam : 0≤x.2.2.1)
    (hx : cutoffComparisonInput Ξ qc x∈coleHopfRecursionBall (r+1) 1 Vlo Vhi B)
    (he : ‖cutoffHighDegreeInput Ξ p qc x-cutoffComparisonInput Ξ qc x‖≤1) :
    cutoffHighDegreeInput Ξ p qc x∈coleHopfRecursionBall (r+1) 1 Vlo (Vhi+1) (B+1) := by
  have hfirst : ‖(cutoffHighDegreeInput Ξ p qc x).1-
      (cutoffComparisonInput Ξ qc x).1‖≤1 :=
    (norm_fst_le (cutoffHighDegreeInput Ξ p qc x-cutoffComparisonInput Ξ qc x)).trans he
  have hterm : ‖(cutoffHighDegreeInput Ξ p qc x).2-
      (cutoffComparisonInput Ξ qc x).2‖≤1 :=
    (norm_snd_le (cutoffHighDegreeInput Ξ p qc x-cutoffComparisonInput Ξ qc x)).trans he
  refine ⟨fun i => ⟨(hx.1 i).1,?_,?_⟩,?_⟩
  · exact (hx.1 i).2.1.trans (le_add_of_nonneg_right
      (cutoffVariancePerturbation_nonneg p (cutoffVarianceProjection x) hz hc hlam i))
  · have hi : ‖(cutoffHighDegreeInput Ξ p qc x).1 i-
        (cutoffComparisonInput Ξ qc x).1 i‖≤1 :=
      (norm_le_pi_norm _ i).trans hfirst
    have hv : ‖((cutoffHighDegreeInput Ξ p qc x).1 i).2-
        ((cutoffComparisonInput Ξ qc x).1 i).2‖≤1 := (norm_snd_le _).trans hi
    have hh := le_abs_self (((cutoffHighDegreeInput Ξ p qc x).1 i).2-
      ((cutoffComparisonInput Ξ qc x).1 i).2)
    have hbase := (hx.1 i).2.2
    change |((cutoffHighDegreeInput Ξ p qc x).1 i).2-
      ((cutoffComparisonInput Ξ qc x).1 i).2|≤1 at hv
    linarith
  · exact (norm_le_insert (cutoffComparisonInput Ξ qc x).2
      (cutoffHighDegreeInput Ξ p qc x).2).trans
        (add_le_add hx.2 (by simpa only [norm_sub_rev] using hterm))

theorem norm_input_jet_le_of_difference {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : E→F} {x : E} (he : ContDiffAt ℝ ∞ (fun y=>f y-g y) x)
    (hg : ContDiffAt ℝ ∞ g x) (j : ℕ) {D ε : ℝ}
    (hb : ‖iteratedFDeriv ℝ j g x‖≤D)
    (hd : ‖iteratedFDeriv ℝ j (fun y=>f y-g y) x‖≤ε) :
    ContDiffAt ℝ ∞ f x ∧ ‖iteratedFDeriv ℝ j f x‖≤D+ε := by
  have hf : ContDiffAt ℝ ∞ f x := by
    convert he.add hg using 1
    funext y
    exact (sub_add_cancel (f y) (g y)).symm
  refine ⟨hf,?_⟩
  have heq := fun_iteratedFDeriv_sub_apply
    (hf.of_le (show (j:ℕ∞ω)≤∞ by simp)) (hg.of_le (show (j:ℕ∞ω)≤∞ by simp))
  rw [heq] at hd
  exact (norm_le_insert (iteratedFDeriv ℝ j g x) (iteratedFDeriv ℝ j f x)).trans
    (add_le_add hb (by simpa only [norm_sub_rev] using hd))

end GeneralDepthPaper
