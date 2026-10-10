module

public import DepthPaper.CutoffErrorCoordinateBounds

@[expose] public section


/-! Actual Fréchet derivative operator norms of χ−ψ satisfy the uniform
exponential estimate. All coordinate words are bounded first, then the
two-dimensional multilinear expansion supplies the operator norm. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal BigOperators
namespace DepthPaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

theorem cutoffError_iteratedFDeriv_exponential_bound
    {ε : ℝ} (hε : 0<ε) (n : ℕ) :
    ∃C:ℝ,0<C ∧ ∃D:ℕ,∀m∈Icc ε 1,∀V>1,
      ‖iteratedFDeriv ℝ n (fun p:ℝ×ℝ=>cutoffErrorTerminal p.1 p.2) (m,V)‖≤
        C*V^D*Real.exp (-(ε^2)*V/2) := by
  classical
  let R:=Fin n→Fin 2
  have hx (r:R):=cutoffError_coordinateWordJet_exponential_bound (List.ofFn r) hε
  choose c hc d hb using hx
  let C:ℝ:=1+∑r:R,c r
  let D:ℕ:=∑r:R,d r
  have hC:0<C := by
    have hs:0≤∑r:R,c r:=Finset.sum_nonneg (fun r _=>(hc r).le)
    dsimp only [C]
    linarith
  refine ⟨(2:ℝ)^n*C,by positivity,D,?_⟩
  intro m hm V hV
  have hp:(m,V)∈cutoffErrorDomain:=⟨⟨hε.trans_le hm.1,hm.2.trans_lt (by norm_num)⟩,
    zero_lt_one.trans hV⟩
  let B:=C*V^D*Real.exp (-(ε^2)*V/2)
  have hB:0≤B:=by dsimp only [B];positivity
  have haxes (r:R):
      ‖iteratedFDeriv ℝ n (fun p:ℝ×ℝ=>cutoffErrorTerminal p.1 p.2) (m,V)
        (fun i=>parameterAxis (r i))‖≤B := by
    rw [iteratedFDeriv_axes_eq_coordinateWordJet isOpen_cutoffErrorDomain contDiffOn_cutoffErrorTerminal n r hp]
    have hcr:c r≤C := by
      have hi:=Finset.single_le_sum (fun k (_:k∈(Finset.univ:Finset R))=>(hc k).le)
        (Finset.mem_univ r)
      dsimp only [C]
      linarith
    have hdr:d r≤D:=Finset.single_le_sum (fun k (_:k∈(Finset.univ:Finset R))=>Nat.zero_le _)
      (Finset.mem_univ r)
    have hd:V^(d r)≤V^D := by
      rw [←Real.rpow_natCast,←Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hV.le (by exact_mod_cast hdr)
    exact (hb r m hm V hV).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul hcr hd (by positivity) hC.le) (Real.exp_pos _).le)
  exact (two_parameter_multilinear_norm_bound n _ hB haxes).trans_eq (by dsimp only [B];ring)

end DepthPaper
