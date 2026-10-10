module

public import DepthPaper.CutoffCompositionJets

@[expose] public section


/-! Pure exponential terminal-error bounds and their genuine local
Fréchet composition with the high-degree variance. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
namespace DepthPaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

theorem cutoffError_iteratedFDeriv_pure_exponential_bound
    {ε:ℝ} (hε:0 < ε) (n:ℕ) :
    ∃C:ℝ,0 < C ∧ ∀m∈Icc ε 1,∀V>1,
      ‖iteratedFDeriv ℝ n (fun p:ℝ×ℝ=>cutoffErrorTerminal p.1 p.2) (m,V)‖≤
        C*Real.exp (-(ε^2)*V/4) := by
  obtain ⟨C,hC,D,hb⟩:=cutoffError_iteratedFDeriv_exponential_bound hε n
  let a:=ε^2/4
  have ha:0 < a:=by dsimp only [a];positivity
  refine ⟨C*(D.factorial:ℝ)/a^D,by positivity,?_⟩
  intro m hm V hV
  have hpoly:=polynomial_times_exp_bound D (c:=0) (u:=V) ha le_rfl
    (zero_lt_one.trans hV).le
  simp only [zero_add,mul_zero,Real.exp_zero,mul_one] at hpoly
  have he:Real.exp (-(ε^2)*V/2)=Real.exp (-a*V)*Real.exp (-a*V) := by
    rw [←Real.exp_add];congr 1;dsimp only [a];ring
  apply (hb m hm V hV).trans
  rw [he]
  have hh:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpoly hC.le) (Real.exp_pos (-a*V)).le
  have hexp:Real.exp (-a*V)=Real.exp (-(ε^2)*V/4) := by
    congr 1;dsimp only [a];ring
  rw [hexp] at hh
  rw [hexp]
  convert hh using 1 <;> ring

theorem cutoffError_low_order_pure_exponential_bound
    {ε:ℝ} (hε:0 < ε) (N:ℕ) :
    ∃C:ℝ,0 < C ∧ ∀n≤N,∀m∈Icc ε 1,∀V>1,
      ‖iteratedFDeriv ℝ n (fun p:ℝ×ℝ=>cutoffErrorTerminal p.1 p.2) (m,V)‖≤
        C*Real.exp (-(ε^2)*V/4) := by
  classical
  have hx (i:Fin (N+1)):=cutoffError_iteratedFDeriv_pure_exponential_bound hε i.val
  choose c hc hb using hx
  let C:ℝ:=1+∑i:Fin (N+1),c i
  have hC:0 < C := by
    have hs:=Finset.sum_nonneg (fun i (_:i∈(Finset.univ:Finset (Fin (N+1))))=>(hc i).le)
    dsimp only [C];linarith
  refine ⟨C,hC,?_⟩
  intro n hn m hm V hV
  let i:Fin (N+1):=⟨n,by omega⟩
  have hci:c i≤C := by
    have hi:=Finset.single_le_sum
      (fun k (_:k∈(Finset.univ:Finset (Fin (N+1))))=>(hc k).le) (Finset.mem_univ i)
    dsimp only [C];linarith
  exact (hb i m hm V hV).trans
    (mul_le_mul_of_nonneg_right hci (Real.exp_pos _).le)

theorem cutoffParameterMap_low_order_jet_bound (Ξ:AdmissibleCovariance)
    {qc L:ℝ} (hc:qc∈Icc (0:ℝ) 1) (N:ℕ) :
    ∃B:ℝ,1≤B ∧ ∀p:ℕ,1≤p→∀x:ℝ×(ℝ×ℝ),
      x.2.1∈Icc (0:ℝ) L→x.2.2∈Icc (0:ℝ) 1→∀j,1≤j→j≤N→
      ‖iteratedFDeriv ℝ j (cutoffParameterMap Ξ p qc) x‖≤
        (B*(p:ℝ)^(N+1))^j := by
  classical
  have hx (i:Fin N):=cutoffParameterMap_jet_bound Ξ (L:=L) hc (i.val+1) (by omega)
  choose c hcB hb using hx
  let B:ℝ:=1+∑i:Fin N,c i
  have hB:1≤B := by
    have hs:=Finset.sum_nonneg
      (fun i (_:i∈(Finset.univ:Finset (Fin N)))=>(zero_le_one.trans (hcB i)))
    dsimp only [B];linarith
  refine ⟨B,hB,?_⟩
  intro p hp x hlam hQ j hj hjN
  let i:Fin N:=⟨j-1,by omega⟩
  have hij:i.val+1=j:=by dsimp only [i];omega
  have hci:c i≤B := by
    have hi:=Finset.single_le_sum
      (fun k (_:k∈(Finset.univ:Finset (Fin N)))=>zero_le_one.trans (hcB k))
      (Finset.mem_univ i)
    dsimp only [B];linarith
  have hpow:(p:ℝ)^(j+1)≤(p:ℝ)^(N+1):=
    pow_le_pow_right₀ (by exact_mod_cast hp) (by omega)
  have hbp:1≤B*(p:ℝ)^(N+1) := by
    have hpN:1≤(p:ℝ)^(N+1):=one_le_pow₀ (by exact_mod_cast hp)
    exact hpN.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hB (pow_nonneg (Nat.cast_nonneg p) _))
  have hfirst:=hb i p hp x hlam hQ
  rw [hij] at hfirst
  exact hfirst.trans ((mul_le_mul hci hpow (by positivity) (zero_le_one.trans hB)).trans
    (by simpa only [pow_one] using pow_le_pow_right₀ hbp hj))

theorem cutoffError_local_composition_bound
    {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H:E→ℝ×ℝ) (hH:ContDiff ℝ ∞ H) {x:E}
    {ε C D:ℝ} (hε:0 < ε) {n:ℕ}
    (hm:(H x).1∈Icc ε 1) (hV:1 < (H x).2)
    (hC:∀i,i ≤ n → ‖iteratedFDeriv ℝ i
      (fun p:ℝ×ℝ=>cutoffErrorTerminal p.1 p.2) (H x)‖≤C)
    (hD:∀i,1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i H x‖≤D^i) :
    ‖iteratedFDeriv ℝ n (fun y=>cutoffErrorTerminal (H y).1 (H y).2) x‖≤
      (n.factorial:ℝ)*C*D^n := by
  let U:=H ⁻¹' cutoffErrorDomain
  have hU:IsOpen U:=isOpen_cutoffErrorDomain.preimage hH.continuous
  have hx:x∈U:=⟨⟨hε.trans_le hm.1,hm.2.trans_lt (by norm_num)⟩,zero_lt_one.trans hV⟩
  have hb:=norm_iteratedFDerivWithin_comp_le contDiffOn_cutoffErrorTerminal hH.contDiffOn
    (show (n:ℕ∞ω)≤∞ by simp) isOpen_cutoffErrorDomain.uniqueDiffOn hU.uniqueDiffOn
    (show MapsTo H U cutoffErrorDomain from fun _ hy=>hy) hx
    (fun i hi=>by
      rw [iteratedFDerivWithin_of_isOpen i isOpen_cutoffErrorDomain hx]
      exact hC i hi)
    (fun i hi hin=>by
      rw [iteratedFDerivWithin_of_isOpen i hU hx]
      exact hD i hi hin)
  rw [iteratedFDerivWithin_of_isOpen n hU hx] at hb
  exact hb

end DepthPaper
