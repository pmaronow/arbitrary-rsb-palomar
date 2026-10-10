module

public import GeneralDepthPaper.LogarithmicOverlapThreshold

@[expose] public section


/-! The high-degree primitive evaluated at the actual logarithmic threshold
has uniformly vanishing cost. This is the intermediate-region estimate. -/
noncomputable section
open Set Filter
open scoped Topology
namespace GeneralDepthPaper
set_option maxHeartbeats 1000000

theorem logarithmicOverlapThreshold_gap_bound {p : ℕ} (hp : 2≤p)
    {lam lamhi L : ℝ} (hlam : 0 < lam) (hhi : lam≤lamhi) (hL : 0 < L)
    (hlog : 1≤L*Real.log (p:ℝ)) :
    1-logarithmicOverlapThreshold p lam L≤2*(|Real.log lamhi|+Real.log (p:ℝ))/(p:ℝ) := by
  have hpn : 0 < (p:ℝ) := by exact_mod_cast (show 0<p by omega)
  have hn : 0 < ((p-1:ℕ):ℝ) := by exact_mod_cast (show 0<p-1 by omega)
  have hlogp : 0 < Real.log (p:ℝ) := Real.log_pos (by exact_mod_cast (show 1<p by omega))
  have hratio : 0 < lam*(p:ℝ)/(L*Real.log (p:ℝ)) := by positivity
  have hhi0 : 0 < lamhi := hlam.trans_le hhi
  have hnum : 0≤|Real.log lamhi|+Real.log (p:ℝ) := by positivity
  have hrle : lam*(p:ℝ)/(L*Real.log (p:ℝ))≤lamhi*(p:ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hh:=mul_le_mul_of_nonneg_left hlog (mul_nonneg hhi0.le hpn.le)
    have hl:=mul_le_mul_of_nonneg_right hhi hpn.le
    nlinarith
  have hlle : Real.log (lam*(p:ℝ)/(L*Real.log (p:ℝ)))≤|Real.log lamhi|+Real.log (p:ℝ) := by
    have hh:=Real.log_le_log hratio hrle
    rw [Real.log_mul hhi0.ne' hpn.ne'] at hh
    exact hh.trans (add_le_add (le_abs_self _) le_rfl)
  have he:=Real.add_one_le_exp
    (-Real.log (lam*(p:ℝ)/(L*Real.log (p:ℝ)))/((p-1:ℕ):ℝ))
  have hgap : 1-logarithmicOverlapThreshold p lam L≤
      Real.log (lam*(p:ℝ)/(L*Real.log (p:ℝ)))/((p-1:ℕ):ℝ) := by
    dsimp only [logarithmicOverlapThreshold]
    rw [neg_div] at he
    rw [neg_div]
    linarith
  apply hgap.trans
  apply (div_le_div_of_nonneg_right hlle hn.le).trans
  apply (div_le_div_iff₀ hn hpn).mpr
  have hnat : (p:ℝ)≤2*((p-1:ℕ):ℝ) := by exact_mod_cast (show p≤2*(p-1) by omega)
  nlinarith

def logarithmicTailBudget (lamhi L : ℝ) (p : ℕ) : ℝ :=
  L*Real.log (p:ℝ)*(2*(|Real.log lamhi|+Real.log (p:ℝ))/(p:ℝ)+1/(p:ℝ))

theorem tendsto_logarithmicTailBudget (lamhi L : ℝ) :
    Tendsto (logarithmicTailBudget lamhi L) atTop (𝓝 0) := by
  have h1 : Tendsto (fun p:ℕ=>Real.log (p:ℝ)/(p:ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun p:ℕ=>(Real.log (p:ℝ))^2/(p:ℝ)) atTop (𝓝 0) := by
    simpa only [one_mul,add_zero,Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hh:=(h1.const_mul (2*L*|Real.log lamhi|+L)).add (h2.const_mul (2*L))
  simp only [mul_zero,add_zero] at hh
  apply hh.congr'
  exact .of_forall fun p=>by
    dsimp only [logarithmicTailBudget]
    ring

theorem logarithmic_high_degree_cost_bound {p : ℕ} (hp : 2≤p)
    {lam lamhi L : ℝ} (hlam : 0 < lam) (hhi : lam≤lamhi) (hL : 0 < L)
    (hlog : 1≤L*Real.log (p:ℝ)) (hth : logarithmicOverlapThreshold p lam L≤1) :
    lam*(logarithmicOverlapThreshold p lam L)^(p-1)*
        ((p:ℝ)-((p-1:ℕ):ℝ)*logarithmicOverlapThreshold p lam L)≤
      logarithmicTailBudget lamhi L p := by
  let q:=logarithmicOverlapThreshold p lam L
  have hpn : 0 < (p:ℝ) := by exact_mod_cast (show 0<p by omega)
  have he:=logarithmicOverlapThreshold_power hp hlam hL
  have hnat : ((p-1:ℕ):ℝ)=(p:ℝ)-1 := by
    rw [Nat.cast_sub (by omega),Nat.cast_one]
  have heq : lam*q^(p-1)*((p:ℝ)-((p-1:ℕ):ℝ)*q)=
      L*Real.log (p:ℝ)*(1-q+q/(p:ℝ)) := by
    have hh : lam*q^(p-1)=L*Real.log (p:ℝ)/(p:ℝ) := by
      apply (eq_div_iff hpn.ne').mpr
      convert he using 1 <;> dsimp only [q] <;> ring
    rw [hh,hnat]
    field_simp
    <;> ring
  rw [heq]
  have hgap:=logarithmicOverlapThreshold_gap_bound hp hlam hhi hL hlog
  have hqdiv : q/(p:ℝ)≤1/(p:ℝ) := div_le_div_of_nonneg_right hth hpn.le
  apply mul_le_mul_of_nonneg_left (add_le_add hgap hqdiv)
    (mul_nonneg hL.le (Real.log_nonneg (by exact_mod_cast (show 1≤p by omega))))

end GeneralDepthPaper
