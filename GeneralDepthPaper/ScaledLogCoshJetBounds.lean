module

public import GeneralDepthPaper.ScaledLogCoshTerminal
public import GeneralDepthPaper.UniformMassJetBounds
public import GeneralDepthPaper.PositiveResidualJetBounds

@[expose] public section


/-! Every actual mixed mass/spatial derivative of ψ_m is uniformly bounded
on compact positive mass intervals. Positive spatial orders are essential:
ψ_m itself has linear growth. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff Polynomial
namespace GeneralDepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem contDiff_tanh_actual : ContDiff ℝ ∞ Real.tanh := by
  have he : Real.tanh=(fun x:ℝ=>Real.sinh x/Real.cosh x) :=
    funext Real.tanh_eq_sinh_div_cosh
  rw [he]
  exact Real.contDiff_sinh.div Real.contDiff_cosh (fun x=>(Real.cosh_pos x).ne')

theorem contDiff_logCoshJetPolynomial (j : ℕ) :
    ContDiff ℝ ∞ (fun x=>(logCoshJetPolynomial j).eval (Real.tanh x)) := by
  have hp : ContDiff ℝ ∞ (fun x:ℝ=>(logCoshJetPolynomial j).eval x) := by
    simp only [Polynomial.eval_eq_sum_range]
    exact ContDiff.sum fun i _=>contDiff_const.mul (contDiff_id.pow i)
  exact hp.comp contDiff_tanh_actual

theorem sech_sq_exponential_bound (x : ℝ) :
    Paper.sech x^2≤4*Real.exp (-2*|x|) := by
  have hc : Real.exp |x|≤2*Real.cosh x := by
    rw [←Real.cosh_abs,Real.cosh_eq]
    linarith [Real.exp_pos (-|x|)]
  have hcs : (Real.exp |x|)^2≤4*(Real.cosh x)^2 := by
    nlinarith [Real.exp_pos |x|,Real.cosh_pos x]
  have hdiv:=div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤4)
    (sq_pos_of_pos (Real.exp_pos |x|)) hcs
  have he : (Real.exp |x|)^2=Real.exp (2*|x|) := by
    rw [pow_two,←Real.exp_add]
    congr 1
    ring
  rw [he] at hdiv
  rw [Paper.sech,div_pow,one_pow]
  have hsplit : 4/Real.exp (2*|x|)=4*Real.exp (-2*|x|) := by
    rw [show -2*|x|=-(2*|x|) by ring]
    rw [Real.exp_neg]
    ring
  exact (show 1/Real.cosh x^2=4/(4*Real.cosh x^2) by field_simp).le.trans
    (hdiv.trans_eq hsplit)

theorem logCoshJetPolynomial_succ_decay (j : ℕ) (x : ℝ) :
    ‖(logCoshJetPolynomial (j+1)).eval (Real.tanh x)‖≤
      4*‖tanhPolynomialBCF (logCoshJetPolynomial j).derivative‖*Real.exp (-2*|x|) := by
  have hid : 1-Real.tanh x^2=Paper.sech x^2 := by
    linarith [Paper.tanh_sq_add_sech_sq x]
  simp only [logCoshJetPolynomial,Paper.tanhPolynomialDeriv,Polynomial.eval_mul,
    Polynomial.eval_sub,Polynomial.eval_one,Polynomial.eval_pow,Polynomial.eval_X,hid,norm_mul]
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h:=mul_le_mul (BoundedContinuousFunction.norm_coe_le_norm
      (tanhPolynomialBCF (logCoshJetPolynomial j).derivative) x)
    (sech_sq_exponential_bound x) (sq_nonneg _) (norm_nonneg _)
  convert! h using 1 <;> ring

theorem hasDerivAt_logCoshJet_mass (j : ℕ) (m x : ℝ) :
    HasDerivAt (fun a=>(logCoshJetPolynomial j).eval (Real.tanh (a*x)))
      (x*(logCoshJetPolynomial (j+1)).eval (Real.tanh (m*x))) m := by
  have hd:=(Paper.hasDerivAt_tanhPolynomial (logCoshJetPolynomial j) (m*x)).comp m
    ((hasDerivAt_id m).mul_const x)
  convert! hd using 1 <;> simp only [logCoshJetPolynomial] <;> ring

theorem iteratedDeriv_logCoshJet_mass (j k : ℕ) (m x : ℝ) :
    iteratedDeriv k (fun a=>(logCoshJetPolynomial j).eval (Real.tanh (a*x))) m=
      x^k*(logCoshJetPolynomial (j+k)).eval (Real.tanh (m*x)) := by
  induction k generalizing m with
  | zero=>simp
  | succ k ih=>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv k (fun a=>(logCoshJetPolynomial j).eval (Real.tanh (a*x)))=
        fun a=>x^k*(logCoshJetPolynomial (j+k)).eval (Real.tanh (a*x)) := funext fun a=>ih a
    rw [he]
    have hd:=(hasDerivAt_logCoshJet_mass (j+k) m x).const_mul (x^k)
    rw [hd.deriv]
    simp only [pow_succ,Nat.add_assoc]
    ring

theorem logCoshJet_mass_uniform_bound (j k : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∃C:ℝ,0≤C ∧ ∀m≥eps,∀x:ℝ,
      ‖iteratedDeriv k (fun a=>(logCoshJetPolynomial j).eval (Real.tanh (a*x))) m‖≤C := by
  cases k with
  | zero=>
    refine ⟨‖tanhPolynomialBCF (logCoshJetPolynomial j)‖,norm_nonneg _,?_⟩
    intro m hm x
    simpa only [iteratedDeriv_zero,tanhPolynomialBCF_apply] using
      BoundedContinuousFunction.norm_coe_le_norm (tanhPolynomialBCF (logCoshJetPolynomial j)) (m*x)
  | succ k=>
    let A:=4*‖tanhPolynomialBCF (logCoshJetPolynomial (j+k)).derivative‖
    let C:=A*((k+1).factorial:ℝ)/(2*eps)^(k+1)
    refine ⟨C,by dsimp only [C,A]; positivity,?_⟩
    intro m hm x
    have hm0 : 0 < m:=heps.trans_le hm
    rw [iteratedDeriv_logCoshJet_mass,norm_mul,norm_pow,Real.norm_eq_abs]
    have hd:=logCoshJetPolynomial_succ_decay (j+k) (m*x)
    simp only [abs_mul,abs_of_pos hm0] at hd
    have hmon : Real.exp (-2*(m*|x|))≤Real.exp (-(2*eps)*|x|) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hm (abs_nonneg x)])
    have hp:=polynomial_times_exp_bound (k+1) (ε:=2*eps) (c:=0) (u:=|x|)
      (by positivity) le_rfl (abs_nonneg x)
    simp only [zero_add,mul_zero,Real.exp_zero,mul_one] at hp
    have hD:‖(logCoshJetPolynomial (j+(k+1))).eval (Real.tanh (m*x))‖≤
        A*Real.exp (-(2*eps)*|x|) := hd.trans
      (mul_le_mul_of_nonneg_left hmon (by positivity))
    have hh:=mul_le_mul_of_nonneg_left hD (pow_nonneg (abs_nonneg x) (k+1))
    apply hh.trans
    have hh':=mul_le_mul_of_nonneg_left hp (show 0≤A by dsimp only [A]; positivity)
    convert! hh' using 1 <;> ring

def scaledLogCoshPositiveJet (j : ℕ) (m x : ℝ) : ℝ :=
  m^j*(logCoshJetPolynomial j).eval (Real.tanh (m*x))

theorem hasDerivAt_scaledLogCoshPositiveJet (j : ℕ) (m x : ℝ) :
    HasDerivAt (scaledLogCoshPositiveJet j m) (scaledLogCoshPositiveJet (j+1) m x) x := by
  have hd:=((Paper.hasDerivAt_tanhPolynomial (logCoshJetPolynomial j) (m*x)).comp x
    ((hasDerivAt_id x).const_mul m)).const_mul (m^j)
  convert! hd using 1
  simp only [scaledLogCoshPositiveJet,logCoshJetPolynomial,pow_succ,mul_one]
  ring

theorem iteratedDeriv_scaledLogCoshTerminal_spatial (j : ℕ) (m x : ℝ) :
    iteratedDeriv (j+1) (terminalValue (scaledLogCoshTerminal m)) x=scaledLogCoshPositiveJet j m x := by
  induction j generalizing x with
  | zero=>
    rw [iteratedDeriv_one,(hasDerivAt_terminalValue (scaledLogCoshTerminal m) x).deriv,
      terminalJet_scaledLogCoshTerminal_zero]
    simp [scaledLogCoshPositiveJet,logCoshJetPolynomial]
  | succ j ih=>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv (j+1) (terminalValue (scaledLogCoshTerminal m))=
      scaledLogCoshPositiveJet j m := funext fun x=>ih x
    rw [he]
    exact (hasDerivAt_scaledLogCoshPositiveJet j m x).deriv

theorem logCoshJet_mass_uniform_bounds (j N : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∃C:ℝ,0≤C ∧ ∀k≤N,∀m≥eps,∀x:ℝ,
      ‖iteratedDeriv k (fun a=>(logCoshJetPolynomial j).eval (Real.tanh (a*x))) m‖≤C := by
  induction N with
  | zero=>
    obtain ⟨C,hC,hb⟩:=logCoshJet_mass_uniform_bound j 0 heps
    refine ⟨C,hC,?_⟩
    intro k hk
    have hk0 : k=0 := by omega
    subst k
    exact hb
  | succ N ih=>
    obtain ⟨C,hC,hb⟩:=ih
    obtain ⟨D,hD,hd⟩:=logCoshJet_mass_uniform_bound j (N+1) heps
    refine ⟨max C D,hC.trans (le_max_left _ _),?_⟩
    intro k hk m hm x
    by_cases hkn:k≤N
    · exact (hb k hkn m hm x).trans (le_max_left _ _)
    · have hke:k=N+1:=by omega
      subst k
      exact (hd m hm x).trans (le_max_right _ _)

theorem scaledLogCoshJet_mixed_uniform_bound (j k : ℕ) {eps : ℝ} (heps : 0 < eps) (M : ℝ) :
    ∃C:ℝ,0≤C ∧ ∀m∈Icc eps M,∀x:ℝ,
      ‖iteratedDeriv k (fun a=>scaledLogCoshPositiveJet j a x) m‖≤C := by
  obtain ⟨A,hA,ha⟩:=bivariateValue_mass_uniform_bounds (Polynomial.C (Polynomial.X^j)) k eps M
  obtain ⟨B,hB,hb⟩:=logCoshJet_mass_uniform_bounds j k heps
  refine ⟨(2:ℝ)^k*A*B,by positivity,?_⟩
  intro m hm x
  exact norm_iteratedDeriv_mul_le k (contDiff_id.pow j)
    ((contDiff_logCoshJetPolynomial j).comp (contDiff_id.mul contDiff_const))
    (zero_le_one.trans hA) hB
    (fun l hl=>by simpa [bivariateValue] using ha l hl m hm 0 (by norm_num))
    (fun l hl=>hb l hl m hm.1 x)

theorem scaledLogCosh_mixed_uniform_bound (I : Set ℝ) (hI : IsCompact I) (hpos : I⊆Ioi (0:ℝ))
    (j k : ℕ) : ∃C:ℝ,0≤C ∧ ∀m∈I,∀x:ℝ,
      ‖iteratedDeriv k (fun a=>iteratedDeriv (j+1) (terminalValue (scaledLogCoshTerminal a)) x) m‖≤C := by
  by_cases hne:I.Nonempty
  · obtain ⟨eps,hepsI,hmin⟩:=hI.exists_isMinOn hne continuousOn_id
    obtain ⟨M,hMI,hmax⟩:=hI.exists_isMaxOn hne continuousOn_id
    obtain ⟨C,hC,hb⟩:=scaledLogCoshJet_mixed_uniform_bound j k (hpos hepsI) M
    refine ⟨C,hC,?_⟩
    intro m hm x
    simp_rw [iteratedDeriv_scaledLogCoshTerminal_spatial]
    exact hb m ⟨hmin hm,hmax hm⟩ x
  · exact ⟨0,le_rfl,fun m hm=>(hne ⟨m,hm⟩).elim⟩

theorem terminalValue_scaledLogCoshTerminal_all (m x : ℝ) :
    terminalValue (scaledLogCoshTerminal m) x=m⁻¹*Real.log (Real.cosh (m*x)) := by
  by_cases hm : m=0
  · subst m
    have hz : (scaledLogCoshTerminal 0).1.1=0 := by
      simpa only [terminalValue_zero] using terminalValue_scaledLogCoshTerminal_zero 0
    rw [terminalValue,hz]
    change 0+(∫y in (0:ℝ)..x,terminalJet (scaledLogCoshTerminal 0) 0 y)=_
    simp only [terminalJet_scaledLogCoshTerminal_zero,zero_mul,Real.tanh_zero,
      intervalIntegral.integral_zero,zero_add,inv_zero]
  · exact terminalValue_scaledLogCoshTerminal m hm x

theorem scaledLogCosh_literal_mixed_uniform_bound (I : Set ℝ) (hI : IsCompact I)
    (hpos : I⊆Ioi (0:ℝ)) (j k : ℕ) :
    ∃C:ℝ,0≤C ∧ ∀m∈I,∀x:ℝ,
      ‖iteratedDeriv k (fun a=>iteratedDeriv (j+1)
        (fun y=>a⁻¹*Real.log (Real.cosh (a*y))) x) m‖≤C := by
  simpa only [funext (terminalValue_scaledLogCoshTerminal_all _)] using
    scaledLogCosh_mixed_uniform_bound I hI hpos j k

end GeneralDepthPaper
