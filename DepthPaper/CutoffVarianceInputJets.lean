module

public import DepthPaper.CutoffInputJetCalculus
public import DepthPaper.CutoffRecursionRegularity

@[expose] public section


/-! Actual finite variance-input perturbations below the cutoff. Every
Fréchet order has a uniform degree-polynomial exponential estimate. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff BigOperators
namespace DepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

def cutoffVariancePerturbation {r : ℕ} (p : ℕ) (qc : ℝ)
    (x : HighDegreeLowerParameter r) (i : Fin (r+1)) : ℝ :=
  x.2.2*(p:ℝ)*((cutoffAtomicNode x.1 qc i.succ)^(p-1)-
    (cutoffAtomicNode x.1 qc i.castSucc)^(p-1))

def cutoffStepsHighDegreeExtension {r : ℕ} (Ξ : AdmissibleCovariance) (p : ℕ) (qc : ℝ)
    (x : HighDegreeLowerParameter r) : Fin (r+1)→ℝ×ℝ := fun i =>
  ((cutoffRecursionSteps Ξ x.1 x.2.1 qc i).1,
    (cutoffRecursionSteps Ξ x.1 x.2.1 qc i).2+cutoffVariancePerturbation p qc x i)

 theorem cutoffStepsHighDegreeExtension_eq {r : ℕ} (Ξ : AdmissibleCovariance)
    (p : ℕ) (hp : 4 ≤ p) (he : Even p) (hn : p∉Ξ.degrees)
    (x : HighDegreeLowerParameter r) (hlam : 0 < x.2.2) (qc : ℝ) :
    cutoffStepsHighDegreeExtension Ξ p qc x=
      cutoffRecursionSteps (Ξ.addHighDegree p hp he hn x.2.2 hlam) x.1 x.2.1 qc := by
  funext i
  simp only [cutoffStepsHighDegreeExtension,cutoffRecursionSteps,
    AdmissibleCovariance.addHighDegree_first,cutoffVariancePerturbation]
  congr 1
  ring

 theorem contDiff_cutoffVariancePerturbation {r : ℕ} (p : ℕ) (qc : ℝ) (i : Fin (r+1)) :
    ContDiff ℝ ∞ (fun x : HighDegreeLowerParameter r => cutoffVariancePerturbation p qc x i) := by
  have hn (j : Fin (r+2)) := (contDiff_cutoffAtomicNode qc j).comp
    (contDiff_fst (E:=AtomicPoint r) (F:=ℝ×ℝ))
  exact (show ContDiff ℝ ∞ (fun x : HighDegreeLowerParameter r => x.2.2*(p:ℝ)) by fun_prop).mul
    ((hn i.succ |>.pow (p-1)).sub (hn i.castSucc |>.pow (p-1)))

 theorem norm_iteratedFDeriv_amplitude_cutoffNode_pow {r : ℕ}
    (f : HighDegreeLowerParameter r→ℝ) (hf : ContDiff ℝ ∞ f)
    (p j : ℕ) (hp : 1 ≤ p) (x : HighDegreeLowerParameter r)
    {qc C : ℝ} (hc : qc∈Icc (0:ℝ) 1)
    (hloc : ∀i:Fin (r+1),atomicLocation x.1 i∈Icc (0:ℝ) qc)
    (hC : 0 ≤ C) (hb : ∀i:ℕ,i ≤ j → ‖iteratedFDeriv ℝ i f x‖ ≤ C)
    (i : Fin (r+2)) :
    ‖iteratedFDeriv ℝ j (fun y => f y*(cutoffAtomicNode y.1 qc i)^p) x‖ ≤
      (2:ℝ)^j*C*(p:ℝ)^j*qc^(p-j) := by
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp only [cutoffAtomicNode_last]
    have he : (fun y : HighDegreeLowerParameter r => f y*qc^p)=fun y => qc^p • f y := by
      funext y;simp only [smul_eq_mul];ring
    rw [he,iteratedFDeriv_const_smul_apply' (hf.of_le (show (j:ℕ∞ω) ≤ ∞ by simp)).contDiffAt,
      norm_smul,Real.norm_of_nonneg (pow_nonneg hc.1 _)]
    have hqc : qc^p ≤ qc^(p-j) := pow_right_anti₀ hc.1 hc.2 (Nat.sub_le _ _)
    have hpj : (1:ℝ) ≤ (p:ℝ)^j := one_le_pow₀ (by exact_mod_cast hp)
    have htwo : (1:ℝ) ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
    calc
      _ ≤ qc^(p-j)*C := mul_le_mul hqc (hb j le_rfl) (norm_nonneg _) (pow_nonneg hc.1 _)
      _ ≤ (2:ℝ)^j*C*(p:ℝ)^j*qc^(p-j) := by
        have HH := mul_le_mul htwo hpj (by norm_num) (pow_nonneg (by norm_num) j)
        have H := mul_le_mul_of_nonneg_left HH (mul_nonneg hC (pow_nonneg hc.1 (p-j)))
        nlinarith
  · simp only [cutoffAtomicNode_castSucc]
    simpa only [atomicLocationLowerCLM_apply] using norm_iteratedFDeriv_mul_power_cutoff f hf
      (atomicLocationLowerCLM k) (norm_atomicLocationLowerCLM_le_one k) p j hp x hc
      (by simpa only [atomicLocationLowerCLM_apply] using hloc k) hC hb

 theorem cutoffVariancePerturbation_mixed_exponential_bound {r : ℕ} {qc : ℝ}
    (hc : qc∈Ioo (0:ℝ) 1) (B : ℝ) (j : ℕ) :
    ∃C c:ℝ,0 ≤ C ∧ 0 < c ∧ ∀p:ℕ,2 ≤ p → j+1 ≤ p →
      ∀x:HighDegreeLowerParameter r,x∈closedBall 0 B →
      (∀i:Fin (r+1),atomicLocation x.1 i∈Icc (0:ℝ) qc) → ∀i:Fin (r+1),
      ‖iteratedFDeriv ℝ j (fun y => cutoffVariancePerturbation p qc y i) x‖ ≤
        C*(p:ℝ)^(j+1)*Real.exp (-c*(p:ℝ)) := by
  let f : HighDegreeLowerParameter r→ℝ := fun x => x.2.2
  have hf : ContDiff ℝ ∞ f := by fun_prop
  obtain ⟨D,hD,hd⟩ := (BoundedSmoothOn.of_compact (isCompact_closedBall 0 B)
    (fun x _ => hf.contDiffAt)).finite_jet_bound j
  refine ⟨2*(2:ℝ)^j*D*qc^(- ((j+1):ℤ)),-Real.log qc,
    mul_nonneg (mul_nonneg (by positivity) hD) (le_of_lt (zpow_pos hc.1 _)),
    neg_pos.mpr (Real.log_neg hc.1 hc.2),?_⟩
  intro p hp hj x hx hloc i
  have hnode (k : Fin (r+2)) := norm_iteratedFDeriv_amplitude_cutoffNode_pow f hf
    (p-1) j (by omega) x ⟨hc.1.le,hc.2.le⟩ hloc hD (fun k hk => hd x hx k hk) k
  have hn (k : Fin (r+2)) : ContDiff ℝ ∞
      (fun y : HighDegreeLowerParameter r => f y*(cutoffAtomicNode y.1 qc k)^(p-1)) :=
    hf.mul (((contDiff_cutoffAtomicNode qc k).comp contDiff_fst).pow (p-1))
  have he : (fun y : HighDegreeLowerParameter r => cutoffVariancePerturbation p qc y i)=
      fun y => (p:ℝ) • (f y*(cutoffAtomicNode y.1 qc i.succ)^(p-1)-
        f y*(cutoffAtomicNode y.1 qc i.castSucc)^(p-1)) := by
    funext y;dsimp only [cutoffVariancePerturbation,f];simp only [smul_eq_mul];ring
  rw [he,iteratedFDeriv_const_smul_apply'
    (((hn i.succ).sub (hn i.castSucc)).of_le (show (j:ℕ∞ω) ≤ ∞ by simp)).contDiffAt,
    norm_smul,Real.norm_of_nonneg (show 0 ≤ (p:ℝ) from Nat.cast_nonneg _),
    fun_iteratedFDeriv_sub_apply
      ((hn i.succ).of_le (show (j:ℕ∞ω) ≤ ∞ by simp)).contDiffAt
      ((hn i.castSucc).of_le (show (j:ℕ∞ω) ≤ ∞ by simp)).contDiffAt]
  have H := (norm_sub_le _ _).trans (add_le_add (hnode i.succ) (hnode i.castSucc))
  have hpow : ((p-1:ℕ):ℝ)^j ≤ (p:ℝ)^j :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le p 1) j
  have H' : ‖iteratedFDeriv ℝ j (fun y => f y*(cutoffAtomicNode y.1 qc i.succ)^(p-1)) x-
      iteratedFDeriv ℝ j (fun y => f y*(cutoffAtomicNode y.1 qc i.castSucc)^(p-1)) x‖ ≤
      2*(2:ℝ)^j*D*(p:ℝ)^j*qc^(p-(j+1)) := by
    have hs : p-1-j=p-(j+1) := by omega
    rw [hs] at H
    have Hb := mul_le_mul_of_nonneg_left hpow
      (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) j) hD)
        (pow_nonneg hc.1.le (p-(j+1))))
    nlinarith
  rw [pow_cutoff_exponential hc.1 p (j+1) hj] at H'
  have H'' := mul_le_mul_of_nonneg_left H' (show 0 ≤ (p:ℝ) from Nat.cast_nonneg _)
  simp only [Nat.cast_add,Nat.cast_one] at H'' ⊢
  convert H'' using 1 <;> rw [pow_succ] <;> ring


theorem cutoffStepsDifference_mixed_exponential_bound {r : ℕ} (Ξ : AdmissibleCovariance)
    {qc : ℝ} (hc : qc∈Ioo (0:ℝ) 1) (B : ℝ) (j : ℕ) :
    ∃C c:ℝ,0 ≤ C ∧ 0 < c ∧ ∀p:ℕ,2 ≤ p → j+1 ≤ p →
      ∀x:HighDegreeLowerParameter r,x∈closedBall 0 B →
      (∀i:Fin (r+1),atomicLocation x.1 i∈Icc (0:ℝ) qc) →
      ‖iteratedFDeriv ℝ j (fun y => cutoffStepsHighDegreeExtension Ξ p qc y-
        cutoffRecursionSteps Ξ y.1 y.2.1 qc) x‖ ≤
        C*(p:ℝ)^(j+1)*Real.exp (-c*(p:ℝ)) := by
  obtain ⟨C,c,hC,hc',hb⟩ := cutoffVariancePerturbation_mixed_exponential_bound (r:=r) hc B j
  refine ⟨C,c,hC,hc',fun p hp hj x hx hloc => ?_⟩
  have he : (fun y : HighDegreeLowerParameter r => cutoffStepsHighDegreeExtension Ξ p qc y-
      cutoffRecursionSteps Ξ y.1 y.2.1 qc)=
      (fun y => fun i : Fin (r+1) => ((0:ℝ),cutoffVariancePerturbation p qc y i)) := by
    funext y i
    apply Prod.ext <;> simp [cutoffStepsHighDegreeExtension]
  rw [he]
  have hs : ContDiff ℝ ∞ (fun y : HighDegreeLowerParameter r =>
      fun i : Fin (r+1) => ((0:ℝ),cutoffVariancePerturbation p qc y i)) := by
    rw [contDiff_pi]
    intro i
    exact contDiff_const.prodMk (contDiff_cutoffVariancePerturbation p qc i)
  have hM : 0 ≤ C*(p:ℝ)^(j+1)*Real.exp (-c*(p:ℝ)) := by positivity
  apply norm_iteratedFDeriv_pi_le hs.contDiffAt j hM
  intro i
  apply norm_iteratedFDeriv_prod_le contDiffAt_const
    (contDiff_cutoffVariancePerturbation p qc i).contDiffAt j ?_ (hb p hp hj x hx hloc i)
  cases j with
  | zero => simpa only [norm_iteratedFDeriv_zero,norm_zero] using hM
  | succ j => simpa only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero] using hM


theorem cutoffStepsDifference_low_order_exponential_bound {r : ℕ} (Ξ : AdmissibleCovariance)
    {qc : ℝ} (hc : qc∈Ioo (0:ℝ) 1) (B : ℝ) (N : ℕ) :
    ∃C c:ℝ,0 ≤ C ∧ 0 < c ∧ ∀p:ℕ,N+2 ≤ p →
      ∀x:HighDegreeLowerParameter r,x∈closedBall 0 B →
      (∀i:Fin (r+1),atomicLocation x.1 i∈Icc (0:ℝ) qc) → ∀j:ℕ,j ≤ N →
      ‖iteratedFDeriv ℝ j (fun y => cutoffStepsHighDegreeExtension Ξ p qc y-
        cutoffRecursionSteps Ξ y.1 y.2.1 qc) x‖ ≤
        C*(p:ℝ)^(N+1)*Real.exp (-c*(p:ℝ)) := by
  have hh (i : Fin (N+1)) := cutoffStepsDifference_mixed_exponential_bound (r:=r) Ξ hc B i
  choose C c hC hc' hb using hh
  let D : ℝ := ∑i:Fin (N+1),C i
  let a : ℝ := Finset.univ.inf' Finset.univ_nonempty c
  have hD : 0 ≤ D := Finset.sum_nonneg (fun i _ => hC i)
  have ha : 0 < a := by exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun i _ => hc' i)
  refine ⟨D,a,hD,ha,fun p hp x hx hloc j hj => ?_⟩
  let i : Fin (N+1) := ⟨j,by omega⟩
  have H := hb i p (by omega) (by dsimp only [i];omega) x hx hloc
  have hCD : C i ≤ D := Finset.single_le_sum (fun k _ => hC k) (Finset.mem_univ i)
  have hpp : (p:ℝ)^(j+1) ≤ (p:ℝ)^(N+1) :=
    pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ p by omega)) (by omega)
  have hac : a ≤ c i := Finset.inf'_le c (Finset.mem_univ i)
  have he : Real.exp (-c i*(p:ℝ)) ≤ Real.exp (-a*(p:ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hac (Nat.cast_nonneg p)]
  exact H.trans (mul_le_mul (mul_le_mul hCD hpp (pow_nonneg (Nat.cast_nonneg _) _) hD)
    he (Real.exp_pos _).le (mul_nonneg hD (pow_nonneg (Nat.cast_nonneg _) _)))

end DepthPaper
