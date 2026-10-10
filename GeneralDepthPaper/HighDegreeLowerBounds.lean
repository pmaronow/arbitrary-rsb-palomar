module

public import GeneralDepthPaper.HighDegreeJetBounds
public import GeneralDepthPaper.HighDegreeCorrection
public import GeneralDepthPaper.UniformDerivativeCalculus

@[expose] public section


/-! Uniform mixed derivatives of the explicit lower covariance remainder.
Weights, locations, total mass and the high-spin coefficient are genuine
independent coordinates in the smooth polynomial extension. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff BigOperators
namespace GeneralDepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem norm_iteratedFDeriv_mul_power_cutoff (f : E→ℝ) (hf : ContDiff ℝ ∞ f)
    (L : E→L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (p j : ℕ) (hp : 1 ≤ p)
    (x : E) {qc C : ℝ} (hc : qc∈Icc (0:ℝ) 1) (hx : L x∈Icc (0:ℝ) qc)
    (hC : 0 ≤ C) (hb : ∀i:ℕ,i ≤ j → ‖iteratedFDeriv ℝ i f x‖ ≤ C) :
    ‖iteratedFDeriv ℝ j (fun y => f y*(L y)^p) x‖ ≤
      (2:ℝ)^j*C*(p:ℝ)^j*qc^(p-j) := by
  have hg : ContDiff ℝ ∞ (fun y => (L y)^p) := L.contDiff.pow p
  apply (norm_iteratedFDeriv_mul_le hf hg x (by simp)).trans
  have hs : (∑i∈Finset.range (j+1),(j.choose i:ℝ)*C*((p:ℝ)^j*qc^(p-j)))=
      (2:ℝ)^j*C*(p:ℝ)^j*qc^(p-j) := by
    rw [←Finset.sum_mul,←Finset.sum_mul,←Nat.cast_sum,Nat.sum_range_choose,Nat.cast_pow,Nat.cast_ofNat]
    ring
  rw [←hs]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ j := by have hh:=Finset.mem_range.mp hi;omega
  have hpow := (norm_iteratedFDeriv_comp_contraction L hL (fun y => y^p)
    (contDiff_id.pow p) (j-i) x).trans (norm_iteratedDeriv_pow_cutoff p (j-i) hc.1 hx)
  have hqc : qc^(p-(j-i)) ≤ qc^(p-j) := pow_right_anti₀ hc.1 hc.2 (by omega)
  have hgB := hpow.trans (mul_le_mul
    (pow_le_pow_right₀ (by exact_mod_cast hp : (1:ℝ) ≤ p) (Nat.sub_le _ _))
    hqc (pow_nonneg hc.1 _)
    (pow_nonneg (Nat.cast_nonneg _) _))
  have HH := mul_le_mul (hb i hi') hgB (norm_nonneg _) hC
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left HH (Nat.cast_nonneg (j.choose i))

abbrev HighDegreeLowerParameter (r : ℕ) := AtomicPoint r × (ℝ × ℝ)

def atomicLocationLowerCLM {r : ℕ} (i : Fin (r+1)) : HighDegreeLowerParameter r→L[ℝ] ℝ :=
  Fin.cases 0 (fun j => (ContinuousLinearMap.proj j).comp
    ((ContinuousLinearMap.fst ℝ (Fin r→ℝ) (Fin r→ℝ)).comp
      (ContinuousLinearMap.fst ℝ (AtomicPoint r) (ℝ×ℝ)))) i

@[simp] theorem atomicLocationLowerCLM_apply {r : ℕ} (i : Fin (r+1))
    (x : HighDegreeLowerParameter r) : atomicLocationLowerCLM i x=atomicLocation x.1 i := by
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [atomicLocationLowerCLM,atomicLocation]

theorem norm_atomicLocationLowerCLM_le_one {r : ℕ} (i : Fin (r+1)) :
    ‖atomicLocationLowerCLM i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [atomicLocationLowerCLM_apply,one_mul]
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [atomicLocation_zero,norm_zero];exact norm_nonneg _
  · rw [atomicLocation_succ]
    exact (norm_le_pi_norm _ j).trans ((norm_fst_le x.1).trans (norm_fst_le x))

def lowerCovariancePolynomial {r : ℕ} (p : ℕ) (qc : ℝ)
    (x : HighDegreeLowerParameter r) : ℝ :=
  x.2.2*x.2.1/2*(((p:ℝ)-1)*
    (∑i:Fin (r+1),atomicWeight x.1 i*(atomicLocation x.1 i)^p)-(p:ℝ)*qc^(p-1))

theorem lowerCovariancePolynomial_eq {r : ℕ} (Ξ : AdmissibleCovariance)
    (p : ℕ) (hp : 4 ≤ p) (he : Even p) (hn : p∉Ξ.degrees)
    (z : AtomicPoint r) (m qc lam : ℝ) (hlam : 0 < lam) :
    lowerCovarianceRemainder Ξ (Ξ.addHighDegree p hp he hn lam hlam) z m qc=
      lowerCovariancePolynomial p qc (z,(m,lam)) :=
  lowerCovarianceRemainder_highDegree Ξ p hp he hn lam hlam z m qc


theorem BoundedSmoothOn.finite_jet_bound {f : E→ℝ} {s : Set E}
    (hf : BoundedSmoothOn f s) (j : ℕ) :
    ∃C:ℝ,0 ≤ C ∧ ∀x∈s,∀i:ℕ,i ≤ j → ‖iteratedFDeriv ℝ i f x‖ ≤ C := by
  choose C hC hb using hf.bound
  refine ⟨∑i∈Finset.range (j+1),C i,Finset.sum_nonneg (fun i _ => hC i),?_⟩
  intro x hx i hi
  exact (hb i x hx).trans (Finset.single_le_sum (fun k _ => hC k)
    (Finset.mem_range.mpr (by omega)))

def lowerAtomAmplitude {r : ℕ} (i : Fin (r+1)) (x : HighDegreeLowerParameter r) : ℝ :=
  x.2.2*x.2.1/2*atomicWeight x.1 i

def lowerCutoffAmplitude {r : ℕ} (x : HighDegreeLowerParameter r) : ℝ := x.2.2*x.2.1/2

theorem contDiff_lowerAtomAmplitude {r : ℕ} (i : Fin (r+1)) :
    ContDiff ℝ ∞ (lowerAtomAmplitude i) :=
  (show ContDiff ℝ ∞ (fun x : HighDegreeLowerParameter r => x.2.2*x.2.1/2) by fun_prop).mul
    ((contDiff_atomicWeight i).comp contDiff_fst)

theorem contDiff_lowerCutoffAmplitude {r : ℕ} :
    ContDiff ℝ ∞ (lowerCutoffAmplitude (r:=r)) := by unfold lowerCutoffAmplitude;fun_prop

theorem lowerCovariancePolynomial_sum {r : ℕ} (p : ℕ) (qc : ℝ) :
    lowerCovariancePolynomial (r:=r) p qc=(fun x =>
      ((p:ℝ)-1) • (∑i:Fin (r+1),lowerAtomAmplitude i x*(atomicLocationLowerCLM i x)^p)-
        ((p:ℝ)*qc^(p-1)) • lowerCutoffAmplitude x) := by
  funext x
  simp only [lowerCovariancePolynomial,lowerAtomAmplitude,lowerCutoffAmplitude,
    atomicLocationLowerCLM_apply,smul_eq_mul]
  simp_rw [mul_assoc]
  rw [←Finset.mul_sum]
  ring

theorem lowerCovariancePolynomial_mixed_exponential_bound {r : ℕ} {qc : ℝ}
    (hc : qc∈Ioo (0:ℝ) 1) (B : ℝ) (j : ℕ) :
    ∃C c:ℝ,0 ≤ C ∧ 0 < c ∧ ∀p:ℕ,1 ≤ p → j ≤ p →
      ∀x:HighDegreeLowerParameter r,x∈closedBall 0 B →
        (∀i:Fin (r+1),atomicLocation x.1 i∈Icc (0:ℝ) qc) →
        ‖iteratedFDeriv ℝ j (lowerCovariancePolynomial p qc) x‖ ≤
          C*(p:ℝ)^(j+1)*Real.exp (-c*(p:ℝ)) := by
  have hamps (i : Fin (r+1)) := (BoundedSmoothOn.of_compact (isCompact_closedBall 0 B)
    (fun x _ => (contDiff_lowerAtomAmplitude i).contDiffAt)).finite_jet_bound j
  choose C hC hb using hamps
  obtain ⟨D,hD,hd⟩ := (BoundedSmoothOn.of_compact (isCompact_closedBall (0:HighDegreeLowerParameter r) B)
    (fun x _ => (contDiff_lowerCutoffAmplitude (r:=r)).contDiffAt)).finite_jet_bound j
  let A : ℝ := D+∑i:Fin (r+1),C i
  have hA : 0 ≤ A := add_nonneg hD (Finset.sum_nonneg (fun i _ => hC i))
  have hCA (i : Fin (r+1)) : C i ≤ A := by
    have H := Finset.single_le_sum (fun k (_:k∈Finset.univ) => hC k) (Finset.mem_univ i)
    dsimp only [A]
    linarith
  have hDA : D ≤ A := le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hC i))
  let K : ℝ := (r+1:ℕ)*(2:ℝ)^j*A
  refine ⟨K*qc^(- (j:ℤ))+A*qc⁻¹,-Real.log qc,?_,
    neg_pos.mpr (Real.log_neg hc.1 hc.2),?_⟩
  · have hK : 0 ≤ K := by dsimp only [K];positivity
    exact add_nonneg (mul_nonneg hK (le_of_lt (zpow_pos hc.1 _)))
      (mul_nonneg hA (inv_nonneg.mpr hc.1.le))
  intro p hp hj x hx hloc
  have hterm (i : Fin (r+1)) :
      ‖iteratedFDeriv ℝ j (fun y => lowerAtomAmplitude i y*(atomicLocationLowerCLM i y)^p) x‖ ≤
        (2:ℝ)^j*A*(p:ℝ)^j*qc^(p-j) :=
    norm_iteratedFDeriv_mul_power_cutoff _ (contDiff_lowerAtomAmplitude i) _
      (norm_atomicLocationLowerCLM_le_one i) p j hp x ⟨hc.1.le,hc.2.le⟩
      (by simpa only [atomicLocationLowerCLM_apply] using hloc i) hA
      (fun k hk => (hb i x hx k hk).trans (hCA i))
  have hsum : ‖iteratedFDeriv ℝ j (fun y =>
      ∑i:Fin (r+1),lowerAtomAmplitude i y*(atomicLocationLowerCLM i y)^p) x‖ ≤
      K*(p:ℝ)^j*qc^(p-j) := by
    rw [iteratedFDeriv_fun_sum_apply (fun i _ =>
      (((contDiff_lowerAtomAmplitude i).mul ((atomicLocationLowerCLM i).contDiff.pow p)).of_le
        (show (j:ℕ∞ω) ≤ ∞ by simp)).contDiffAt)]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun i _ => hterm i)).trans_eq ?_)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    dsimp only [K]
    ring
  have hg : ContDiff ℝ ∞ (fun y =>
      ∑i:Fin (r+1),lowerAtomAmplitude i y*(atomicLocationLowerCLM i y)^p) :=
    ContDiff.sum (fun i _ => (contDiff_lowerAtomAmplitude i).mul ((atomicLocationLowerCLM i).contDiff.pow p))
  rw [lowerCovariancePolynomial_sum,fun_iteratedFDeriv_sub_apply
    ((hg.const_smul _).of_le (show (j:ℕ∞ω) ≤ ∞ by simp)).contDiffAt
    (((contDiff_lowerCutoffAmplitude (r:=r)).const_smul _).of_le (show (j:ℕ∞ω) ≤ ∞ by simp)).contDiffAt,
    iteratedFDeriv_const_smul_apply' (hg.of_le (show (j:ℕ∞ω) ≤ ∞ by simp)).contDiffAt,
    iteratedFDeriv_const_smul_apply'
      ((contDiff_lowerCutoffAmplitude (r:=r)).of_le (show (j:ℕ∞ω) ≤ ∞ by simp)).contDiffAt]
  have hpR : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : 0 ≤ (p:ℝ) := Nat.cast_nonneg _
  have hpm : ‖(p:ℝ)-1‖ ≤ p := by rw [Real.norm_of_nonneg (by linarith)];linarith
  have hncut : ‖(p:ℝ)*qc^(p-1)‖=(p:ℝ)*qc^(p-1) :=
    Real.norm_of_nonneg (mul_nonneg hp0 (pow_nonneg hc.1.le _))
  have HH : ‖((p:ℝ)-1) • iteratedFDeriv ℝ j (fun y =>
        ∑i:Fin (r+1),lowerAtomAmplitude i y*(atomicLocationLowerCLM i y)^p) x-
      ((p:ℝ)*qc^(p-1)) • iteratedFDeriv ℝ j (lowerCutoffAmplitude (r:=r)) x‖ ≤
      (p:ℝ)*(K*(p:ℝ)^j*qc^(p-j))+(p:ℝ)*qc^(p-1)*A :=
    (norm_sub_le _ _).trans (add_le_add
    (by rw [norm_smul];exact mul_le_mul hpm hsum (norm_nonneg _) hp0)
    (by
      rw [norm_smul,hncut]
      exact mul_le_mul_of_nonneg_left ((hd x hx j le_rfl).trans hDA)
        (mul_nonneg hp0 (pow_nonneg hc.1.le _))))
  have hlast : p-1=p-(1:ℕ) := rfl
  conv at HH =>
    rhs
    rw [pow_cutoff_exponential hc.1 p j hj,pow_cutoff_exponential hc.1 p 1 hp]
  have hpp : (p:ℝ) ≤ (p:ℝ)^(j+1) := le_self_pow₀ hpR (by omega)
  have hnonneg : 0 ≤ A*qc^(-(1:ℤ))*Real.exp (Real.log qc*(p:ℝ)) :=
    mul_nonneg (mul_nonneg hA (le_of_lt (zpow_pos hc.1 _))) (Real.exp_nonneg _)
  have hcut := mul_le_mul_of_nonneg_left hpp hnonneg
  have hcq : qc^(-(1:ℤ))=qc⁻¹ := by simp
  simp only [Nat.cast_one,zpow_neg_one] at HH hcut
  calc
    _ ≤ _ := HH
    _ ≤ K*qc^(- (j:ℤ))*(p:ℝ)^(j+1)*Real.exp (Real.log qc*(p:ℝ))+
        A*qc⁻¹*(p:ℝ)^(j+1)*Real.exp (Real.log qc*(p:ℝ)) := by
      rw [pow_succ]
      rw [pow_succ] at hcut
      nlinarith [hcut]
    _ = _ := by ring

end GeneralDepthPaper
