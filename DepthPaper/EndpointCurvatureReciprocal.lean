module

public import DepthPaper.EndpointCurvatureJets

@[expose] public section


/-! Genuine inverse jets with a uniform positive curvature lower bound.
The polynomial growth comes from actual covariance derivatives. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 64

theorem norm_iteratedFDeriv_real_inverse_le {a : ℝ} (ha : 1 ≤ a) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y:ℝ=> y⁻¹) a‖ ≤ (j.factorial:ℝ) := by
  have hapos : 0 < a := zero_lt_one.trans_le ha
  have hu : IsUnit a := isUnit_iff_ne_zero.mpr hapos.ne'
  have H := norm_iteratedFDeriv_inverse_le hu.unit j
  have hei : ((hu.unit⁻¹:ℝˣ):ℝ)=a⁻¹ := by
    simpa only [IsUnit.unit_spec,Ring.inverse_eq_inv] using (Ring.inverse_unit hu.unit).symm
  simp only [IsUnit.unit_spec,hei,Ring.inverse_eq_inv'] at H
  have hinv : ‖a⁻¹‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (inv_nonneg.mpr hapos.le)]
    exact (inv_le_one₀ hapos).mpr ha
  exact H.trans ((mul_le_mul_of_nonneg_left
    (pow_le_one₀ (norm_nonneg _) hinv) (Nat.cast_nonneg _)).trans_eq (mul_one _))

theorem norm_iteratedFDeriv_reciprocal_polynomial_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E→ℝ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hx : 1 ≤ f x) (N p : ℕ) (hp : 1 ≤ p)
    (C : ℝ) (hC : 1 ≤ C)
    (hb : ∀i:ℕ,i ≤ N→‖iteratedFDeriv ℝ i f x‖ ≤ C*(p:ℝ)^(N+2)) :
    ∀j:ℕ,j ≤ N→‖iteratedFDeriv ℝ j (fun y=> (f y)⁻¹) x‖ ≤ ((N.factorial:ℝ)^2*C^N)*(p:ℝ)^((N+2)*N) := by
  let D := C*(p:ℝ)^(N+2)
  have hD : 1 ≤ D := by
    exact one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ (by exact_mod_cast hp))
  intro j hj
  have ho : ContDiffAt ℝ ∞ (fun a:ℝ=> a⁻¹) (f x) :=
    contDiffAt_inv ℝ (zero_lt_one.trans_le hx).ne'
  have houter : ∀i:ℕ,i ≤ j→‖iteratedFDeriv ℝ i (fun a:ℝ=> a⁻¹) (f x)‖ ≤ (N.factorial:ℝ) := by
    intro i hi
    exact (norm_iteratedFDeriv_real_inverse_le hx i).trans
      (by exact_mod_cast Nat.factorial_le (hi.trans hj))
  have hinner : ∀i:ℕ,1 ≤ i→i ≤ j→‖iteratedFDeriv ℝ i f x‖ ≤ D^i := by
    intro i hi hij
    exact (hb i (hij.trans hj)).trans (le_self_pow₀ hD (by omega))
  have H := norm_iteratedFDeriv_comp_le_at ho hf j (N.factorial:ℝ) D houter hinner
  change ‖iteratedFDeriv ℝ j (fun y=> (f y)⁻¹) x‖ ≤ _ at H
  apply H.trans
  have hfac : (j.factorial:ℝ) ≤ (N.factorial:ℝ) := by exact_mod_cast Nat.factorial_le hj
  calc
    (j.factorial:ℝ)*(N.factorial:ℝ)*D^j ≤ (N.factorial:ℝ)*(N.factorial:ℝ)*D^N :=
      mul_le_mul (mul_le_mul_of_nonneg_right hfac (Nat.cast_nonneg _))
        (pow_le_pow_right₀ hD hj) (pow_nonneg (zero_le_one.trans hD) _) (by positivity)
    _=((N.factorial:ℝ)^2*C^N)*(p:ℝ)^((N+2)*N) := by
      simp only [D,mul_pow,←pow_mul]
      ring

theorem endpoint_curvature_reciprocal_polynomial_bound (Ξ : AdmissibleCovariance) {r : ℕ}
    {qc lo hi cQ CQ : ℝ} (hc : qc∈Icc (0:ℝ) 1) (hlo : 0 < lo) (hcQ : 0 < cQ)
    (N : ℕ) :
    ∃C:ℝ,1 ≤ C ∧ ∃A:ℕ,∃P:ℕ,4 ≤ P ∧
      ∀p:ℕ,P ≤ p→∀x:CutoffInputParameter r,x.2.2.1∈Icc lo hi→
        x.2.2.2∈endpointStrip cQ CQ p→
        1 ≤ highDegreeSecondExpression Ξ p x.2.2 ∧
        ContDiffAt ℝ ∞ (fun y:CutoffInputParameter r=> (highDegreeSecondExpression Ξ p y.2.2)⁻¹) x ∧
        ∀j:ℕ,j ≤ N→‖iteratedFDeriv ℝ j
          (fun y:CutoffInputParameter r=> (highDegreeSecondExpression Ξ p y.2.2)⁻¹) x‖ ≤ C*(p:ℝ)^A := by
  obtain ⟨D,hD,hb⟩ := highDegreeSecondExpression_full_jet_bound (r:=r) Ξ hc N (L:=hi)
  obtain ⟨P,hP⟩ := eventually_atTop.mp (endpoint_curvature_at_least_one_eventually Ξ hlo (CQ:=CQ) hcQ)
  let C := (N.factorial:ℝ)^2*D^N
  have hC : 1 ≤ C := one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ (by exact_mod_cast Nat.factorial_pos N)) (one_le_pow₀ hD)
  refine ⟨C,hC,(N+2)*N,max P 4,le_max_right _ _,?_⟩
  intro p hp x hl hQ
  have hpx := hP p ((le_max_left _ _).trans hp)
  have hcurv := hpx.2 x.2.2 hl hQ
  have hf : ContDiffAt ℝ ∞ (fun y:CutoffInputParameter r=> highDegreeSecondExpression Ξ p y.2.2) x :=
    (contDiff_highDegreeSecondExpression Ξ p).contDiffAt.comp x endpointPairProjection.contDiff.contDiffAt
  refine ⟨hcurv,hf.inv (zero_lt_one.trans_le hcurv).ne',?_⟩
  exact norm_iteratedFDeriv_reciprocal_polynomial_le hf hcurv N p (by omega) D hD
    (fun i hi=> hb p (by omega) x ⟨hlo.le.trans hl.1,hl.2⟩
      ⟨(endpointStrip_mem_unit hcQ p hQ).1,(endpointStrip_mem_unit hcQ p hQ).2.le⟩ i hi)

end DepthPaper
