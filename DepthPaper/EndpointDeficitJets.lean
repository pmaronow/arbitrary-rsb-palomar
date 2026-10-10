module

public import DepthPaper.EndpointDeficitAverage
public import DepthPaper.EndpointCurvatureReciprocal
public import DepthPaper.ProductJetBounds

@[expose] public section


/-! Exponentially small genuine endpoint-deficit jets, including the
mass-one boundary, derived from the actual remainder identity. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 64

theorem endpointDeficitFromRemainder_eq_product (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (qc : ℝ) : endpointDeficitFromRemainder (r:=r) Ξ p qc=
      (fun x=> (-2:ℝ) • ((highDegreeSecondExpression Ξ p x.2.2)⁻¹*endpointDeficitAverage Ξ p qc x)) := by
  funext x
  rw [endpointDeficitFromRemainder_eq_average,smul_eq_mul,div_eq_mul_inv]
  ring

theorem endpoint_deficit_crude_derivative_bound (Ξ : AdmissibleCovariance) {r : ℕ}
    {K : Set (AtomicPoint r)} (hK : IsCompact K) (hvalid : ∀z∈K,IsAtomicPoint z)
    {e lo hi qc cQ CQ : ℝ} (he : 0 < e) (hlo : 0 < lo) (hLH : lo ≤ hi)
    (hc : qc∈Ioo (0:ℝ) 1) (hcut : ∀z∈K,atomicLocation z (Fin.last r) < qc)
    (hcQ : 0 < cQ) (N : ℕ) :
    ∃C:ℝ,0 < C ∧ ∃A:ℕ,∃c:ℝ,0 < c ∧ ∃P:ℕ,4 ≤ P ∧
      ∀p:ℕ,P ≤ p→∀x:CutoffInputParameter r,x.1∈K→x.2.1∈Icc e 1→
        x.2.2.1∈Icc lo hi→x.2.2.2∈endpointStrip cQ CQ p→
        ContDiffAt ℝ ∞ (endpointDeficitFromRemainder Ξ p qc) x ∧
        ∀j:ℕ,j ≤ N→‖iteratedFDeriv ℝ j (endpointDeficitFromRemainder Ξ p qc) x‖ ≤ C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) := by
  obtain ⟨C1,hC1,A1,c,hcpos,P1,hP1,h1⟩ := endpoint_deficit_average_exponential_bound
    Ξ hK hvalid he hlo hLH hc hcut hcQ N
  obtain ⟨C2,hC2,A2,P2,hP2,h2⟩ := endpoint_curvature_reciprocal_polynomial_bound
    (r:=r) Ξ ⟨hc.1.le,hc.2.le⟩ hlo (CQ:=CQ) hcQ N
  refine ⟨2*(2:ℝ)^N*C2*C1,by positivity,A2+A1,c,hcpos,max P1 P2,
    hP2.trans (le_max_right _ _),?_⟩
  intro p hp x hx hm hl hQ
  obtain ⟨_,ha,haj⟩ := h1 p ((le_max_left _ _).trans hp) x hx hm hl hQ
  obtain ⟨_,hi,hij⟩ := h2 p ((le_max_right _ _).trans hp) x hl hQ
  have hs : ContDiffAt ℝ ∞ (fun y:CutoffInputParameter r=> (highDegreeSecondExpression Ξ p y.2.2)⁻¹*endpointDeficitAverage Ξ p qc y) x := hi.mul ha
  rw [endpointDeficitFromRemainder_eq_product]
  refine ⟨hs.const_smul _,?_⟩
  intro j hj
  rw [iteratedFDeriv_const_smul_apply' (hs.of_le (by simp)),norm_smul]
  norm_num only [Real.norm_eq_abs,abs_neg,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have H := norm_iteratedFDeriv_mul_bound_at hi ha j
    (C2*(p:ℝ)^A2) (C1*(p:ℝ)^A1*Real.exp (-c*(p:ℝ)))
      (by positivity) (by positivity) (fun i hi=> hij i (hi.trans hj))
      (fun i hi=> haj i (hi.trans hj))
  apply (mul_le_mul_of_nonneg_left H (by norm_num : (0:ℝ) ≤ 2)).trans
  have hpow : (2:ℝ)^j ≤ (2:ℝ)^N := pow_le_pow_right₀ (by norm_num) hj
  calc
    2*((2:ℝ)^j*(C2*(p:ℝ)^A2)*(C1*(p:ℝ)^A1*Real.exp (-c*(p:ℝ)))) ≤ 2*((2:ℝ)^N*(C2*(p:ℝ)^A2)*(C1*(p:ℝ)^A1*Real.exp (-c*(p:ℝ)))) := by gcongr
    _=(2*(2:ℝ)^N*C2*C1)*(p:ℝ)^(A2+A1)*Real.exp (-c*(p:ℝ)) := by
      rw [pow_add]
      ring

end DepthPaper
