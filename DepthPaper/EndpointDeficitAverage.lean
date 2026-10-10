module

public import DepthPaper.MassAverageSmooth
public import DepthPaper.EndpointDeficitIdentity
public import DepthPaper.LowerRecursionLemma

@[expose] public section


/-! Actual smooth averaged mixed derivative and its exponentially small
jets. These statements include the mass-one endpoint. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 64

def endpointDeficitAverage (Ξ : AdmissibleCovariance) {r : ℕ} (p : ℕ) (qc : ℝ) :
    CutoffInputParameter r→ℝ := massAverage (lowerRemainderMassEndpointDerivative Ξ p qc)

theorem contDiffOn_endpointDeficitAverage (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (qc : ℝ) :
    ContDiffOn ℝ ∞ (endpointDeficitAverage (r:=r) Ξ p qc)
      (cutoffInputSmoothDomain Ξ p qc) :=
  contDiffOn_massAverage (isOpen_cutoffInputSmoothDomain Ξ p qc)
    (contDiffOn_lowerRemainderMassEndpointDerivative Ξ p qc)
    (fun _ ht _ hx=> massInterpolation_mem_smoothDomain Ξ p qc hx ht)

theorem massInterpolation_mass_window {r : ℕ} {e : ℝ} {x : CutoffInputParameter r}
    (hx : x.2.1∈Icc e 1) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    (massInterpolation t x).2.1∈Icc e 1 := by
  dsimp only [massInterpolation]
  constructor
  · nlinarith [hx.1,mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr ht.2)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) ht.1]

theorem endpoint_deficit_average_exponential_bound (Ξ : AdmissibleCovariance) {r : ℕ}
    {K : Set (AtomicPoint r)} (hK : IsCompact K) (hvalid : ∀z∈K,IsAtomicPoint z)
    {e lo hi qc cQ CQ : ℝ} (he : 0 < e) (hlo : 0 < lo) (hLH : lo ≤ hi)
    (hc : qc∈Ioo (0:ℝ) 1) (hcut : ∀z∈K,atomicLocation z (Fin.last r) < qc)
    (hcQ : 0 < cQ) (N : ℕ) :
    ∃C:ℝ,0 < C ∧ ∃A:ℕ,∃c:ℝ,0 < c ∧ ∃P:ℕ,1 ≤ P ∧
      ∀p:ℕ,P ≤ p→∀x:CutoffInputParameter r,x.1∈K→x.2.1∈Icc e 1→
        x.2.2.1∈Icc lo hi→x.2.2.2∈endpointStrip cQ CQ p→
        0 < endpointVarianceExpression Ξ p qc x.2.2 ∧
        ContDiffAt ℝ ∞ (endpointDeficitAverage Ξ p qc) x ∧
        ∀j:ℕ,j ≤ N→‖iteratedFDeriv ℝ j (endpointDeficitAverage Ξ p qc) x‖ ≤ C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) := by
  obtain ⟨C,hC,A,c,hcpos,P,hP,hb⟩ := lower_recursion_error_exponential_bound
    Ξ hK hvalid he hlo hLH hc hcut hcQ (N+2)
  obtain ⟨P2,hP2⟩ := eventually_atTop.mp (endpointStrip_above_cutoff_eventually (CQ:=CQ) hc.2 hcQ)
  refine ⟨C,hC,A,c,hcpos,max P P2,hP.trans (le_max_left _ _),?_⟩
  intro p hp x hx hm hl hQ
  have hp1 := (le_max_left P P2).trans hp
  obtain ⟨hf,hjb⟩ := hb p hp1 x hx hm hl hQ
  have hcQx : qc < x.2.2.2 := hP2 p ((le_max_right _ _).trans hp) _ hQ
  have hW : 0 < endpointVarianceExpression Ξ p qc x.2.2 := by
    have hfirst := sub_pos.mpr (Ξ.first_strictMonoOn hc.1.le (hc.1.trans hcQx).le hcQx)
    have hpow := pow_le_pow_left₀ hc.1.le hcQx.le (p-1)
    dsimp only [endpointVarianceExpression]
    exact add_pos_of_pos_of_nonneg hfirst
      (mul_nonneg (mul_nonneg (hlo.le.trans hl.1) (Nat.cast_nonneg _)) (sub_nonneg.mpr hpow))
  have hdom : x∈cutoffInputSmoothDomain Ξ p qc :=
    cutoffInputSmoothDomain_mem Ξ p x (hvalid x.1 hx) (hcut x.1 hx)
      ⟨he.trans_le hm.1,hm.2.trans_lt (by norm_num)⟩ (hlo.le.trans hl.1)
      hW
  refine ⟨hW,(contDiffOn_endpointDeficitAverage Ξ p qc x hdom).contDiffAt
    ((isOpen_cutoffInputSmoothDomain Ξ p qc).mem_nhds hdom),?_⟩
  intro j hj
  apply norm_iteratedFDeriv_massAverage_le (isOpen_cutoffInputSmoothDomain Ξ p qc)
    (contDiffOn_lowerRemainderMassEndpointDerivative Ξ p qc)
    (fun _ ht _ hy=> massInterpolation_mem_smoothDomain Ξ p qc hy ht) j hdom
  intro t ht
  obtain ⟨hft,hbt⟩ := hb p hp1 (massInterpolation t x) hx
    (massInterpolation_mass_window hm ht) hl hQ
  exact (norm_iteratedFDeriv_lowerRemainderMassEndpointDerivative_le Ξ p qc hft j).trans
    (hbt (j+2) (by omega))

theorem endpointDeficitFromRemainder_eq_average (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (qc : ℝ) (x : CutoffInputParameter r) :
    endpointDeficitFromRemainder Ξ p qc x=
      -2/highDegreeSecondExpression Ξ p x.2.2*endpointDeficitAverage Ξ p qc x := by
  rw [endpointDeficitFromRemainder,endpointDeficitAverage,massAverage_eq_intervalIntegral]
  rfl

end DepthPaper
