module

public import DepthPaper.EndpointDeficitLemma

@[expose] public section


/-! The literal endpoint contact equation in the lower parameter chart,
and its genuine positive endpoint derivative on the thin strip. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 64

def cutoffParameterAssembly {r : ℕ} :
    (HighDegreeLowerParameter r×ℝ)→L[ℝ]CutoffInputParameter r :=
  let Z := (ContinuousLinearMap.fst ℝ (AtomicPoint r) (ℝ×ℝ)).comp
    (ContinuousLinearMap.fst ℝ (HighDegreeLowerParameter r) ℝ)
  let M := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    ((ContinuousLinearMap.snd ℝ (AtomicPoint r) (ℝ×ℝ)).comp
      (ContinuousLinearMap.fst ℝ (HighDegreeLowerParameter r) ℝ))
  let L := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
    ((ContinuousLinearMap.snd ℝ (AtomicPoint r) (ℝ×ℝ)).comp
      (ContinuousLinearMap.fst ℝ (HighDegreeLowerParameter r) ℝ))
  Z.prod (M.prod (L.prod (ContinuousLinearMap.snd ℝ (HighDegreeLowerParameter r) ℝ)))

theorem cutoffParameterAssembly_apply {r : ℕ} (w : HighDegreeLowerParameter r×ℝ) :
    cutoffParameterAssembly w=(w.1.1,(w.1.2.1,(w.1.2.2,w.2))) := rfl

theorem norm_cutoffParameterAssembly_le {r : ℕ} : ‖cutoffParameterAssembly (r:=r)‖ ≤ 1 := by
  apply (cutoffParameterAssembly (r:=r)).opNorm_le_bound zero_le_one
  intro x
  rw [cutoffParameterAssembly_apply,one_mul]
  simp only [Prod.norm_def,max_assoc]
  exact le_rfl

def endpointRootEquation (Ξ : AdmissibleCovariance) {r : ℕ} (p : ℕ) (qc : ℝ)
    (w : HighDegreeLowerParameter r×ℝ) : ℝ :=
  w.2-1+endpointDeficitFromRemainder Ξ p qc (cutoffParameterAssembly w)

def endpointRootSmoothDomain (Ξ : AdmissibleCovariance) {r : ℕ} (p : ℕ) (qc : ℝ) :
    Set (HighDegreeLowerParameter r×ℝ) :=
  cutoffParameterAssembly ⁻¹' endpointDeficitSmoothDomain Ξ p qc

theorem isOpen_endpointRootSmoothDomain (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (qc : ℝ) : IsOpen (endpointRootSmoothDomain (r:=r) Ξ p qc) :=
  (isOpen_endpointDeficitSmoothDomain Ξ p qc).preimage cutoffParameterAssembly.continuous

theorem contDiffOn_endpointRootEquation (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (qc : ℝ) : ContDiffOn ℝ ∞ (endpointRootEquation (r:=r) Ξ p qc)
      (endpointRootSmoothDomain Ξ p qc) :=
  (contDiff_snd.sub contDiff_const).contDiffOn.add
    ((contDiffOn_endpointDeficitFromRemainder Ξ p qc).comp
      cutoffParameterAssembly.contDiff.contDiffOn (fun _ h=>h))

theorem hasDerivAt_endpointRootEquation_endpoint (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (qc : ℝ) (theta : HighDegreeLowerParameter r) (Q : ℝ)
    (hmem : (theta,Q)∈endpointRootSmoothDomain Ξ p qc) :
    HasDerivAt (fun q=>endpointRootEquation Ξ p qc (theta,q))
      (1+fderiv ℝ (endpointDeficitFromRemainder Ξ p qc)
        (cutoffParameterAssembly (theta,Q)) lowerEndpointDirection) Q := by
  have hA := (contDiffOn_endpointDeficitFromRemainder Ξ p qc _ hmem).contDiffAt
    ((isOpen_endpointDeficitSmoothDomain Ξ p qc).mem_nhds hmem)
  have hcurve : HasDerivAt (fun q:ℝ=>cutoffParameterAssembly (theta,q))
      lowerEndpointDirection Q :=
    (hasDerivAt_const Q theta.1).prodMk ((hasDerivAt_const Q theta.2.1).prodMk
      ((hasDerivAt_const Q theta.2.2).prodMk (hasDerivAt_id Q)))
  exact ((hasDerivAt_id Q).sub_const 1).add
    (by simpa only [Function.comp_def] using
      ((hA.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt Q hcurve))

theorem endpointRootEquation_derivative_ge_half (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (qc : ℝ) (theta : HighDegreeLowerParameter r) (Q : ℝ)
    (hmem : (theta,Q)∈endpointRootSmoothDomain Ξ p qc)
    (hb : ‖iteratedFDeriv ℝ 1 (endpointDeficitFromRemainder Ξ p qc)
      (cutoffParameterAssembly (theta,Q))‖ ≤ 1/2) :
    1/2 ≤ deriv (fun q=>endpointRootEquation Ξ p qc (theta,q)) Q := by
  rw [(hasDerivAt_endpointRootEquation_endpoint Ξ p qc theta Q hmem).deriv]
  have hd := (fderiv ℝ (endpointDeficitFromRemainder Ξ p qc)
    (cutoffParameterAssembly (theta,Q))).le_opNorm (lowerEndpointDirection (r:=r))
  rw [norm_lowerEndpointDirection,mul_one,←norm_iteratedFDeriv_one] at hd
  have h := hd.trans hb
  have hneg := (abs_le.mp (show |fderiv ℝ (endpointDeficitFromRemainder Ξ p qc)
    (cutoffParameterAssembly (theta,Q)) lowerEndpointDirection| ≤ 1/2 by
      simpa only [Real.norm_eq_abs] using h)).1
  linarith

theorem endpointRootSmoothDomain_mem (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (qc : ℝ) (theta : HighDegreeLowerParameter r) (Q : ℝ)
    (hz : IsAtomicPoint theta.1) (hcut : atomicLocation theta.1 (Fin.last r) < qc)
    (hm : theta.2.1∈Ioo (0:ℝ) 2) (hlam : 0 ≤ theta.2.2)
    (hc : 0 ≤ qc) (hQ : qc < Q) : (theta,Q)∈endpointRootSmoothDomain Ξ p qc := by
  have hQ0 : 0 < Q := hc.trans_lt hQ
  have hW : 0 < endpointVarianceExpression Ξ p qc (theta.2.2,Q) := by
    exact add_pos_of_pos_of_nonneg
      (sub_pos.mpr (Ξ.first_strictMonoOn hc hQ0.le hQ))
      (mul_nonneg (mul_nonneg hlam (Nat.cast_nonneg _))
        (sub_nonneg.mpr (pow_le_pow_left₀ hc hQ.le (p-1))))
  have hcurv : 0 < highDegreeSecondExpression Ξ p (theta.2.2,Q) :=
    add_pos_of_pos_of_nonneg (Ξ.second_pos hQ0)
      (mul_nonneg (mul_nonneg (mul_nonneg hlam (Nat.cast_nonneg _))
        (Nat.cast_nonneg _)) (pow_nonneg hQ0.le _))
  exact ⟨cutoffInputSmoothDomain_mem Ξ p (cutoffParameterAssembly (theta,Q))
    hz hcut hm hlam hW,hcurv.ne'⟩

end DepthPaper
