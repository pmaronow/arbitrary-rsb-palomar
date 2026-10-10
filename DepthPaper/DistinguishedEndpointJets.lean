module

public import DepthPaper.DistinguishedEndpointContact
public import DepthPaper.ImplicitRootThirdJetBounds

@[expose] public section


/-! Actual exponentially small derivatives of the distinguished contact.
The small implicit correction estimates are applied to the true cutoff
deficit on its proved open smooth domain. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 64

def endpointRootCorrection (Ξ : AdmissibleCovariance) {r : ℕ} (p : ℕ) (qc : ℝ) :
    HighDegreeLowerParameter r×ℝ→ℝ :=
  endpointDeficitFromRemainder Ξ p qc ∘ cutoffParameterAssembly

theorem contDiffOn_endpointRootCorrection (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (qc : ℝ) : ContDiffOn ℝ ∞ (endpointRootCorrection (r:=r) Ξ p qc)
      (endpointRootSmoothDomain Ξ p qc) :=
  (contDiffOn_endpointDeficitFromRemainder Ξ p qc).comp
    cutoffParameterAssembly.contDiff.contDiffOn (fun _ h=>h)

theorem norm_endpointRootCorrection_jet_le (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (qc : ℝ) {w : HighDegreeLowerParameter r×ℝ}
    (hw : w∈endpointRootSmoothDomain Ξ p qc) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (endpointRootCorrection Ξ p qc) w‖ ≤
      ‖iteratedFDeriv ℝ j (endpointDeficitFromRemainder Ξ p qc) (cutoffParameterAssembly w)‖ :=
  norm_iteratedFDeriv_comp_CLM_contraction cutoffParameterAssembly norm_cutoffParameterAssembly_le
    ((contDiffOn_endpointDeficitFromRemainder Ξ p qc).contDiffAt
      ((isOpen_endpointDeficitSmoothDomain Ξ p qc).mem_nhds hw)) j

theorem distinguishedEndpoint_three_jet_bound (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (qc cQ CQ : ℝ) (hCQ : cQ < CQ) (hp : 0 < p)
    {theta : HighDegreeLowerParameter r}
    (htheta : theta∈distinguishedEndpointDomain Ξ p qc cQ CQ)
    {ε : ℝ} (hε : 0 ≤ ε) (hsmall : ε ≤ 1/2)
    (hb : ∀i:ℕ,1 ≤ i→i ≤ 3→
      ‖iteratedFDeriv ℝ i (endpointDeficitFromRemainder Ξ p qc)
        (cutoffParameterAssembly (theta,distinguishedEndpoint Ξ p qc cQ CQ theta))‖ ≤ ε) :
    ∀i:ℕ,1 ≤ i→i ≤ 3→
      ‖iteratedFDeriv ℝ i (distinguishedEndpoint Ξ p qc cQ CQ) theta‖ ≤ 8*ε := by
  have hs := distinguishedEndpoint_spec Ξ p qc cQ CQ hCQ hp htheta
  have hmem := (htheta.1 _ (Ioo_subset_Icc_self hs.1)).1
  have hA : ContDiffAt ℝ ∞ (endpointRootCorrection Ξ p qc)
      (theta,distinguishedEndpoint Ξ p qc cQ CQ theta) :=
    (contDiffOn_endpointRootCorrection Ξ p qc).contDiffAt
      ((isOpen_endpointRootSmoothDomain Ξ p qc).mem_nhds hmem)
  have hlocal : ∀ᶠu in 𝓝 theta,distinguishedEndpoint Ξ p qc cQ CQ u=
      1-endpointRootCorrection Ξ p qc (u,distinguishedEndpoint Ξ p qc cQ CQ u) := by
    filter_upwards [(isOpen_distinguishedEndpointDomain Ξ p qc cQ CQ hCQ hp).mem_nhds htheta]
      with u hu
    have hz := (distinguishedEndpoint_spec Ξ p qc cQ CQ hCQ hp hu).2.1
    dsimp only [endpointRootEquation] at hz
    change distinguishedEndpoint Ξ p qc cQ CQ u=
      1-endpointDeficitFromRemainder Ξ p qc
        (cutoffParameterAssembly (u,distinguishedEndpoint Ξ p qc cQ CQ u))
    linarith
  have hAb : ∀i:ℕ,1 ≤ i→i ≤ 3→
      ‖iteratedFDeriv ℝ i (endpointRootCorrection Ξ p qc)
        (theta,distinguishedEndpoint Ξ p qc cQ CQ theta)‖ ≤ ε :=
    fun i hi hj=>(norm_endpointRootCorrection_jet_le Ξ p qc hmem i).trans (hb i hi hj)
  have h12 := implicit_correction_first_second_jet_bound hε hsmall hA hs.2.2 hlocal
    (hAb 1 le_rfl (by omega)) (hAb 2 (by omega) (by omega))
  have h3 := implicit_correction_third_jet_bound hε hsmall hA hs.2.2 hlocal hAb
  intro i hi hj
  interval_cases i
  · exact h12.1.trans (by nlinarith)
  · exact h12.2.trans (by nlinarith)
  · exact h3

theorem distinguished_endpoint_derivatives_exponential_bound (Ξ : AdmissibleCovariance)
    {r : ℕ} {K : Set (AtomicPoint r)} (hK : IsCompact K)
    (hvalid : ∀z∈K,IsAtomicPoint z) {e lo hi qc cQ CQ : ℝ}
    (he : e∈Ioo (0:ℝ) 1) (hlo : 0 < lo) (hLH : lo ≤ hi)
    (hc : qc∈Ioo (0:ℝ) 1) (hcut : ∀z∈K,atomicLocation z (Fin.last r) < qc)
    (hcQ : 0 < cQ) (hclo : cQ < e^2*lo/2) (hChi : hi/2 < CQ) :
    ∃C:ℝ,0 < C ∧ ∃A:ℕ,∃c:ℝ,0 < c ∧
      ∀ᶠp:ℕ in atTop,∀heven:Even p,∀theta:HighDegreeLowerParameter r,
        theta.1∈K→theta.2.1∈Icc e 1→theta.2.2∈Icc lo hi→
        ∀i:ℕ,1 ≤ i→i ≤ 3→
          ‖iteratedFDeriv ℝ i (distinguishedEndpoint Ξ p qc cQ CQ) theta‖ ≤
            C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) := by
  obtain ⟨C,hC,A,c,hcpos,P,hP,H⟩ := endpoint_deficit_crude_derivative_bound
    Ξ hK hvalid he.1 hlo hLH hc hcut hcQ (CQ:=CQ) 3
  have hCQ : cQ < CQ := by
    have hpow : e^2*lo ≤ hi := by
      have hh := mul_le_mul_of_nonneg_right (show e^2 ≤ 1 by nlinarith [he.1,he.2]) hlo.le
      nlinarith
    linarith
  refine ⟨8*C,by positivity,A,c,hcpos,?_⟩
  filter_upwards [eventually_ge_atTop P,
    distinguished_endpoint_smooth_eventually Ξ hK hvalid he hlo hLH hc hcut hcQ hclo hChi,
    (tendsto_nat_polynomial_exp C c A hcpos).eventually
      (Iio_mem_nhds (by norm_num : (0:ℝ) < 1/2))]
      with p hp hs hsmall heven theta hz hm hl i hi hj
  have hr := hs heven theta hz hm hl
  have hstrip : distinguishedEndpoint Ξ p qc cQ CQ theta∈endpointStrip cQ CQ p :=
    Ioo_subset_Icc_self hr.2.1
  have hjets := H p hp (cutoffParameterAssembly
    (theta,distinguishedEndpoint Ξ p qc cQ CQ theta)) hz hm hl hstrip
  have hb := distinguishedEndpoint_three_jet_bound Ξ p qc cQ CQ hCQ (by omega)
    hr.1 (by positivity : 0 ≤ C*(p:ℝ)^A*Real.exp (-c*(p:ℝ))) hsmall.le
      (fun j _ hj=>hjets.2 j hj) i hi hj
  convert hb using 1 <;> ring

end DepthPaper
