module

public import GeneralDepthPaper.EndpointRootInputs
public import GeneralDepthPaper.IntervalRootDomain

@[expose] public section


/-! The actual distinguished endpoint contact, chosen as the genuine
monotone implicit root of the actual endpoint deficit. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 64

def distinguishedEndpoint (Ξ : AdmissibleCovariance) {r : ℕ} (p : ℕ) (qc cQ CQ : ℝ) :
    HighDegreeLowerParameter r→ℝ :=
  intervalImplicitRoot (endpointRootEquation Ξ p qc)
    (1-Real.exp (-cQ*(p:ℝ))) (1-Real.exp (-CQ*(p:ℝ)))

def distinguishedEndpointDomain (Ξ : AdmissibleCovariance) {r : ℕ} (p : ℕ)
    (qc cQ CQ : ℝ) : Set (HighDegreeLowerParameter r) :=
  intervalRootDomain (endpointRootEquation Ξ p qc) (endpointRootSmoothDomain Ξ p qc)
    (1-Real.exp (-cQ*(p:ℝ))) (1-Real.exp (-CQ*(p:ℝ)))

theorem endpointStrip_lower_lt_upper {cQ CQ : ℝ} (hCQ : cQ < CQ) (p : ℕ)
    (hp : 0 < p) : 1-Real.exp (-cQ*(p:ℝ)) < 1-Real.exp (-CQ*(p:ℝ)) := by
  have hpos : (0:ℝ) < p := by exact_mod_cast hp
  have H := Real.exp_lt_exp.mpr (show -CQ*(p:ℝ) < -cQ*(p:ℝ) by
    nlinarith [mul_lt_mul_of_pos_right hCQ hpos])
  linarith

theorem isOpen_distinguishedEndpointDomain (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (qc cQ CQ : ℝ) (hCQ : cQ < CQ) (hp : 0 < p) :
    IsOpen (distinguishedEndpointDomain (r:=r) Ξ p qc cQ CQ) :=
  isOpen_intervalRootDomain _ _ (isOpen_endpointRootSmoothDomain Ξ p qc)
    (contDiffOn_endpointRootEquation Ξ p qc) (endpointStrip_lower_lt_upper hCQ p hp)

theorem contDiffOn_distinguishedEndpoint (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (qc cQ CQ : ℝ) (hCQ : cQ < CQ) (hp : 0 < p) :
    ContDiffOn ℝ ∞ (distinguishedEndpoint (r:=r) Ξ p qc cQ CQ)
      (distinguishedEndpointDomain Ξ p qc cQ CQ) :=
  intervalImplicitRoot_smooth_domain _ _ (isOpen_endpointRootSmoothDomain Ξ p qc)
    (contDiffOn_endpointRootEquation Ξ p qc) (endpointStrip_lower_lt_upper hCQ p hp)

theorem distinguishedEndpoint_spec (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (qc cQ CQ : ℝ) (hCQ : cQ < CQ) (hp : 0 < p)
    {theta : HighDegreeLowerParameter r}
    (htheta : theta∈distinguishedEndpointDomain Ξ p qc cQ CQ) :
    distinguishedEndpoint Ξ p qc cQ CQ theta∈
      Ioo (1-Real.exp (-cQ*(p:ℝ))) (1-Real.exp (-CQ*(p:ℝ))) ∧
    endpointRootEquation Ξ p qc (theta,distinguishedEndpoint Ξ p qc cQ CQ theta)=0 ∧
    ContDiffAt ℝ ∞ (distinguishedEndpoint Ξ p qc cQ CQ) theta := by
  have H := intervalImplicitRoot_spec_domain _ _ (isOpen_endpointRootSmoothDomain Ξ p qc)
    (contDiffOn_endpointRootEquation Ξ p qc) (endpointStrip_lower_lt_upper hCQ p hp) htheta
  exact ⟨H.1,H.2,(contDiffOn_distinguishedEndpoint Ξ p qc cQ CQ hCQ hp theta htheta).contDiffAt
    ((isOpen_distinguishedEndpointDomain Ξ p qc cQ CQ hCQ hp).mem_nhds htheta)⟩

theorem distinguishedEndpointDomain_mem_of_inputs (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (qc cQ CQ : ℝ) (theta : HighDegreeLowerParameter r)
    (hfiber : ∀Q∈endpointStrip cQ CQ p,(theta,Q)∈endpointRootSmoothDomain Ξ p qc ∧
      1/2 ≤ deriv (fun q=>endpointRootEquation Ξ p qc (theta,q)) Q)
    (hleft : endpointRootEquation Ξ p qc (theta,1-Real.exp (-cQ*(p:ℝ))) < 0)
    (hright : 0 < endpointRootEquation Ξ p qc (theta,1-Real.exp (-CQ*(p:ℝ)))) :
    theta∈distinguishedEndpointDomain Ξ p qc cQ CQ := by
  refine ⟨?_,hleft,hright⟩
  intro Q hQ
  have H := hfiber Q hQ
  refine ⟨H.1,?_⟩
  change 0 < fderiv ℝ (endpointRootEquation Ξ p qc) (theta,Q) (0,1)
  rw [←interval_partial_derivative_eq _ theta Q
    ((contDiffOn_endpointRootEquation Ξ p qc _ H.1).contDiffAt
      ((isOpen_endpointRootSmoothDomain Ξ p qc).mem_nhds H.1))]
  exact (by norm_num : (0:ℝ) < 1/2).trans_le H.2

theorem distinguished_endpoint_smooth_eventually (Ξ : AdmissibleCovariance) {r : ℕ}
    {K : Set (AtomicPoint r)} (hK : IsCompact K) (hvalid : ∀z∈K,IsAtomicPoint z)
    {e lo hi qc cQ CQ : ℝ} (he : e∈Ioo (0:ℝ) 1) (hlo : 0 < lo) (hLH : lo ≤ hi)
    (hc : qc∈Ioo (0:ℝ) 1) (hcut : ∀z∈K,atomicLocation z (Fin.last r) < qc)
    (hcQ : 0 < cQ) (hclo : cQ < e^2*lo/2) (hChi : hi/2 < CQ) :
    ∀ᶠp:ℕ in atTop,∀heven:Even p,∀theta:HighDegreeLowerParameter r,
      theta.1∈K→theta.2.1∈Icc e 1→theta.2.2∈Icc lo hi→
        theta∈distinguishedEndpointDomain Ξ p qc cQ CQ ∧
        distinguishedEndpoint Ξ p qc cQ CQ theta∈
          Ioo (1-Real.exp (-cQ*(p:ℝ))) (1-Real.exp (-CQ*(p:ℝ))) ∧
        endpointRootEquation Ξ p qc (theta,distinguishedEndpoint Ξ p qc cQ CQ theta)=0 ∧
        ContDiffAt ℝ ∞ (distinguishedEndpoint Ξ p qc cQ CQ) theta := by
  have hCQ : cQ < CQ := by
    have H : e^2*lo ≤ hi := by
      have h := mul_le_mul_of_nonneg_right (show e^2 ≤ 1 by nlinarith [he.1,he.2]) hlo.le
      nlinarith
    linarith
  filter_upwards [endpoint_root_inputs_eventually Ξ hK hvalid he.1 hlo hLH hc hcut hcQ hclo hChi]
    with p hp heven theta hz hm hl
  obtain ⟨hp4,hn,H⟩ := hp.2 heven
  have hi := H theta hz hm hl
  have hdom := distinguishedEndpointDomain_mem_of_inputs Ξ p qc cQ CQ theta hi.1 hi.2.1 hi.2.2
  exact ⟨hdom,distinguishedEndpoint_spec Ξ p qc cQ CQ hCQ (by omega) hdom⟩

end GeneralDepthPaper
