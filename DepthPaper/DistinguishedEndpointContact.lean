module

public import DepthPaper.DistinguishedEndpoint

@[expose] public section


/-! The chosen smooth scalar root is the unique actual Parisi contact in
the manuscript's endpoint strip, with the literal two-sided scale. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 64

def distinguishedOverlap (Ξ : AdmissibleCovariance) {r : ℕ} (p : ℕ)
    (qc cQ CQ : ℝ) (theta : HighDegreeLowerParameter r) : Overlap :=
  projIcc 0 1 zero_le_one (distinguishedEndpoint Ξ p qc cQ CQ theta)

theorem distinguishedOverlap_coe (Ξ : AdmissibleCovariance) {r : ℕ} (p : ℕ)
    (qc cQ CQ : ℝ) (theta : HighDegreeLowerParameter r)
    (hunit : distinguishedEndpoint Ξ p qc cQ CQ theta∈Icc (0:ℝ) 1) :
    (distinguishedOverlap Ξ p qc cQ CQ theta:ℝ)=
      distinguishedEndpoint Ξ p qc cQ CQ theta := by
  exact congrArg Subtype.val (projIcc_of_mem zero_le_one hunit)

theorem distinguishedEndpoint_unique_closed (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (qc cQ CQ : ℝ) (hCQ : cQ < CQ) (hp : 0 < p)
    {theta : HighDegreeLowerParameter r}
    (htheta : theta∈distinguishedEndpointDomain Ξ p qc cQ CQ)
    {Q : ℝ} (hQ : Q∈endpointStrip cQ CQ p)
    (hzero : endpointRootEquation Ξ p qc (theta,Q)=0) :
    distinguishedEndpoint Ξ p qc cQ CQ theta=Q := by
  have hslice : ∀q∈endpointStrip cQ CQ p,
      ContDiffAt ℝ ∞ (fun r=>endpointRootEquation Ξ p qc (theta,r)) q := by
    intro q hq
    exact ((contDiffOn_endpointRootEquation Ξ p qc _ (htheta.1 q hq).1).contDiffAt
      ((isOpen_endpointRootSmoothDomain Ξ p qc).mem_nhds (htheta.1 q hq).1)).comp q
        (contDiffAt_const.prodMk contDiffAt_id)
  have hder : ∀q∈endpointStrip cQ CQ p,
      0 < deriv (fun r=>endpointRootEquation Ξ p qc (theta,r)) q := by
    intro q hq
    exact intervalRootDomain_partial_pos _ _ (isOpen_endpointRootSmoothDomain Ξ p qc)
      (contDiffOn_endpointRootEquation Ξ p qc) htheta hq
  have hneqleft : Q≠1-Real.exp (-cQ*(p:ℝ)) := by
    intro h
    rw [h] at hzero
    linarith [htheta.2.1]
  have hneqright : Q≠1-Real.exp (-CQ*(p:ℝ)) := by
    intro h
    rw [h] at hzero
    linarith [htheta.2.2]
  exact intervalImplicitRoot_unique _ (endpointStrip_lower_lt_upper hCQ p hp) theta
    hslice htheta.2.1 htheta.2.2 hder
      ⟨lt_of_le_of_ne hQ.1 (Ne.symm hneqleft),lt_of_le_of_ne hQ.2 hneqright⟩ hzero

theorem distinguished_endpoint_contact_eventually (Ξ : AdmissibleCovariance) {r : ℕ}
    {K : Set (AtomicPoint r)} (hK : IsCompact K) (hvalid : ∀z∈K,IsAtomicPoint z)
    {e lo hi qc cQ CQ : ℝ} (he : e∈Ioo (0:ℝ) 1) (hlo : 0 < lo) (hLH : lo ≤ hi)
    (hc : qc∈Ioo (0:ℝ) 1) (hcut : ∀z∈K,atomicLocation z (Fin.last r) < qc)
    (hcQ : 0 < cQ) (hclo : cQ < e^2*lo/2) (hChi : hi/2 < CQ) :
    ∃b:ℝ,0 < b ∧ ∃D:ℝ,0 < D ∧
      ∀ᶠp:ℕ in atTop,4 ≤ p ∧ ∀heven:Even p,∃hp:4 ≤ p,∃hn:p∉Ξ.degrees,
        ∀theta:HighDegreeLowerParameter r,∀hz:theta.1∈K,
          theta.2.1∈Icc e 1→∀hlam:theta.2.2∈Icc lo hi,
          let Ψ := Ξ.addHighDegree p hp heven hn theta.2.2 (hlo.trans_le hlam.1)
          let Q := distinguishedOverlap Ξ p qc cQ CQ theta
          (Q:ℝ)=distinguishedEndpoint Ξ p qc cQ CQ theta ∧
          (Q:ℝ)∈Ioo (1-Real.exp (-cQ*(p:ℝ))) (1-Real.exp (-CQ*(p:ℝ))) ∧
          Gamma Ψ (twoLevelMeasure theta.1 (hvalid _ hz) theta.2.1 Q) Q=(Q:ℝ) ∧
          (∀T:Overlap,(T:ℝ)∈endpointStrip cQ CQ p→
            Gamma Ψ (twoLevelMeasure theta.1 (hvalid _ hz) theta.2.1 T) T=(T:ℝ)→T=Q) ∧
          b*(p:ℝ)^(-(1/2:ℝ))*Real.exp (-theta.2.1^2*theta.2.2*(p:ℝ)/2) ≤ 1-(Q:ℝ) ∧
          1-(Q:ℝ) ≤ D*(p:ℝ)^(-(1/2:ℝ))*Real.exp (-theta.2.1^2*theta.2.2*(p:ℝ)/2) ∧
          ContDiffAt ℝ ∞ (distinguishedEndpoint Ξ p qc cQ CQ) theta := by
  obtain ⟨C,hC,A,c,hcpos,b,hb,D,hD,P,hP,H⟩ := endpoint_deficit
    Ξ r K hK hvalid e lo hi qc cQ CQ he.1 hlo hLH hc hcut hcQ
  have hCQ : cQ < CQ := by
    have hpow : e^2*lo ≤ hi := by
      have h := mul_le_mul_of_nonneg_right (show e^2 ≤ 1 by nlinarith [he.1,he.2]) hlo.le
      nlinarith
    linarith
  refine ⟨b,hb,D,hD,?_⟩
  filter_upwards [eventually_ge_atTop P,
    distinguished_endpoint_smooth_eventually Ξ hK hvalid he hlo hLH hc hcut hcQ hclo hChi,
    endpointStrip_above_cutoff_eventually (CQ:=CQ) hc.2 hcQ]
      with p hp hs hcutoff
  refine ⟨hP.trans hp,?_⟩
  intro heven
  obtain ⟨hp4,hn,hdata⟩ := H p hp heven
  refine ⟨hp4,hn,?_⟩
  intro theta hz hm hl
  have hroot := hs heven theta hz hm hl
  let Q := distinguishedOverlap Ξ p qc cQ CQ theta
  have hqstrip : distinguishedEndpoint Ξ p qc cQ CQ theta∈endpointStrip cQ CQ p :=
    ⟨hroot.2.1.1.le,hroot.2.1.2.le⟩
  have hqeq : (Q:ℝ)=distinguishedEndpoint Ξ p qc cQ CQ theta :=
    distinguishedOverlap_coe Ξ p qc cQ CQ theta
      ⟨(endpointStrip_mem_unit hcQ p hqstrip).1,(endpointStrip_mem_unit hcQ p hqstrip).2.le⟩
  have hQstrip : (Q:ℝ)∈endpointStrip cQ CQ p := by rw [hqeq];exact hqstrip
  have hd := hdata theta.1 hz theta.2.1 hm theta.2.2 hl Q hQstrip
  let Ψ := Ξ.addHighDegree p hp4 heven hn theta.2.2 (hlo.trans_le hl.1)
  have hcontact : Gamma Ψ (twoLevelMeasure theta.1 (hvalid _ hz) theta.2.1 Q) Q=(Q:ℝ) := by
    have hz0 := hroot.2.2.1
    rw [←hqeq] at hz0
    dsimp only [endpointRootEquation,cutoffParameterAssembly_apply] at hz0
    rw [←hd.1] at hz0
    linarith
  have huniq : ∀T:Overlap,(T:ℝ)∈endpointStrip cQ CQ p→
      Gamma Ψ (twoLevelMeasure theta.1 (hvalid _ hz) theta.2.1 T) T=(T:ℝ)→T=Q := by
    intro T hT hTzero
    have hdt := hdata theta.1 hz theta.2.1 hm theta.2.2 hl T hT
    have hzero : endpointRootEquation Ξ p qc (theta,(T:ℝ))=0 := by
      dsimp only [endpointRootEquation,cutoffParameterAssembly_apply]
      rw [←hdt.1,hTzero]
      ring
    apply Subtype.ext
    exact (distinguishedEndpoint_unique_closed Ξ p qc cQ CQ hCQ (by omega)
      hroot.1 hT hzero).symm.trans hqeq.symm
  have hsize := hd.2.2.2.2
  rw [hcontact] at hsize
  exact ⟨hqeq,by rw [hqeq];exact hroot.2.1,hcontact,huniq,hsize.1,hsize.2,hroot.2.2.2⟩

end DepthPaper
