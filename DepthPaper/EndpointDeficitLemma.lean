module

public import DepthPaper.EndpointDeficitJets
public import DepthPaper.EndpointDeficitTwoSided

@[expose] public section


/-! The complete literal deficit lemma: the removable mass quotient,
actual C² parameter bounds, and actual two-sided endpoint size. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 64

def endpointDeficitSmoothDomain (Ξ : AdmissibleCovariance) {r : ℕ} (p : ℕ) (qc : ℝ) :
    Set (CutoffInputParameter r) := cutoffInputSmoothDomain Ξ p qc ∩
      {x | highDegreeSecondExpression Ξ p x.2.2≠0}

theorem isOpen_endpointDeficitSmoothDomain (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (qc : ℝ) : IsOpen (endpointDeficitSmoothDomain (r:=r) Ξ p qc) :=
  (isOpen_cutoffInputSmoothDomain Ξ p qc).inter
    (isClosed_singleton.isOpen_compl.preimage
      ((contDiff_highDegreeSecondExpression Ξ p).continuous.comp endpointPairProjection.continuous))

theorem contDiffOn_endpointDeficitFromRemainder (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (qc : ℝ) : ContDiffOn ℝ ∞ (endpointDeficitFromRemainder (r:=r) Ξ p qc)
      (endpointDeficitSmoothDomain Ξ p qc) := by
  rw [endpointDeficitFromRemainder_eq_product]
  intro x hx
  have hi : ContDiffAt ℝ ∞ (fun y:CutoffInputParameter r=> (highDegreeSecondExpression Ξ p y.2.2)⁻¹) x :=
    ((contDiff_highDegreeSecondExpression Ξ p).contDiffAt.comp x
      endpointPairProjection.contDiff.contDiffAt).inv hx.2
  have ha := (contDiffOn_endpointDeficitAverage Ξ p qc x hx.1).contDiffAt
    ((isOpen_cutoffInputSmoothDomain Ξ p qc).mem_nhds hx.1)
  exact ((hi.mul ha).const_smul _).contDiffWithinAt

def EndpointDeficitTarget : Prop :=
  ∀Ξ:AdmissibleCovariance,∀r:ℕ,∀K:Set (AtomicPoint r),IsCompact K→
    ∀hvalid:(∀z∈K,IsAtomicPoint z),∀e lo hi qc cQ CQ:ℝ,0 < e→∀hlo:0 < lo,lo ≤ hi→
      qc∈Ioo (0:ℝ) 1→(∀z∈K,atomicLocation z (Fin.last r) < qc)→0 < cQ→
      ∃C:ℝ,0 < C ∧ ∃A:ℕ,∃c:ℝ,0 < c ∧ ∃b:ℝ,0 < b ∧ ∃D:ℝ,0 < D ∧ ∃P:ℕ,4 ≤ P ∧
        ∀p:ℕ,P ≤ p→∀he:Even p,∃hp:4 ≤ p,∃hn:p∉Ξ.degrees,
          ∀z:AtomicPoint r,∀hz:z∈K,∀m∈Icc e 1,∀lam:ℝ,∀hlam:lam∈Icc lo hi,
            ∀Q:Overlap,(Q:ℝ)∈endpointStrip cQ CQ p→
              let x : CutoffInputParameter r := (z,(m,(lam,(Q:ℝ))))
              let Ψ := Ξ.addHighDegree p hp he hn lam (hlo.trans_le hlam.1)
              1-Gamma Ψ (twoLevelMeasure z (hvalid z hz) m Q) Q=
                endpointDeficitFromRemainder Ξ p qc x ∧
              ContDiffAt ℝ ∞ (endpointDeficitFromRemainder Ξ p qc) x ∧
              (∀j:ℕ,j ≤ 2→‖iteratedFDeriv ℝ j (endpointDeficitFromRemainder Ξ p qc) x‖ ≤ C*(p:ℝ)^A*Real.exp (-c*(p:ℝ))) ∧
              (∀j:ℕ,j ≤ 2→∀v:Fin j→LowerInputCoordinate r,
                ‖directionalWordJet lowerInputAxis (endpointDeficitFromRemainder Ξ p qc)
                  (List.ofFn v) x‖ ≤ C*(p:ℝ)^A*Real.exp (-c*(p:ℝ))) ∧
              b*(p:ℝ)^(-(1/2:ℝ))*Real.exp (-m^2*lam*(p:ℝ)/2) ≤ 1-Gamma Ψ (twoLevelMeasure z (hvalid z hz) m Q) Q ∧
              1-Gamma Ψ (twoLevelMeasure z (hvalid z hz) m Q) Q ≤ D*(p:ℝ)^(-(1/2:ℝ))*Real.exp (-m^2*lam*(p:ℝ)/2)

theorem endpoint_deficit : EndpointDeficitTarget := by
  intro Ξ r K hK hvalid e lo hi qc cQ CQ he hlo hLH hc hcut hcQ
  obtain ⟨C,hC,A,c,hcpos,P1,hP1,h1⟩ := endpoint_deficit_crude_derivative_bound
    Ξ (CQ:=CQ) hK hvalid he hlo hLH hc hcut hcQ 2
  obtain ⟨b,hb,D,hD,P2,h2⟩ := endpoint_deficit_two_sided Ξ hlo hLH hc (CQ:=CQ) hcQ
  obtain ⟨P3,h3⟩ := eventually_atTop.mp (endpointStrip_above_cutoff_eventually (CQ:=CQ) hc.2 hcQ)
  let P := max (max P1 P2) P3
  refine ⟨C,hC,A,c,hcpos,b,hb,D,hD,P,hP1.trans
    ((le_max_left _ _).trans (le_max_left _ _)),?_⟩
  intro p hp heven
  have hp1 : P1 ≤ p := (le_max_left P1 P2).trans ((le_max_left _ _).trans hp)
  have hp2 : P2 ≤ p := (le_max_right P1 P2).trans ((le_max_left _ _).trans hp)
  obtain ⟨hp4,hn,hsize⟩ := h2 p hp2 heven
  refine ⟨hp4,hn,?_⟩
  intro z hz m hm lam hl Q hQ
  let x : CutoffInputParameter r := (z,(m,(lam,(Q:ℝ))))
  have hm0 : 0 < m := he.trans_le hm.1
  have hQqc : qc < (Q:ℝ) := h3 p ((le_max_right _ _).trans hp) Q hQ
  have hQ1 : (Q:ℝ) < 1 := (endpointStrip_mem_unit hcQ p hQ).2
  have hi := endpoint_deficit_remainder_identity Ξ p hp4 heven hn z (hvalid z hz)
    m ⟨hm0,hm.2⟩ lam (hlo.trans_le hl.1) Q (hcut z hz) hQqc hQ1
  obtain ⟨hs,hjets⟩ := h1 p hp1 x hz hm hl hQ
  have hW : 0 < endpointVarianceExpression Ξ p qc x.2.2 := by
    have hbase := sub_pos.mpr (Ξ.first_strictMonoOn hc.1.le (hc.1.trans hQqc).le hQqc)
    exact add_pos_of_pos_of_nonneg hbase (mul_nonneg
      (mul_nonneg (hlo.le.trans hl.1) (Nat.cast_nonneg _))
      (sub_nonneg.mpr (pow_le_pow_left₀ hc.1.le hQqc.le (p-1))))
  have hdom : x∈endpointDeficitSmoothDomain Ξ p qc := by
    refine ⟨cutoffInputSmoothDomain_mem Ξ p x (hvalid z hz) (hcut z hz)
      ⟨hm0,hm.2.trans_lt (by norm_num)⟩ (hlo.le.trans hl.1) hW,?_⟩
    have hh : highDegreeSecondExpression Ξ p x.2.2=
        (Ξ.addHighDegree p hp4 heven hn lam (hlo.trans_le hl.1)).second Q :=
      (Ξ.addHighDegree_second p hp4 heven hn lam (hlo.trans_le hl.1) Q).symm
    change highDegreeSecondExpression Ξ p x.2.2≠0
    rw [hh]
    exact ((Ξ.addHighDegree p hp4 heven hn lam (hlo.trans_le hl.1)).second_pos
      (hc.1.trans hQqc)).ne'
  have hword : ∀j:ℕ,j ≤ 2→∀v:Fin j→LowerInputCoordinate r,
      ‖directionalWordJet lowerInputAxis (endpointDeficitFromRemainder Ξ p qc)
        (List.ofFn v) x‖ ≤ C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) := by
    intro j hj v
    rw [←iteratedFDeriv_dirs_eq_directionalWordJet lowerInputAxis
      (isOpen_endpointDeficitSmoothDomain Ξ p qc)
      (contDiffOn_endpointDeficitFromRemainder Ξ p qc) j v hdom]
    have H := (iteratedFDeriv ℝ j (endpointDeficitFromRemainder Ξ p qc) x).le_opNorm
      (fun i=>lowerInputAxis (v i))
    have H' : ‖iteratedFDeriv ℝ j (endpointDeficitFromRemainder Ξ p qc) x
        (fun i=>lowerInputAxis (v i))‖ ≤
          ‖iteratedFDeriv ℝ j (endpointDeficitFromRemainder Ξ p qc) x‖ := by
      simpa only [norm_lowerInputAxis,Finset.prod_const_one,mul_one] using H
    exact H'.trans (hjets j hj)
  obtain ⟨hlower,hupper⟩ := hsize lam hl Q hQ m ⟨hm0,hm.2⟩ r z (hvalid z hz) (hcut z hz)
  exact ⟨hi,hs,hjets,hword,hlower,hupper⟩

end DepthPaper
