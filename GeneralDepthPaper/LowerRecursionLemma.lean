module

public import GeneralDepthPaper.LowerRecursionSmoothDomain
public import GeneralDepthPaper.CutoffTerminalApproximation

@[expose] public section


/-! Literal lower recursion Lemma 4.2: the actual candidate functional
equals the limiting objective plus its explicit endpoint term and a C⁴
remainder with exponentially small ordered coordinate derivatives. -/
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff BigOperators
namespace GeneralDepthPaper
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 64

abbrev LowerInputCoordinate (r : ℕ) := (Fin r⊕Fin r)⊕Fin 3

def lowerInputAxis {r : ℕ} : LowerInputCoordinate r→CutoffInputParameter r :=
  Sum.elim (Sum.elim
    (fun i=>((Pi.single i 1,0),(0,(0,0))))
    (fun i=>((0,Pi.single i 1),(0,(0,0)))))
    (fun i=>((0,0),cutoffAxis i))

theorem norm_lowerInputAxis {r : ℕ} (i : LowerInputCoordinate r) : ‖lowerInputAxis i‖=1 := by
  rcases i with i|i
  · rcases i with i|i <;> simp [lowerInputAxis,Prod.norm_def,Pi.norm_single]
  · change ‖((0:AtomicPoint r),cutoffAxis i)‖=1
    rw [Prod.norm_def,norm_zero,norm_cutoffAxis]
    norm_num

theorem endpointStrip_above_cutoff_eventually {qc cQ CQ : ℝ}
    (hc : qc<1) (hcQ : 0<cQ) :
    ∀ᶠp:ℕ in atTop,∀Q:ℝ,Q∈endpointStrip cQ CQ p→qc<Q := by
  have hlim := tendsto_nat_polynomial_exp 1 cQ 0 hcQ
  have hs : ∀ᶠp:ℕ in atTop,Real.exp (-cQ*(p:ℝ))<1-qc := by
    simpa only [pow_zero,mul_one,one_mul] using hlim.eventually (Iio_mem_nhds (by linarith))
  filter_upwards [hs] with p hp Q hQ
  have hlower := hQ.1
  linarith

theorem twoLevelFunctional_eq_lowerRecursionErrorRaw (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (hp : 4≤p) (he : Even p) (hn : p∉Ξ.degrees)
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Ioc (0:ℝ) 1)
    (lam : ℝ) (hlam : 0<lam) (Q : Overlap) (qc : ℝ)
    (hc : atomicLocation z (Fin.last r)<qc) (hcQ : qc≤(Q:ℝ)) :
    twoLevelFunctional (Ξ.addHighDegree p hp he hn lam hlam) z hz m Q=
      limitingAtomicObjective Ξ r lam (z,m)+
        (1-m)/2*(∫q in (Q:ℝ)..1,(1-q)*(Ξ.addHighDegree p hp he hn lam hlam).second q)+
          lowerRecursionErrorRaw Ξ p qc (z,(m,(lam,(Q:ℝ)))) := by
  have H := twoLevelFunctional_decomposition Ξ (Ξ.addHighDegree p hp he hn lam hlam)
    z hz m hm Q qc hc hcQ
  have hlambda : (Ξ.addHighDegree p hp he hn lam hlam).value 1-Ξ.value 1=lam := by
    simp only [AdmissibleCovariance.addHighDegree_value,one_pow,mul_one,add_sub_cancel_left]
  rw [hlambda,lowerRecursionRemainder_eq_extension] at H
  rw [lowerRecursionErrorRaw_eq_extension Ξ p hp he hn (z,(m,(lam,(Q:ℝ)))) hlam qc]
  exact H

def LowerRecursionTarget : Prop :=
  ∀Ξ:AdmissibleCovariance,∀r:ℕ,∀K:Set (AtomicPoint r),IsCompact K→
    ∀hvalid:(∀z∈K,IsAtomicPoint z),∀ε lamlo lamhi qc cQ CQ:ℝ,0<ε→0<lamlo→lamlo≤lamhi→
    qc∈Ioo (0:ℝ) 1→(∀z∈K,atomicLocation z (Fin.last r)<qc)→0<cQ→
    ∃C:ℝ,0<C ∧ ∃A:ℕ,∃c:ℝ,0<c ∧ ∃p0:ℕ,4≤p0 ∧
      ∀p:ℕ,p0≤p→∀he:Even p,∀z:AtomicPoint r,∀hz:z∈K,∀m∈Icc ε 1,∀lam∈Icc lamlo lamhi,
        ∀Q:Overlap,(Q:ℝ)∈endpointStrip cQ CQ p→
          ∃hp:4≤p,∃hn:p∉Ξ.degrees,∃hlam:0<lam,
            twoLevelFunctional (Ξ.addHighDegree p hp he hn lam hlam) z
                (hvalid z hz) m Q=
              limitingAtomicObjective Ξ r lam (z,m)+
                (1-m)/2*(∫q in (Q:ℝ)..1,(1-q)*(Ξ.addHighDegree p hp he hn lam hlam).second q)+
                  lowerRecursionErrorRaw Ξ p qc (z,(m,(lam,(Q:ℝ)))) ∧
            ContDiffAt ℝ ∞ (lowerRecursionErrorRaw Ξ p qc) (z,(m,(lam,(Q:ℝ)))) ∧
            ∀n:ℕ,n≤4→∀v:Fin n→LowerInputCoordinate r,
              ‖directionalWordJet lowerInputAxis (lowerRecursionErrorRaw Ξ p qc)
                (List.ofFn v) (z,(m,(lam,(Q:ℝ))))‖≤C*(p:ℝ)^A*Real.exp (-c*(p:ℝ))

theorem lower_recursion : LowerRecursionTarget := by
  intro Ξ r K hK hvalid ε lamlo lamhi qc cQ CQ hε hlo hLH hc hcut hcQ
  obtain ⟨C,hC,A,c,hcpos,pr,hpr,hr⟩ :=
    lower_recursion_error_exponential_bound Ξ (CQ:=CQ) hK hvalid hε hlo hLH hc hcut hcQ 4
  obtain ⟨Ct,hCt,At,ct,hct,pt,hpt,ht⟩ :=
    cutoff_endpoint_error_exponential_bound Ξ (CQ:=CQ) hε hlo hLH hc hcQ 0
  obtain ⟨pq,hpq⟩ := eventually_atTop.mp (endpointStrip_above_cutoff_eventually (CQ:=CQ) hc.2 hcQ)
  let p0 := max (max pr pt) (max pq (max 4 (Ξ.degrees.sup id+1)))
  refine ⟨C,hC,A,c,hcpos,p0,by dsimp only [p0];omega,?_⟩
  intro p hp he z hz m hm lam hlam Q hQ
  have hp4 : 4≤p := by dsimp only [p0] at hp;omega
  have hn : p∉Ξ.degrees := by
    intro hmem
    have hsup : p≤Ξ.degrees.sup id := Finset.le_sup (f:=id) hmem
    dsimp only [p0] at hp
    omega
  have hlambda : 0<lam := hlo.trans_le hlam.1
  have hcQ' : qc<(Q:ℝ) := hpq p (by dsimp only [p0] at hp;omega) Q hQ
  let x : CutoffInputParameter r := (z,(m,(lam,(Q:ℝ))))
  obtain ⟨hs,hjets⟩ := hr p (by dsimp only [p0] at hp;omega) x hz hm hlam hQ
  obtain ⟨hW,hsm,hb⟩ := ht p (by dsimp only [p0] at hp;omega) m hm lam hlam Q hQ
  have hdom : x∈cutoffInputSmoothDomain Ξ p qc := cutoffInputSmoothDomain_mem Ξ p x
    (hvalid z hz) (hcut z hz) ⟨hε.trans_le hm.1,hm.2.trans_lt (by norm_num)⟩
      hlambda.le (zero_lt_one.trans hW)
  refine ⟨hp4,hn,hlambda,twoLevelFunctional_eq_lowerRecursionErrorRaw Ξ p hp4 he hn z
    (hvalid z hz) m ⟨hε.trans_le hm.1,hm.2⟩ lam hlambda Q qc (hcut z hz) hcQ'.le,hs,?_⟩
  intro n hn4 v
  rw [←iteratedFDeriv_dirs_eq_directionalWordJet lowerInputAxis
    (isOpen_cutoffInputSmoothDomain Ξ p qc) (contDiffOn_lowerRecursionErrorRaw Ξ p qc) n v hdom]
  have hop := (iteratedFDeriv ℝ n (lowerRecursionErrorRaw Ξ p qc) x).le_opNorm
    (fun i=>lowerInputAxis (v i))
  have hop' : ‖iteratedFDeriv ℝ n (lowerRecursionErrorRaw Ξ p qc) x
      (fun i=>lowerInputAxis (v i))‖≤‖iteratedFDeriv ℝ n (lowerRecursionErrorRaw Ξ p qc) x‖ := by
    simpa only [norm_lowerInputAxis,Finset.prod_const_one,mul_one] using hop
  exact hop'.trans (hjets n hn4)

end GeneralDepthPaper
