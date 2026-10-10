module

public import GeneralDepthPaper.ColeHopfGradientTime
public import GeneralDepthPaper.TruncatedSpatialFields
public import GeneralDepthPaper.TruncatedCoefficient
public import GeneralDepthPaper.ColeHopfValueTime

@[expose] public section


/-! Actual time evolution between the finite grid points of a truncated
Parisi problem. A differentiable, nondecreasing covariance clock is enough;
flat clocks and nonmonotone mass levels are allowed. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction NNReal
namespace GeneralDepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

def truncatedFirst {L : ℕ} {qc : ℝ} (hqc : 0 ≤ qc)
    (p : TruncatedRecursionParameter L qc) (q : ℝ) : ℝ := p.1 (projIcc 0 qc hqc q)

def truncatedPotential {L : ℕ} {qc : ℝ} (hqc : 0 ≤ qc)
    (p : TruncatedRecursionParameter L qc) (q x : ℝ) : ℝ :=
  terminalValue (truncatedPotentialTerminal p (projIcc 0 qc hqc q)) x

theorem hasDerivAt_truncatedPotential_time {L : ℕ} {qc : ℝ} (hqc : 0 ≤ qc)
    (p : TruncatedRecursionParameter L qc) (hn : Monotone p.2.1) (hm : Monotone p.1)
    (i : Fin L) (q c x : ℝ)
    (hq : q ∈ Ioo (p.2.1 i.castSucc : ℝ) (p.2.1 i.succ : ℝ))
    (hc : HasDerivAt (truncatedFirst hqc p) c q) :
    HasDerivAt (fun t => truncatedPotential hqc p t x)
      (-c/2*(truncatedSpatialField hqc p 1 (q,x)+
        p.2.2.1 i*(truncatedSpatialField hqc p 0 (q,x))^2)) q := by
  let V := fun t => p.1 (p.2.1 i.succ)-truncatedFirst hqc p t
  let g := truncatedPotentialTerminal p (p.2.1 i.succ)
  have hev : ∀ᶠ t in 𝓝 q,t ∈ Ioo (p.2.1 i.castSucc : ℝ) (p.2.1 i.succ : ℝ) :=
    Ioo_mem_nhds hq.1 hq.2
  have hcell (t : ℝ) (ht : t ∈ Ioo (p.2.1 i.castSucc : ℝ) (p.2.1 i.succ : ℝ)) :
      projIcc 0 qc hqc t ∈ Icc (p.2.1 i.castSucc) (p.2.1 i.succ) := by
    have htc : t ∈ Icc (0:ℝ) qc :=
      ⟨(p.2.1 i.castSucc).property.1.trans ht.1.le,ht.2.le.trans (p.2.1 i.succ).property.2⟩
    rw [projIcc_of_mem hqc htc]
    exact ⟨ht.1.le,ht.2.le⟩
  have hV : ∀ᶠ t in 𝓝 q,0 ≤ V t := by
    filter_upwards [hev] with t ht
    exact sub_nonneg.mpr (hm (hcell t ht).2)
  have hVq : 0 ≤ V q := sub_nonneg.mpr (hm (hcell q hq).2)
  have hVd : HasDerivAt V (-c) q := (hc.const_sub _).congr_deriv (by ring)
  have hd := (hasDerivWithinAt_coleHopfTerminal_value_variance
    (p.2.2.1 i) g (V q) hVq x).comp_hasDerivAt q hVd hV
  have he (t : ℝ) (ht : t ∈ Ioo (p.2.1 i.castSucc : ℝ) (p.2.1 i.succ : ℝ)) :
      truncatedPotential hqc p t x = terminalValue (coleHopfTerminal ((p.2.2.1 i,V t),g)) x := by
    rw [truncatedPotential,truncatedPotentialTerminal_cell p hn i _ (hcell t ht)]
    rfl
  have hj (j : Fin 3) : truncatedSpatialField hqc p j (q,x) =
      terminalJet (coleHopfTerminal ((p.2.2.1 i,V q),g)) j x := by
    rw [truncatedSpatialField_apply,truncatedPotentialTerminal_cell p hn i _ (hcell q hq)]
    rfl
  apply (hd.congr_of_eventuallyEq (hev.mono fun t ht => he t ht)).congr_deriv
  rw [hj 0,hj 1]
  ring

theorem hasDerivAt_truncatedSpatialField_zero_time {L : ℕ} {qc : ℝ} (hqc : 0 ≤ qc)
    (p : TruncatedRecursionParameter L qc) (hn : Monotone p.2.1) (hm : Monotone p.1)
    (i : Fin L) (q c x : ℝ)
    (hq : q ∈ Ioo (p.2.1 i.castSucc : ℝ) (p.2.1 i.succ : ℝ))
    (hc : HasDerivAt (truncatedFirst hqc p) c q) :
    HasDerivAt (fun t => truncatedSpatialField hqc p 0 (t,x))
      (-c/2*(truncatedSpatialField hqc p 2 (q,x)+
        2*p.2.2.1 i*truncatedSpatialField hqc p 0 (q,x)*truncatedSpatialField hqc p 1 (q,x))) q := by
  let V := fun t => p.1 (p.2.1 i.succ)-truncatedFirst hqc p t
  let g := truncatedPotentialTerminal p (p.2.1 i.succ)
  have hqcc : q ∈ Icc (0:ℝ) qc :=
    ⟨(p.2.1 i.castSucc).property.1.trans hq.1.le,hq.2.le.trans (p.2.1 i.succ).property.2⟩
  have hproj : (projIcc 0 qc hqc q : ℝ) = q := by rw [projIcc_of_mem hqc hqcc]
  have hev : ∀ᶠ t in 𝓝 q,t ∈ Ioo (p.2.1 i.castSucc : ℝ) (p.2.1 i.succ : ℝ) :=
    Ioo_mem_nhds hq.1 hq.2
  have hcell (t : ℝ) (ht : t ∈ Ioo (p.2.1 i.castSucc : ℝ) (p.2.1 i.succ : ℝ)) :
      projIcc 0 qc hqc t ∈ Icc (p.2.1 i.castSucc) (p.2.1 i.succ) := by
    have htc : t ∈ Icc (0:ℝ) qc :=
      ⟨(p.2.1 i.castSucc).property.1.trans ht.1.le,ht.2.le.trans (p.2.1 i.succ).property.2⟩
    rw [projIcc_of_mem hqc htc]
    exact ⟨ht.1.le,ht.2.le⟩
  have hV : ∀ᶠ t in 𝓝 q,0 ≤ V t := by
    filter_upwards [hev] with t ht
    exact sub_nonneg.mpr (hm (hcell t ht).2)
  have hVq : 0 ≤ V q := sub_nonneg.mpr (hm (hcell q hq).2)
  have hVd : HasDerivAt V (-c) q := (hc.const_sub _).congr_deriv (by ring)
  have hd := hasDerivAt_coleHopfTerminal_gradient_clock (p.2.2.1 i) g V q (-c) x hVd hVq hV
  have he (t : ℝ) (ht : t ∈ Ioo (p.2.1 i.castSucc : ℝ) (p.2.1 i.succ : ℝ)) (j : Fin 3) :
      truncatedSpatialField hqc p j (t,x) =
        terminalJet (coleHopfTerminal ((p.2.2.1 i,V t),g)) j x := by
    rw [truncatedSpatialField_apply,truncatedPotentialTerminal_cell p hn i _ (hcell t ht)]
    rfl
  apply (hd.congr_of_eventuallyEq (hev.mono fun t ht => he t ht 0)).congr_deriv
  rw [he q hq 0,he q hq 1,he q hq 2]

theorem hasDerivAt_truncatedSpatialField_zero_time_coefficient {L : ℕ} {qc : ℝ}
    (hqc : 0 ≤ qc) (p : TruncatedRecursionParameter L qc)
    (hn : Monotone p.2.1) (hm : Monotone p.1) (i : Fin L) (q c x : ℝ)
    (hq : q ∈ Ioo (p.2.1 i.castSucc : ℝ) (p.2.1 i.succ : ℝ))
    (hc : HasDerivAt (truncatedFirst hqc p) c q) :
    HasDerivAt (fun t => truncatedSpatialField hqc p 0 (t,x))
      (-c/2*(truncatedSpatialField hqc p 2 (q,x)+
        2*truncatedCoefficient p q*truncatedSpatialField hqc p 0 (q,x)*
          truncatedSpatialField hqc p 1 (q,x))) q := by
  rw [truncatedCoefficient_eq_level p hn q i ⟨hq.1.le,hq.2⟩]
  exact hasDerivAt_truncatedSpatialField_zero_time hqc p hn hm i q c x hq hc

end GeneralDepthPaper
