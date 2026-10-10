module

public import GeneralDepthPaper.LimitingCutoffChoice

@[expose] public section


/-! Raising the harmless preliminary cutoff yields exactly the actual
strict negative standing cutoff required for the high-overlap argument. -/
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 1200000

namespace LimitingStandingData
variable {Ξ:AdmissibleCovariance} {r:ℕ} {seed:AtomicPoint r}

def withCutoff (d:LimitingStandingData Ξ seed) (qc:ℝ) (hq:qc∈Ioo (0:ℝ) 1)
    (hle:d.cutoff ≤ qc) : LimitingStandingData Ξ seed :=
  {d with
    cutoff := qc
    cutoff_mem := hq
    ball_below_cutoff := fun z hz=>(d.ball_below_cutoff z hz).trans_le hle}

end LimitingStandingData

theorem exists_standing_cutoff_data (Ξ:AdmissibleCovariance) {r:ℕ}
    (seed:AtomicPoint r) (hz:IsAtomicPoint seed) (hnd:Nondegenerate Ξ seed hz) :
    ∃d:LimitingStandingData Ξ seed,∃gamma:ℝ,0 < gamma ∧
      (∀m:d.MassInterval,d.limitingVariation m 1 ≤ -5*gamma) ∧
      (∀m:d.MassInterval,∀q∈Icc d.cutoff 1,d.limitingVariation m q ≤ -4*gamma) ∧
      (1/2:ℝ)*(∫q in d.cutoff..1,(1-q)*Ξ.second q) ≤ gamma := by
  obtain ⟨d0⟩:=exists_limitingStandingData Ξ seed hz hnd
  obtain ⟨gamma,hg,qc,hqc,hend,hnegative,hcost⟩:=d0.limiting_cutoff_choice
  let d:=d0.withCutoff qc ⟨d0.cutoff_mem.1.trans hqc.1,hqc.2⟩ hqc.1.le
  refine ⟨d,gamma,hg,?_,?_,hcost⟩
  · exact hend
  · exact hnegative

end GeneralDepthPaper
