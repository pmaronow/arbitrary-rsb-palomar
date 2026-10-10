module

public import DepthPaper.TerminalConstantShift

@[expose] public section


/-! The precise uniform jet convergence in Appendix A.2: terminal additive
constants may diverge, since only the first three terminal derivatives are
assumed to converge. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction
namespace DepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem tendsto_truncatedSpatialField_of_terminal_jets {L : ℕ} {qc : ℝ}
    (hqc : 0 ≤ qc) {P : Type*} {F : Filter P}
    (p : P → TruncatedRecursionParameter L qc) (p0 : TruncatedRecursionParameter L qc)
    (hfirst : Tendsto (fun n => (p n).1) F (𝓝 p0.1))
    (hnode : Tendsto (fun n => (p n).2.1) F (𝓝 p0.2.1))
    (hlevel : Tendsto (fun n => (p n).2.2.1) F (𝓝 p0.2.2.1))
    (hjet : ∀j : Fin 3,Tendsto (fun n => terminalJet (p n).2.2.2 j) F (𝓝 (terminalJet p0.2.2.2 j)))
    (hm : ∀n,Monotone (p n).1) (hm0 : Monotone p0.1) (j : Fin 3) :
    Tendsto (fun n => truncatedSpatialField hqc (p n) j) F (𝓝 (truncatedSpatialField hqc p0 j)) := by
  have hN : Tendsto (fun n => terminalNormalize (p n).2.2.2) F
      (𝓝 (terminalNormalize p0.2.2.2)) := (tendsto_terminalNormalize_iff _ _).mpr hjet
  have hparam : Tendsto (fun n => normalizedTruncatedParameter (p n)) F
      (𝓝 (normalizedTruncatedParameter p0)) := by
    simpa only [normalizedTruncatedParameter,nhds_prod_eq] using
      hfirst.prodMk (hnode.prodMk (hlevel.prodMk hN))
  have h := (continuous_truncatedSpatialField hqc j).continuousAt.tendsto.comp hparam
  change Tendsto (fun n => truncatedSpatialField hqc (normalizedTruncatedParameter (p n)) j)
    F (𝓝 (truncatedSpatialField hqc (normalizedTruncatedParameter p0) j)) at h
  simpa only [truncatedSpatialField_normalized hqc _ (hm _) j,
    truncatedSpatialField_normalized hqc p0 hm0 j] using h

theorem tendstoUniformly_truncatedSpatialField_of_terminal_jets {L : ℕ} {qc : ℝ}
    (hqc : 0 ≤ qc) {P : Type*} {F : Filter P}
    (p : P → TruncatedRecursionParameter L qc) (p0 : TruncatedRecursionParameter L qc)
    (hfirst : Tendsto (fun n => (p n).1) F (𝓝 p0.1))
    (hnode : Tendsto (fun n => (p n).2.1) F (𝓝 p0.2.1))
    (hlevel : Tendsto (fun n => (p n).2.2.1) F (𝓝 p0.2.2.1))
    (hjet : ∀j : Fin 3,Tendsto (fun n => terminalJet (p n).2.2.2 j) F (𝓝 (terminalJet p0.2.2.2 j)))
    (hm : ∀n,Monotone (p n).1) (hm0 : Monotone p0.1) (j : Fin 3) :
    TendstoUniformly (fun n qx => truncatedSpatialField hqc (p n) j qx)
      (truncatedSpatialField hqc p0 j) F :=
  BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
    (tendsto_truncatedSpatialField_of_terminal_jets hqc p p0 hfirst hnode hlevel hjet hm hm0 j)

end DepthPaper
