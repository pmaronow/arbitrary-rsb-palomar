module

public import DepthPaper.ColeHopfRecursion

@[expose] public section


open Lean
run_cmd do
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  for name in [
      ``DepthPaper.contDiffAt_submodule_of_coe,
      ``DepthPaper.uniformContinuous_gaussianTerminalTiltMean,
      ``DepthPaper.hasDerivAt_coleHopf_terminalValue,
      ``DepthPaper.hasDerivAt_terminalGaussianJetOne,
      ``DepthPaper.hasDerivAt_terminalGaussianJetTwo,
      ``DepthPaper.uniformContinuous_terminalGaussianJetThree,
      ``DepthPaper.terminalValue_centeredColeHopfTerminal,
      ``DepthPaper.contDiffAt_centeredColeHopfTerminal,
      ``DepthPaper.terminalValue_coleHopfTerminal,
      ``DepthPaper.norm_terminalJet_coleHopfTerminal_le,
      ``DepthPaper.contDiffAt_coleHopfRecursion,
      ``DepthPaper.norm_terminalJet_coleHopfRecursion_le] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on disallowed axiom {ax}"

#print axioms DepthPaper.contDiffAt_submodule_of_coe
#print axioms DepthPaper.contDiffAt_centeredColeHopfTerminal
#print axioms DepthPaper.contDiffAt_coleHopfRecursion
#print axioms DepthPaper.norm_terminalJet_coleHopfRecursion_le
