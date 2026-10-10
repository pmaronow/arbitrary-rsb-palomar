module

public import GeneralDepthPaper.ColeHopfRecursion

@[expose] public section


open Lean
run_cmd do
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  for name in [
      ``GeneralDepthPaper.contDiffAt_submodule_of_coe,
      ``GeneralDepthPaper.uniformContinuous_gaussianTerminalTiltMean,
      ``GeneralDepthPaper.hasDerivAt_coleHopf_terminalValue,
      ``GeneralDepthPaper.hasDerivAt_terminalGaussianJetOne,
      ``GeneralDepthPaper.hasDerivAt_terminalGaussianJetTwo,
      ``GeneralDepthPaper.uniformContinuous_terminalGaussianJetThree,
      ``GeneralDepthPaper.terminalValue_centeredColeHopfTerminal,
      ``GeneralDepthPaper.contDiffAt_centeredColeHopfTerminal,
      ``GeneralDepthPaper.terminalValue_coleHopfTerminal,
      ``GeneralDepthPaper.norm_terminalJet_coleHopfTerminal_le,
      ``GeneralDepthPaper.contDiffAt_coleHopfRecursion,
      ``GeneralDepthPaper.norm_terminalJet_coleHopfRecursion_le] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on disallowed axiom {ax}"

#print axioms GeneralDepthPaper.contDiffAt_submodule_of_coe
#print axioms GeneralDepthPaper.contDiffAt_centeredColeHopfTerminal
#print axioms GeneralDepthPaper.contDiffAt_coleHopfRecursion
#print axioms GeneralDepthPaper.norm_terminalJet_coleHopfRecursion_le
