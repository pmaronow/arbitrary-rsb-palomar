module

public import DepthPaper.ObservableContinuity

@[expose] public section


open Lean
run_cmd do
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  for name in [
      ``DepthPaper.observable_continuity,
      ``DepthPaper.TruncatedParisiData.Gamma_sub_eq_integral_cell_interior,
      ``DepthPaper.TruncatedParisiData.Gamma_eq_initial_add_integral,
      ``DepthPaper.TruncatedParisiData.hasDerivWithinAt_Gamma,
      ``DepthPaper.TruncatedParisiData.contDiffOn_Gamma,
      ``DepthPaper.TruncatedParisiData.contDiffOn_firstVariation,
      ``DepthPaper.TruncatedParisiData.firstVariationJets_derivative,
      ``DepthPaper.TruncatedDataConvergence.state_mean_square,
      ``DepthPaper.TruncatedDataConvergence.Gamma,
      ``DepthPaper.TruncatedDataConvergence.Gamma2,
      ``DepthPaper.TruncatedDataConvergence.firstVariation_C2] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on disallowed axiom {ax}"

#print axioms DepthPaper.observable_continuity
#print axioms DepthPaper.TruncatedParisiData.Gamma_sub_eq_integral_cell_interior
#print axioms DepthPaper.TruncatedParisiData.Gamma_eq_initial_add_integral
#print axioms DepthPaper.TruncatedParisiData.hasDerivWithinAt_Gamma
#print axioms DepthPaper.TruncatedParisiData.contDiffOn_Gamma
#print axioms DepthPaper.TruncatedParisiData.contDiffOn_firstVariation
#print axioms DepthPaper.TruncatedParisiData.firstVariationJets_derivative
#print axioms DepthPaper.TruncatedDataConvergence.state_mean_square
#print axioms DepthPaper.TruncatedDataConvergence.Gamma
#print axioms DepthPaper.TruncatedDataConvergence.Gamma2
#print axioms DepthPaper.TruncatedDataConvergence.firstVariation_C2
