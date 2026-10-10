module

public import GeneralDepthPaper.ObservableContinuity

@[expose] public section


open Lean
run_cmd do
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  for name in [
      ``GeneralDepthPaper.observable_continuity,
      ``GeneralDepthPaper.TruncatedParisiData.Gamma_sub_eq_integral_cell_interior,
      ``GeneralDepthPaper.TruncatedParisiData.Gamma_eq_initial_add_integral,
      ``GeneralDepthPaper.TruncatedParisiData.hasDerivWithinAt_Gamma,
      ``GeneralDepthPaper.TruncatedParisiData.contDiffOn_Gamma,
      ``GeneralDepthPaper.TruncatedParisiData.contDiffOn_firstVariation,
      ``GeneralDepthPaper.TruncatedParisiData.firstVariationJets_derivative,
      ``GeneralDepthPaper.TruncatedDataConvergence.state_mean_square,
      ``GeneralDepthPaper.TruncatedDataConvergence.Gamma,
      ``GeneralDepthPaper.TruncatedDataConvergence.Gamma2,
      ``GeneralDepthPaper.TruncatedDataConvergence.firstVariation_C2] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on disallowed axiom {ax}"

#print axioms GeneralDepthPaper.observable_continuity
#print axioms GeneralDepthPaper.TruncatedParisiData.Gamma_sub_eq_integral_cell_interior
#print axioms GeneralDepthPaper.TruncatedParisiData.Gamma_eq_initial_add_integral
#print axioms GeneralDepthPaper.TruncatedParisiData.hasDerivWithinAt_Gamma
#print axioms GeneralDepthPaper.TruncatedParisiData.contDiffOn_Gamma
#print axioms GeneralDepthPaper.TruncatedParisiData.contDiffOn_firstVariation
#print axioms GeneralDepthPaper.TruncatedParisiData.firstVariationJets_derivative
#print axioms GeneralDepthPaper.TruncatedDataConvergence.state_mean_square
#print axioms GeneralDepthPaper.TruncatedDataConvergence.Gamma
#print axioms GeneralDepthPaper.TruncatedDataConvergence.Gamma2
#print axioms GeneralDepthPaper.TruncatedDataConvergence.firstVariation_C2
