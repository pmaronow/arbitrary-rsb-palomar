module

public import GeneralDepthPaper.SmoothCovarianceFamily

@[expose] public section


open Lean
run_cmd do
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  for name in [
      ``FourPapersCommon.mixedPotential_coleHopf_on_constantCDF,
      ``GeneralDepthPaper.parisiCDF_atomicMeasure_cell,
      ``GeneralDepthPaper.atomicCorrection_eq_integral,
      ``GeneralDepthPaper.potential_atomicMeasure_eq_recursion,
      ``GeneralDepthPaper.atomicFunctional_eq_recursion,
      ``GeneralDepthPaper.contDiffAt_atomicFunctionalExtension,
      ``GeneralDepthPaper.SmoothCovarianceFamily.finite_step_regularity] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on disallowed axiom {ax}"

#print axioms GeneralDepthPaper.potential_atomicMeasure_eq_recursion
#print axioms GeneralDepthPaper.atomicFunctional_eq_recursion
#print axioms GeneralDepthPaper.SmoothCovarianceFamily.finite_step_regularity
