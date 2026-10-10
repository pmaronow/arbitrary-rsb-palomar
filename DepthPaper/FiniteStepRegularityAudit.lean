module

public import DepthPaper.SmoothCovarianceFamily

@[expose] public section


open Lean
run_cmd do
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  for name in [
      ``FourPapersCommon.mixedPotential_coleHopf_on_constantCDF,
      ``DepthPaper.parisiCDF_atomicMeasure_cell,
      ``DepthPaper.atomicCorrection_eq_integral,
      ``DepthPaper.potential_atomicMeasure_eq_recursion,
      ``DepthPaper.atomicFunctional_eq_recursion,
      ``DepthPaper.contDiffAt_atomicFunctionalExtension,
      ``DepthPaper.SmoothCovarianceFamily.finite_step_regularity] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on disallowed axiom {ax}"

#print axioms DepthPaper.potential_atomicMeasure_eq_recursion
#print axioms DepthPaper.atomicFunctional_eq_recursion
#print axioms DepthPaper.SmoothCovarianceFamily.finite_step_regularity
