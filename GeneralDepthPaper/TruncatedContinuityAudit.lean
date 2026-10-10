module

public import GeneralDepthPaper.TruncatedSpatialFields
public import GeneralDepthPaper.TruncatedCoefficientConvergence

@[expose] public section


/-! Kernel audit for the actual finite-cell recursion and moving-grid
continuity used in Appendix A.2. This does not assert its diffusion conclusion. -/
#print axioms GeneralDepthPaper.terminalValue_truncatedPotential_cell
#print axioms GeneralDepthPaper.continuous_truncatedPotentialFamily
#print axioms GeneralDepthPaper.continuous_truncatedSpatialField
#print axioms GeneralDepthPaper.norm_truncatedSpatialField_zero_le_one
#print axioms GeneralDepthPaper.hasDerivAt_truncatedSpatialField_zero
#print axioms GeneralDepthPaper.hasDerivAt_truncatedSpatialField_one
#print axioms GeneralDepthPaper.tendsto_truncatedCoefficient_L1
#print axioms GeneralDepthPaper.tendsto_truncatedCoefficient_L2
