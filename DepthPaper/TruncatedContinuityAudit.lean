module

public import DepthPaper.TruncatedSpatialFields
public import DepthPaper.TruncatedCoefficientConvergence

@[expose] public section


/-! Kernel audit for the actual finite-cell recursion and moving-grid
continuity used in Appendix A.2. This does not assert its diffusion conclusion. -/
#print axioms DepthPaper.terminalValue_truncatedPotential_cell
#print axioms DepthPaper.continuous_truncatedPotentialFamily
#print axioms DepthPaper.continuous_truncatedSpatialField
#print axioms DepthPaper.norm_truncatedSpatialField_zero_le_one
#print axioms DepthPaper.hasDerivAt_truncatedSpatialField_zero
#print axioms DepthPaper.hasDerivAt_truncatedSpatialField_one
#print axioms DepthPaper.tendsto_truncatedCoefficient_L1
#print axioms DepthPaper.tendsto_truncatedCoefficient_L2
