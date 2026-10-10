module

public import GeneralDepthPaper.GaussianTiltedUniform
public import GeneralDepthPaper.ColeHopfSpatialJets

@[expose] public section


/-! Uniform continuity of the actual third Cole–Hopf jet, proved from actual
normalized Gaussian observables and the terminal-data translation group. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000

theorem uniformContinuous_terminalGaussianJetThree (p : ColeHopfParameter) (hv : 0<p.1.2) :
    UniformContinuous (terminalGaussianJetThree p) := by
  let B := terminalJet p.2 0
  let C := terminalJet p.2 1
  let D := terminalJet p.2 2
  have hB := uniformContinuous_terminalJet p.2 0
  have hC := uniformContinuous_terminalJet p.2 1
  have hD := uniformContinuous_terminalJet p.2 2
  have hMB := uniformContinuous_gaussianTerminalTiltMean p hv B hB
  have hMC := uniformContinuous_gaussianTerminalTiltMean p hv C hC
  have hMD := uniformContinuous_gaussianTerminalTiltMean p hv D hD
  have hMB2 := uniformContinuous_gaussianTerminalTiltMean p hv (B^2)
    (uniformContinuous_bcf_pow B hB 2)
  have hMB3 := uniformContinuous_gaussianTerminalTiltMean p hv (B^3)
    (uniformContinuous_bcf_pow B hB 3)
  have hMBC := uniformContinuous_gaussianTerminalTiltMean p hv (B*C)
    (uniformContinuous_bcf_mul B C hB hC)
  have hlast := ((hMB3.sub ((uniformContinuous_bcf_mul _ _ hMB hMB2).const_smul (3:ℝ))).add
      ((uniformContinuous_bcf_pow _ hMB 3).const_smul (2:ℝ))).const_smul (p.1.1^2)
  have H := (hMD.add ((hMBC.sub (uniformContinuous_bcf_mul _ _ hMB hMC)).const_smul (3*p.1.1))).add hlast
  convert! H using 1


end GeneralDepthPaper
