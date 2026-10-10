module

public import GeneralDepthPaper.GaussianMomentUniformBounds
public import GeneralDepthPaper.BoundedSmoothAlgebra

@[expose] public section


/-! Actual joint all-order parameter bounds for the first three spatial
Cole–Hopf derivatives, uniform on terminal balls including mass zero. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction ContDiff
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64

theorem boundedSmoothOn_shiftedTerminalJet (A Vlo Vhi B : ℝ)
    (hA : 0≤A) (hVlo : 0<Vlo) (i : Fin 3) :
    BoundedSmoothOn (fun p:ColeHopfParameter=>shiftedTerminalJetCLM i p.2)
      (coleHopfBall A Vlo Vhi B) :=
  (boundedSmoothOn_coleHopf_terminal A Vlo Vhi B hA hVlo).compCLM (shiftedTerminalJetCLM i)

theorem boundedSmoothOn_terminalGaussianJetOne (A Vlo Vhi B : ℝ)
    (hA : 0≤A) (hVlo : 0<Vlo) (hV : Vlo≤Vhi) (hB : 0≤B) :
    BoundedSmoothOn terminalGaussianJetOne (coleHopfBall A Vlo Vhi B) :=
  boundedSmoothOn_terminalGaussianMoment A Vlo Vhi B hA hVlo hV hB _
    (boundedSmoothOn_shiftedTerminalJet A Vlo Vhi B hA hVlo 0)

theorem boundedSmoothOn_terminalGaussianJetTwo (A Vlo Vhi B : ℝ)
    (hA : 0≤A) (hVlo : 0<Vlo) (hV : Vlo≤Vhi) (hB : 0≤B) :
    BoundedSmoothOn terminalGaussianJetTwo (coleHopfBall A Vlo Vhi B) := by
  have h0 := boundedSmoothOn_shiftedTerminalJet A Vlo Vhi B hA hVlo 0
  have h1 := boundedSmoothOn_shiftedTerminalJet A Vlo Vhi B hA hVlo 1
  have ha := boundedSmoothOn_coleHopf_first A Vlo Vhi B hA hVlo
  have hJ := boundedSmoothOn_terminalGaussianJetOne A Vlo Vhi B hA hVlo hV hB
  exact (boundedSmoothOn_terminalGaussianMoment A Vlo Vhi B hA hVlo hV hB _ h1).add
    (ha.smul ((boundedSmoothOn_terminalGaussianMoment A Vlo Vhi B hA hVlo hV hB _
      (h0.pow 2)).sub (hJ.pow 2)))

theorem boundedSmoothOn_terminalGaussianJetThree (A Vlo Vhi B : ℝ)
    (hA : 0≤A) (hVlo : 0<Vlo) (hV : Vlo≤Vhi) (hB : 0≤B) :
    BoundedSmoothOn terminalGaussianJetThree (coleHopfBall A Vlo Vhi B) := by
  have h0 := boundedSmoothOn_shiftedTerminalJet A Vlo Vhi B hA hVlo 0
  have h1 := boundedSmoothOn_shiftedTerminalJet A Vlo Vhi B hA hVlo 1
  have h2 := boundedSmoothOn_shiftedTerminalJet A Vlo Vhi B hA hVlo 2
  have ha := boundedSmoothOn_coleHopf_first A Vlo Vhi B hA hVlo
  have hJ := boundedSmoothOn_terminalGaussianJetOne A Vlo Vhi B hA hVlo hV hB
  exact ((boundedSmoothOn_terminalGaussianMoment A Vlo Vhi B hA hVlo hV hB _ h2).add
    ((ha.const_smul (3:ℝ)).smul
      ((boundedSmoothOn_terminalGaussianMoment A Vlo Vhi B hA hVlo hV hB _ (h0.mul h1)).sub
        (hJ.mul (boundedSmoothOn_terminalGaussianMoment A Vlo Vhi B hA hVlo hV hB _ h1))))).add
    ((ha.pow 2).smul
      (((boundedSmoothOn_terminalGaussianMoment A Vlo Vhi B hA hVlo hV hB _ (h0.pow 3)).sub
        ((hJ.mul (boundedSmoothOn_terminalGaussianMoment A Vlo Vhi B hA hVlo hV hB _
          (h0.pow 2))).const_smul (3:ℝ))).add ((hJ.pow 3).const_smul (2:ℝ))))

end GeneralDepthPaper
