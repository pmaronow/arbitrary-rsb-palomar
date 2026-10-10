module

public import GeneralDepthPaper.GaussianGradientVariance
public import GeneralDepthPaper.ColeHopfClosedVariance

@[expose] public section


/-! Closed-variance heat evolution of the actual first spatial Cole–Hopf jet.
This supplies time derivatives on flat covariance cells as well as positive
variance cells, without dividing by the mass. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace GeneralDepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem terminalJet_coleHopfTerminal_boundary (p : ColeHopfParameter)
    (hv : 0 ≤ p.1.2) (j : Fin 3) : terminalJet (coleHopfTerminal p) j =
      ![boundaryGaussianJetOne p,boundaryGaussianJetTwo p,boundaryGaussianJetThree p] j := by
  rcases eq_or_lt_of_le hv with h0 | hpos
  · have hp : p = ((p.1.1,0),p.2) := by ext <;> simp_all
    rw [hp,coleHopfTerminal_zero_variance]
    fin_cases j <;> simp
  · rw [coleHopfTerminal]
    change terminalJet p.2 j+(centeredColeHopfTerminal p).1.2 j = _
    rw [centeredColeHopfTerminal_raw p hpos]
    fin_cases j <;> simp [centeredColeHopfJets,boundaryGaussianJetOne_eq p hpos,
      boundaryGaussianJetTwo_eq p hpos,boundaryGaussianJetThree_eq p hpos]

theorem hasDerivWithinAt_coleHopfTerminal_gradient_variance
    (a : ℝ) (g : TerminalSpace) (V : ℝ) (hV : 0 ≤ V) (x : ℝ) :
    HasDerivWithinAt (fun v : ℝ => terminalJet (coleHopfTerminal ((a,v),g)) 0 x)
      ((1/2:ℝ)*(terminalJet (coleHopfTerminal ((a,V),g)) 2 x+
        2*a*terminalJet (coleHopfTerminal ((a,V),g)) 0 x*
          terminalJet (coleHopfTerminal ((a,V),g)) 1 x)) (Ici 0) V := by
  have hd := hasDerivWithinAt_boundaryGaussianJetOne_variance a g V hV x
  have hfun : (fun v : ℝ => terminalJet (coleHopfTerminal ((a,v),g)) 0 x)
      =ᶠ[𝓝[Ici 0] V] (fun v => boundaryGaussianJetOne ((a,v),g) x) := by
    apply eventually_nhdsWithin_of_forall
    intro v hv
    simp only [terminalJet_coleHopfTerminal_boundary ((a,v),g) hv,Matrix.cons_val_zero]
  have he : terminalJet (coleHopfTerminal ((a,V),g)) 0 x = boundaryGaussianJetOne ((a,V),g) x := by
    simp only [terminalJet_coleHopfTerminal_boundary ((a,V),g) hV,Matrix.cons_val_zero]
  apply (hd.congr_of_eventuallyEq hfun he).congr_deriv
  simp [terminalJet_coleHopfTerminal_boundary ((a,V),g) hV]

theorem hasDerivAt_coleHopfTerminal_gradient_clock
    (a : ℝ) (g : TerminalSpace) (V : ℝ → ℝ) (q c x : ℝ)
    (hd : HasDerivAt V c q) (hv : 0 ≤ V q) (he : ∀ᶠ t in 𝓝 q,0 ≤ V t) :
    HasDerivAt (fun t => terminalJet (coleHopfTerminal ((a,V t),g)) 0 x)
      (c/2*(terminalJet (coleHopfTerminal ((a,V q),g)) 2 x+
        2*a*terminalJet (coleHopfTerminal ((a,V q),g)) 0 x*
          terminalJet (coleHopfTerminal ((a,V q),g)) 1 x)) q := by
  have h := (hasDerivWithinAt_coleHopfTerminal_gradient_variance a g (V q) hv x).comp_hasDerivAt q hd he
  exact h.congr_deriv (by ring)

end GeneralDepthPaper
