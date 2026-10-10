module

public import DepthPaper.GaussianTiltedOperator
public import DepthPaper.GaussianTiltedBounds
public import DepthPaper.CenteredColeHopfValue

@[expose] public section


/-! Banach-valued Gaussian moment polynomials for the first three spatial
Cole–Hopf jets. Their joint analytic regularity uses actual tilted averages;
spatial derivative identification is kept separate from this parameter proof. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff
namespace DepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000

def terminalJetCLM (i : Fin 3) : TerminalSpace→L[ℝ](ℝ →ᵇ ℝ) :=
  LinearMap.mkContinuous
    {toFun:=fun g=>terminalJet g i
     map_add':=fun g h=>rfl
     map_smul':=fun c g=>rfl}
    1 (fun g=>by
      convert! norm_terminalJet_le g i using 1
      simp only [one_mul])

@[simp] theorem terminalJetCLM_apply (i : Fin 3) (g : TerminalSpace) :
    terminalJetCLM i g=terminalJet g i := rfl

def shiftedTerminalJetCLM (i : Fin 3) : TerminalSpace→L[ℝ]GaussianObservable :=
  (BoundedContinuousFunction.compContinuousCLM ℝ ℝ
    ⟨fun s:ℝ×ℝ=>s.2+s.1,by fun_prop⟩).comp (terminalJetCLM i)

@[simp] theorem shiftedTerminalJetCLM_apply (i : Fin 3) (g : TerminalSpace) (s : ℝ×ℝ) :
    shiftedTerminalJetCLM i g s=terminalJet g i (s.2+s.1) := rfl

def terminalGaussianMoment (H : ColeHopfParameter→GaussianObservable) (p : ColeHopfParameter) : ℝ →ᵇ ℝ :=
  tiltedGaussianOperator (p,H p)

theorem analyticAt_terminalGaussianMoment (H : ColeHopfParameter→GaussianObservable)
    (p : ColeHopfParameter) (hv : 0<p.1.2) (hH : AnalyticAt ℝ H p) :
    AnalyticAt ℝ (terminalGaussianMoment H) p :=
  (analyticAt_tiltedGaussianOperator (p,H p) hv).comp
    (f:=fun q:ColeHopfParameter=>(q,H q)) (analyticAt_id.prod hH)

def terminalGaussianJetOne (p : ColeHopfParameter) : ℝ →ᵇ ℝ :=
  terminalGaussianMoment (fun q=>shiftedTerminalJetCLM 0 q.2) p

def terminalGaussianJetTwo (p : ColeHopfParameter) : ℝ →ᵇ ℝ :=
  terminalGaussianMoment (fun q=>shiftedTerminalJetCLM 1 q.2) p+
    p.1.1 • (terminalGaussianMoment (fun q=>(shiftedTerminalJetCLM 0 q.2)^2) p-
      terminalGaussianJetOne p^2)

def terminalGaussianJetThree (p : ColeHopfParameter) : ℝ →ᵇ ℝ :=
  terminalGaussianMoment (fun q=>shiftedTerminalJetCLM 2 q.2) p+
  (3*p.1.1) • (terminalGaussianMoment
      (fun q=>shiftedTerminalJetCLM 0 q.2*shiftedTerminalJetCLM 1 q.2) p-
    terminalGaussianJetOne p*terminalGaussianMoment (fun q=>shiftedTerminalJetCLM 1 q.2) p)+
  p.1.1^2 • (terminalGaussianMoment (fun q=>(shiftedTerminalJetCLM 0 q.2)^3) p-
    (3:ℝ) • (terminalGaussianJetOne p*terminalGaussianMoment (fun q=>(shiftedTerminalJetCLM 0 q.2)^2) p)+
    (2:ℝ) • terminalGaussianJetOne p^3)

theorem analyticAt_shiftedTerminalJet (i : Fin 3) (p : ColeHopfParameter) :
    AnalyticAt ℝ (fun q:ColeHopfParameter=>shiftedTerminalJetCLM i q.2) p :=
  ((shiftedTerminalJetCLM i).analyticAt p.2).comp (f:=fun q:ColeHopfParameter=>q.2) analyticAt_snd

theorem analyticAt_terminalGaussianJetOne (p : ColeHopfParameter) (hv : 0<p.1.2) :
    AnalyticAt ℝ terminalGaussianJetOne p :=
  analyticAt_terminalGaussianMoment _ p hv (analyticAt_shiftedTerminalJet 0 p)

theorem analyticAt_terminalGaussianJetTwo (p : ColeHopfParameter) (hv : 0<p.1.2) :
    AnalyticAt ℝ terminalGaussianJetTwo p := by
  have h0 := analyticAt_shiftedTerminalJet 0 p
  have h1 := analyticAt_shiftedTerminalJet 1 p
  have ha : AnalyticAt ℝ (fun q:ColeHopfParameter=>q.1.1) p :=
    analyticAt_fst.comp analyticAt_fst
  exact (analyticAt_terminalGaussianMoment _ p hv h1).add (ha.smul
    ((analyticAt_terminalGaussianMoment _ p hv (h0.pow 2)).sub
      ((analyticAt_terminalGaussianJetOne p hv).pow 2)))

theorem analyticAt_terminalGaussianJetThree (p : ColeHopfParameter) (hv : 0<p.1.2) :
    AnalyticAt ℝ terminalGaussianJetThree p := by
  have h0 := analyticAt_shiftedTerminalJet 0 p
  have h1 := analyticAt_shiftedTerminalJet 1 p
  have h2 := analyticAt_shiftedTerminalJet 2 p
  have ha : AnalyticAt ℝ (fun q:ColeHopfParameter=>q.1.1) p :=
    analyticAt_fst.comp analyticAt_fst
  have hJ := analyticAt_terminalGaussianJetOne p hv
  exact ((analyticAt_terminalGaussianMoment _ p hv h2).add
    ((analyticAt_const.mul ha).smul
      ((analyticAt_terminalGaussianMoment _ p hv (h0.mul h1)).sub
        (hJ.mul (analyticAt_terminalGaussianMoment _ p hv h1))))).add
      ((ha.pow 2).smul
        (((analyticAt_terminalGaussianMoment _ p hv (h0.pow 3)).sub
          ((hJ.mul (analyticAt_terminalGaussianMoment _ p hv (h0.pow 2))).const_smul (c:=(3:ℝ)))).add
          ((hJ.pow 3).const_smul (c:=(2:ℝ)))))

theorem norm_terminalGaussianJetOne_le (p : ColeHopfParameter) (hv : 0<p.1.2) :
    ‖terminalGaussianJetOne p‖≤‖terminalJet p.2 0‖ := by
  exact (norm_tiltedGaussianOperator_le _ hv).trans
    (BoundedContinuousFunction.norm_compContinuous_le _ _)

end DepthPaper
