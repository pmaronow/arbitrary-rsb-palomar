module

public import DepthPaper.CutoffErrorMixedDerivatives
public import DepthPaper.CoordinateWordJets

@[expose] public section


/-! Ordered coordinate derivatives of the actual terminal error are
identified by continuous linear point evaluations with the genuine scalar
logarithmic differential algebra. No permutation of partials is assumed. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal BoundedContinuousFunction
namespace DepthPaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64
open ColeHopfFoundation.ProbabilityTheory

def cutoffErrorDomain : Set (ℝ×ℝ):=Ioo (0:ℝ) 2 ×ˢ Ioi (0:ℝ)

theorem isOpen_cutoffErrorDomain : IsOpen cutoffErrorDomain := isOpen_Ioo.prod isOpen_Ioi

theorem contDiffOn_cutoffErrorTerminal :
    ContDiffOn ℝ ∞ (fun p:ℝ×ℝ=>cutoffErrorTerminal p.1 p.2) cutoffErrorDomain :=
  fun p hp=>(contDiffAt_cutoffErrorTerminal hp.1 hp.2).contDiffWithinAt

theorem terminalValue_cutoffErrorTerminal {m V : ℝ}
    (hm : m∈Ioo (0:ℝ) 2) (hV : 0≤V) (x : ℝ) :
    terminalValue (cutoffErrorTerminal m V) x=logarithmicError m V x := by
  rw [cutoffErrorTerminal,terminalValue_sub,terminalValue_cutoffTerminal m V hV x,
    coleHopf_largeVariance_expansion m V.toNNReal x,Real.coe_toNNReal V hV,
    terminalValue_scaledLogCoshTerminal m hm.1.ne',
    largeVarianceError_real_eq_logarithmicError hm hV x]
  unfold cutoffLeadingConstant
  rw [div_eq_mul_inv]
  ring

def logarithmicAxisDerivative (i : Fin 2) (e : LogDeficitExpr MassResidualNormalizerExpr) :
    LogDeficitExpr MassResidualNormalizerExpr := if i=0 then e.dm else e.massDV

def logarithmicWordDerivative : List (Fin 2)→LogDeficitExpr MassResidualNormalizerExpr→
    LogDeficitExpr MassResidualNormalizerExpr
  | [],e=>e
  | i::w,e=>logarithmicAxisDerivative i (logarithmicWordDerivative w e)

theorem terminalValue_cutoffError_coordinateWordJet
    (w : List (Fin 2)) {p : ℝ×ℝ} (hp : p∈cutoffErrorDomain) (x : ℝ) :
    terminalValue (coordinateWordJet (fun q:ℝ×ℝ=>cutoffErrorTerminal q.1 q.2) w p) x=
      (logarithmicWordDerivative w errorMassBaseExpr).physicalEval p.1 p.2 x := by
  induction w generalizing p with
  | nil =>
    exact terminalValue_cutoffErrorTerminal hp.1 hp.2.le x
  | cons i w ih =>
    let J:=coordinateWordJet (fun q:ℝ×ℝ=>cutoffErrorTerminal q.1 q.2) w
    let e:=logarithmicWordDerivative w errorMassBaseExpr
    have hJ:ContDiffAt ℝ ∞ J p :=
      (contDiffOn_coordinateWordJet isOpen_cutoffErrorDomain contDiffOn_cutoffErrorTerminal w p hp).contDiffAt
        (isOpen_cutoffErrorDomain.mem_nhds hp)
    have hFD := (terminalEvalCLM x).hasFDerivAt.comp p
      (hJ.differentiableAt (by simp)).hasFDerivAt
    fin_cases i
    · have ha:=hFD.comp_hasDerivAt p.1
        ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
      have he:(fun r=>terminalValue (J (r,p.2)) x)=ᶠ[𝓝 p.1]
          (fun r=>e.physicalEval r p.2 x) := by
        filter_upwards [isOpen_Ioo.mem_nhds hp.1] with r hr
        exact ih ⟨hr,hp.2⟩
      have hb:=(e.hasDerivAt_physicalEval_mass hp.1 hp.2 x).congr_of_eventuallyEq he
      exact ha.unique hb
    · have ha:=hFD.comp_hasDerivAt p.2
        ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
      have he:(fun V=>terminalValue (J (p.1,V)) x)=ᶠ[𝓝 p.2]
          (fun V=>e.physicalEval p.1 V x) := by
        filter_upwards [isOpen_Ioi.mem_nhds hp.2] with V hV
        exact ih ⟨hp.1,hV⟩
      have hb:=(e.hasDerivAt_physicalEval_variance hp.1 hp.2 x).congr_of_eventuallyEq he
      exact ha.unique hb

end DepthPaper
