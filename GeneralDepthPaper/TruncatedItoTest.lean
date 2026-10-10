module

public import GeneralDepthPaper.TruncatedMomentContinuity
public import FRSB.InteriorTimeCap
public import FRSB.ItoSquareTest

@[expose] public section


/-! Globally C¹,² capped actual-gradient tests on each open truncated cell.
Only the terminal C³ jets are used; no infinite terminal smoothness is assumed. -/
noncomputable section
open Set Filter StochasticCalculus
open scoped Topology NNReal BoundedContinuousFunction ContDiff
namespace GeneralDepthPaper
open Paper FourPapersCommon FRSB
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem contDiff_terminalJet_zero (g : TerminalSpace) : ContDiff ℝ 2 (terminalJet g 0) := by
  have h : ContDiff ℝ ((2:ℕ∞ω)+1) (terminalValue g) := contDiff_terminalValue g
  have he : deriv (terminalValue g) = terminalJet g 0 :=
    funext fun x => (hasDerivAt_terminalValue g x).deriv
  simpa only [he] using h.deriv'

theorem norm_interiorTimeCapD_le_one (a l r b t : ℝ) (hal : a < l) (hrb : r < b) :
    ‖interiorTimeCapD a l r b t‖ ≤ 1 := by
  have h1 := hjbTimeCapD_nonneg (-l) ((l-a)/2) (-hjbTimeCap r ((b-r)/2) t)
  have h2 := hjbTimeCapD_nonneg r ((b-r)/2) t
  have h1b := hjbTimeCapD_le_one (-l) (by linarith : 0 < (l-a)/2) (-hjbTimeCap r ((b-r)/2) t)
  have h2b := hjbTimeCapD_le_one r (by linarith : 0 < (b-r)/2) t
  rw [interiorTimeCapD,Real.norm_of_nonneg (mul_nonneg h1 h2)]
  exact (mul_le_mul h1b h2b h2 (by norm_num : (0:ℝ) ≤ 1)).trans_eq (one_mul _)

namespace TruncatedParisiData

def gradient {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) (t x : ℝ) : ℝ :=
  d.spatialField 0 (t,x)

def gradientTimeSource {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc)
    (i : Fin (r+1)) (t x : ℝ) : ℝ :=
  -d.covarianceField 2 t/2*(d.spatialField 2 (t,x)+
    2*d.level i*d.spatialField 0 (t,x)*d.spatialField 1 (t,x))

theorem hasDerivAt_gradient_time {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc)
    (i : Fin (r+1)) (t x : ℝ) (ht : t ∈ Ioo (d.node i.castSucc : ℝ) (d.node i.succ : ℝ)) :
    HasDerivAt (fun q => d.gradient q x) (d.gradientTimeSource i t x) t := by
  have h := d.hasDerivAt_spatialField_zero_time i t x ht
  rw [show d.coefficient t = d.level i from
    truncatedCoefficient_eq_level d.parameter d.node_strictMono.monotone t i ⟨ht.1.le,ht.2⟩] at h
  exact h

theorem contDiff_gradient_spatial {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) (t : ℝ) :
    ContDiff ℝ 2 (d.gradient t) :=
  contDiff_terminalJet_zero (truncatedPotentialTerminal d.parameter (projIcc 0 qc d.qc_pos.le t))

def cappedGradient {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc)
    (i : Fin (r+1)) (l b : ℝ) : ℝ → ℝ → ℝ :=
  interiorCappedTest d.gradient (d.node i.castSucc) l b (d.node i.succ)

theorem cappedGradient_regular {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc)
    (i : Fin (r+1)) (l b : ℝ) (hl : (d.node i.castSucc:ℝ) < l)
    (hlb : l ≤ b) (hb : b < (d.node i.succ:ℝ)) :
    Continuous (fun p : ℝ×ℝ => d.cappedGradient i l b p.1 p.2) ∧
      (∀x,Differentiable ℝ (fun t => d.cappedGradient i l b t x)) ∧
      (∀t,ContDiff ℝ 2 (d.cappedGradient i l b t)) ∧
      Continuous (fun p : ℝ×ℝ => itoTimeDerivative (d.cappedGradient i l b) p.1 p.2) ∧
      Continuous (fun p : ℝ×ℝ => itoSpaceDerivative (d.cappedGradient i l b) p.1 p.2) ∧
      Continuous (fun p : ℝ×ℝ => itoSpaceSecondDerivative (d.cappedGradient i l b) p.1 p.2) := by
  apply interiorCappedTest_regular d.gradient (d.gradientTimeSource i)
    (fun t x => d.spatialField 1 (t,x)) (fun t x => d.spatialField 2 (t,x))
    (d.node i.castSucc) l b (d.node i.succ) hl hlb hb
  · exact (d.spatialField 0).continuous
  · have hr : Continuous (fun p : ℝ×ℝ => d.covarianceField 2 p.1) :=
      (d.continuous_covarianceField 2).comp continuous_fst
    exact (hr.neg.div_const 2).mul ((d.spatialField 2).continuous.add
      (((d.spatialField 0).continuous.const_mul (2*d.level i)).mul (d.spatialField 1).continuous))
  · exact (d.spatialField 1).continuous
  · exact (d.spatialField 2).continuous
  · exact fun t ht x => d.hasDerivAt_gradient_time i t x ht
  · exact fun t x => hasDerivAt_truncatedSpatialField_zero d.qc_pos.le d.parameter t x
  · exact fun t x => hasDerivAt_truncatedSpatialField_one d.qc_pos.le d.parameter t x
  · exact d.contDiff_gradient_spatial

theorem cappedGradient_spaceDerivative {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc)
    (i : Fin (r+1)) (l b t x : ℝ) :
    itoSpaceDerivative (d.cappedGradient i l b) t x =
      d.spatialField 1 (interiorTimeCap (d.node i.castSucc) l b (d.node i.succ) t,x) :=
  interiorCappedTest_spaceDerivative d.gradient (fun t x => d.spatialField 1 (t,x))
    (fun t x => hasDerivAt_truncatedSpatialField_zero d.qc_pos.le d.parameter t x) _ _ _ _ _ _

theorem cappedGradient_spaceSecondDerivative {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc)
    (i : Fin (r+1)) (l b t x : ℝ) :
    itoSpaceSecondDerivative (d.cappedGradient i l b) t x =
      d.spatialField 2 (interiorTimeCap (d.node i.castSucc) l b (d.node i.succ) t,x) :=
  interiorCappedTest_spaceSecondDerivative d.gradient (fun t x => d.spatialField 1 (t,x))
    (fun t x => d.spatialField 2 (t,x))
    (fun t x => hasDerivAt_truncatedSpatialField_zero d.qc_pos.le d.parameter t x)
    (fun t x => hasDerivAt_truncatedSpatialField_one d.qc_pos.le d.parameter t x) _ _ _ _ _ _

end TruncatedParisiData
end GeneralDepthPaper
