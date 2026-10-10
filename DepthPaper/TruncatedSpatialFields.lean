module

public import DepthPaper.TruncatedRecursionCells
public import Mathlib.Topology.Order.ProjIcc

@[expose] public section


/-! Actual first, second and third spatial derivatives of the truncated
Gaussian recursion, with uniform spatial and overlap convergence. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction NNReal
namespace DepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000

def terminalFamilyJet {qc : ℝ} (F : C(TruncatedClockDomain qc,TerminalSpace)) (j : Fin 3) :
    (TruncatedClockDomain qc × ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => terminalJet (F p.1) j p.2)
    (continuous_eval.comp (((terminalJetCLM j).continuous.comp
      (F.continuous.comp continuous_fst)).prodMk continuous_snd))
    ‖F‖ (fun p => (BoundedContinuousFunction.norm_coe_le_norm (terminalJet (F p.1) j) p.2).trans
      ((norm_terminalJet_le _ _).trans (F.norm_coe_le_norm p.1)))

@[simp] theorem terminalFamilyJet_apply {qc : ℝ}
    (F : C(TruncatedClockDomain qc,TerminalSpace)) (j : Fin 3) (p : TruncatedClockDomain qc × ℝ) :
    terminalFamilyJet F j p = terminalJet (F p.1) j p.2 := rfl

theorem norm_terminalFamilyJet_le {qc : ℝ} (F : C(TruncatedClockDomain qc,TerminalSpace)) (j : Fin 3) :
    ‖terminalFamilyJet F j‖ ≤ ‖F‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg F)).mpr fun p =>
    (BoundedContinuousFunction.norm_coe_le_norm (terminalJet (F p.1) j) p.2).trans
      ((norm_terminalJet_le _ _).trans (F.norm_coe_le_norm p.1))

def terminalFamilyJetCLM {qc : ℝ} (j : Fin 3) :
    C(TruncatedClockDomain qc,TerminalSpace) →L[ℝ] ((TruncatedClockDomain qc × ℝ) →ᵇ ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun F => terminalFamilyJet F j
      map_add' := fun F G => by ext p; rfl
      map_smul' := fun c F => by ext p; rfl }
    1 (fun F => by
      change ‖terminalFamilyJet F j‖ ≤ 1*‖F‖
      simpa only [one_mul] using norm_terminalFamilyJet_le F j)

def truncatedSpatialFieldBCF {L : ℕ} {qc : ℝ} (p : TruncatedRecursionParameter L qc) (j : Fin 3) :
    (TruncatedClockDomain qc × ℝ) →ᵇ ℝ := terminalFamilyJet (truncatedPotentialFamily p) j

@[simp] theorem truncatedSpatialFieldBCF_apply {L : ℕ} {qc : ℝ}
    (p : TruncatedRecursionParameter L qc) (j : Fin 3) (q : TruncatedClockDomain qc) (x : ℝ) :
    truncatedSpatialFieldBCF p j (q,x) = terminalJet (truncatedPotentialTerminal p q) j x := rfl

theorem continuous_truncatedSpatialFieldBCF {L : ℕ} {qc : ℝ} (j : Fin 3) :
    Continuous (fun p : TruncatedRecursionParameter L qc => truncatedSpatialFieldBCF p j) :=
  (terminalFamilyJetCLM j).continuous.comp continuous_truncatedPotentialFamily

def truncatedSpatialField {L : ℕ} {qc : ℝ} (hqc : 0 ≤ qc)
    (p : TruncatedRecursionParameter L qc) (j : Fin 3) : (ℝ × ℝ) →ᵇ ℝ :=
  (truncatedSpatialFieldBCF p j).compContinuous
    ⟨fun s : ℝ×ℝ => (projIcc 0 qc hqc s.1,s.2),by fun_prop⟩

@[simp] theorem truncatedSpatialField_apply {L : ℕ} {qc : ℝ} (hqc : 0 ≤ qc)
    (p : TruncatedRecursionParameter L qc) (j : Fin 3) (q x : ℝ) :
    truncatedSpatialField hqc p j (q,x) =
      terminalJet (truncatedPotentialTerminal p (projIcc 0 qc hqc q)) j x := rfl

theorem continuous_truncatedSpatialField {L : ℕ} {qc : ℝ} (hqc : 0 ≤ qc) (j : Fin 3) :
    Continuous (fun p : TruncatedRecursionParameter L qc => truncatedSpatialField hqc p j) :=
  (BoundedContinuousFunction.compContinuousCLM ℝ ℝ
    ⟨fun s : ℝ×ℝ => (projIcc 0 qc hqc s.1,s.2),by fun_prop⟩).continuous.comp
      (continuous_truncatedSpatialFieldBCF j)

theorem norm_truncatedSpatialField_le {L : ℕ} {qc : ℝ} (hqc : 0 ≤ qc)
    (p : TruncatedRecursionParameter L qc) (j : Fin 3) :
    ‖truncatedSpatialField hqc p j‖ ≤ ‖truncatedPotentialFamily p‖ :=
  (BoundedContinuousFunction.norm_compContinuous_le _ _).trans (norm_terminalFamilyJet_le _ j)

theorem norm_truncatedSpatialField_zero_le_one {L : ℕ} {qc : ℝ} (hqc : 0 ≤ qc)
    (p : TruncatedRecursionParameter L qc) (hm : Monotone p.1) (hg : ‖terminalJet p.2.2.2 0‖ ≤ 1) :
    ‖truncatedSpatialField hqc p 0‖ ≤ 1 := by
  apply (BoundedContinuousFunction.norm_le zero_le_one).mpr
  intro qx
  rw [truncatedSpatialField_apply]
  exact (BoundedContinuousFunction.norm_coe_le_norm _ _).trans
    ((norm_terminalJet_truncatedPotentialTerminal_le p hm _).trans hg)

theorem hasDerivAt_truncatedSpatialField_zero {L : ℕ} {qc : ℝ} (hqc : 0 ≤ qc)
    (p : TruncatedRecursionParameter L qc) (q x : ℝ) :
    HasDerivAt (fun y => truncatedSpatialField hqc p 0 (q,y))
      (truncatedSpatialField hqc p 1 (q,x)) x :=
  hasDerivAt_terminalJet_zero (truncatedPotentialTerminal p (projIcc 0 qc hqc q)) x

theorem hasDerivAt_truncatedSpatialField_one {L : ℕ} {qc : ℝ} (hqc : 0 ≤ qc)
    (p : TruncatedRecursionParameter L qc) (q x : ℝ) :
    HasDerivAt (fun y => truncatedSpatialField hqc p 1 (q,y))
      (truncatedSpatialField hqc p 2 (q,x)) x :=
  hasDerivAt_terminalJet_one (truncatedPotentialTerminal p (projIcc 0 qc hqc q)) x

theorem lipschitzWith_truncatedSpatialField_zero {L : ℕ} {qc : ℝ} (hqc : 0 ≤ qc)
    (p : TruncatedRecursionParameter L qc) (q : ℝ) :
    LipschitzWith ‖truncatedPotentialFamily p‖₊ (fun x => truncatedSpatialField hqc p 0 (q,x)) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun x => (hasDerivAt_truncatedSpatialField_zero hqc p q x).differentiableAt)
  intro x
  rw [(hasDerivAt_truncatedSpatialField_zero hqc p q x).deriv]
  exact_mod_cast (BoundedContinuousFunction.norm_coe_le_norm (truncatedSpatialField hqc p 1) (q,x)).trans
    (norm_truncatedSpatialField_le hqc p 1)

end DepthPaper
