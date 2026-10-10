module

public import DepthPaper.RevisedEntropyRecursion
public import DepthPaper.ColeHopfChain

@[expose] public section

/-! The terminal-direction derivative of every genuine finite constant-CDF
recursion equals the terminal expectation along the actual optimal diffusion.
This statement uses the proved transition law rather than a supplied law or
an adjoint-pairing hypothesis. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ContDiff

namespace DepthPaper
open FourPapersCommon
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 64

theorem revisedEntropy_grid_potential_recursion
    (ξ : AdmissibleEvenMixture) (μ : ParisiMeasure)
    (L : ℕ) (q : Fin (L + 1) → ℝ) (d : Fin L → ℝ × ℝ)
    (hq : ∀ i, q i ∈ Icc (0 : ℝ) 1)
    (ho : ∀ i : Fin L, q i.castSucc < q i.succ)
    (hv : ∀ i, 0 < (d i).2)
    (hvar : ∀ i, (d i).2 = ξ.first (q i.succ) - ξ.first (q i.castSucc))
    (hc : ∀ i : Fin L, ∀ s ∈ Ico (q i.castSucc) (q i.succ),
      Paper.parisiCDF μ s = (d i).1)
    (g : TerminalSpace)
    (ht : ∀ x, mixedPotential ξ μ (q (Fin.last L), x) = terminalValue g x)
    (x : ℝ) :
    mixedPotential ξ μ (q 0, x) = terminalValue (coleHopfRecursion L (d, g)) x := by
  apply coleHopf_chain_eq_recursion L d g
    (fun i y => mixedPotential ξ μ (q i, y)) hv ht
  intro i y
  rw [hvar i]
  exact mixedPotential_coleHopf_on_constantCDF ξ μ (hq i.castSucc) (hq i.succ)
    (ho i) (hc i) y

theorem revisedEntropy_grid_terminal_expectation
    (ξ : AdmissibleEvenMixture) (h : ℝ) (μ : ParisiMeasure)
    (L : ℕ) (q : Fin (L + 1) → ℝ) (d : Fin L → ℝ × ℝ)
    (hq : ∀ i, q i ∈ Icc (0 : ℝ) 1)
    (ho : ∀ i : Fin L, q i.castSucc < q i.succ)
    (hv : ∀ i, 0 < (d i).2)
    (hvar : ∀ i, (d i).2 = ξ.first (q i.succ) - ξ.first (q i.castSucc))
    (hc : ∀ i : Fin L, ∀ s ∈ Ico (q i.castSucc) (q i.succ),
      Paper.parisiCDF μ s = (d i).1)
    (g k : TerminalSpace)
    (ht : ∀ x, mixedPotential ξ μ (q (Fin.last L), x) = terminalValue g x)
    (C : ℝ) (hk : ∀ x, ‖terminalValue k x‖ ≤ C) :
    (∫ sample, terminalValue k (mixedState ξ h μ sample (q (Fin.last L)))
      ∂Paper.canonicalBrownianMeasure) =
    ∫ sample, terminalValue (revisedColeHopfRecursionDerivative L d g k)
      (mixedState ξ h μ sample (q 0)) ∂Paper.canonicalBrownianMeasure := by
  induction L generalizing g k with
  | zero =>
    have hd : d = Fin.elim0 := by funext i; exact Fin.elim0 i
    subst d
    rw [revisedColeHopfRecursionDerivative_zero]
    rfl
  | succ L ih =>
    let dt : Fin L → ℝ × ℝ := fun i => d i.succ
    let qt : Fin (L + 1) → ℝ := fun i => q i.succ
    let G := coleHopfRecursion L (dt, g)
    let K := revisedColeHopfRecursionDerivative L dt g k
    have hqt : ∀ i, qt i ∈ Icc (0 : ℝ) 1 := fun i => hq i.succ
    have hot : ∀ i : Fin L, qt i.castSucc < qt i.succ := by
      intro i
      simpa only [qt, Fin.succ_castSucc] using ho i.succ
    have hvt : ∀ i, 0 < (dt i).2 := fun i => hv i.succ
    have hvart : ∀ i, (dt i).2 = ξ.first (qt i.succ) - ξ.first (qt i.castSucc) := by
      intro i
      simpa only [dt, qt, Fin.succ_castSucc] using hvar i.succ
    have hct : ∀ i : Fin L, ∀ s ∈ Ico (qt i.castSucc) (qt i.succ),
        Paper.parisiCDF μ s = (dt i).1 := by
      intro i s hs
      apply hc i.succ s
      simpa only [qt, Fin.succ_castSucc] using hs
    have htt : ∀ x, mixedPotential ξ μ (qt (Fin.last L), x) = terminalValue g x := by
      simpa only [qt, Fin.succ_last] using ht
    have htail := ih qt dt hqt hot hvt hvart hct g k htt hk
    have hG : ∀ x, mixedPotential ξ μ (q (0 : Fin (L + 1)).succ, x) = terminalValue G x :=
      revisedEntropy_grid_potential_recursion ξ μ L qt dt hqt hot hvt hvart hct g htt
    have hK : ∀ x, ‖terminalValue K x‖ ≤ C :=
      norm_revisedColeHopfRecursionDerivative_value_le L dt hvt g k C hk
    have hcell := revisedMixedState_constantCDF_expectation ξ h μ
      (hq (0 : Fin (L + 1)).castSucc) (hq (0 : Fin (L + 1)).succ) (ho 0) (hc 0)
      (terminalValue K) (contDiff_terminalValue K).continuous.measurable C hK
    rw [← hvar 0, show (fun x => mixedPotential ξ μ (q (0 : Fin (L + 1)).succ, x)) =
      terminalValue G from funext hG] at hcell
    rw [revisedColeHopfRecursionDerivative_succ L d hv g k]
    calc
      _ = ∫ sample, terminalValue K (mixedState ξ h μ sample (q (0 : Fin (L + 1)).succ))
          ∂Paper.canonicalBrownianMeasure := by
        simpa only [qt, dt, K, Fin.succ_last] using htail
      _ = ∫ sample, (∫ y, terminalValue K y ∂FRSB.constantMassKernel (d 0).1
          (d 0).2.toNNReal (terminalValue G) (mixedState ξ h μ sample (q 0)))
          ∂Paper.canonicalBrownianMeasure := by
        simpa only [Fin.castSucc_zero] using hcell
      _ = _ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun sample =>
          (terminalValue_revisedColeHopfTerminalDerivative_kernel (d 0).1 (d 0).2
            (hv 0) G K (mixedState ξ h μ sample (q 0))).symm

end DepthPaper
