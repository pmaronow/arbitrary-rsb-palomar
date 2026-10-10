module

public import DepthPaper.EndpointMassRegularity

@[expose] public section


/-! The mixed mass/endpoint derivative consumes exactly two genuine
Fréchet orders of the scalar remainder. These operator norm bounds apply
at the mass-one boundary through the proved open smooth extension. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 900000
set_option maxSynthPendingDepth 64

theorem norm_lowerEndpointDirection {r : ℕ} : ‖lowerEndpointDirection (r:=r)‖=1 := by
  simp [lowerEndpointDirection,Prod.norm_def]

theorem norm_lowerMassDirection {r : ℕ} : ‖lowerMassDirection (r:=r)‖=1 := by
  simp [lowerMassDirection,Prod.norm_def]

theorem norm_iteratedFDeriv_directional_derivative_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E→ℝ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (d : E) (hd : ‖d‖≤1) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y=>fderiv ℝ f y d) x‖≤‖iteratedFDeriv ℝ (j+1) f x‖ := by
  let L : (E→L[ℝ]ℝ)→L[ℝ]ℝ := ContinuousLinearMap.apply ℝ ℝ d
  have hL : ‖L‖≤1 := by
    apply L.opNorm_le_bound zero_le_one
    intro A
    exact (A.le_opNorm d).trans ((mul_le_mul_of_nonneg_left hd (norm_nonneg A)).trans_eq (by ring))
  have hh := L.norm_iteratedFDeriv_comp_left (hf.fderiv_right (m:=∞) (by simp))
    (show (j:ℕ∞ω)≤∞ by simp)
  change ‖iteratedFDeriv ℝ j (fun y=>fderiv ℝ f y d) x‖≤_ at hh
  exact hh.trans ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans_eq (by
    rw [one_mul,norm_iteratedFDeriv_fderiv]))

theorem norm_iteratedFDeriv_lowerRemainderMassEndpointDerivative_le (Ξ : AdmissibleCovariance)
    {r : ℕ} (p : ℕ) (qc : ℝ) {x : CutoffInputParameter r}
    (hf : ContDiffAt ℝ ∞ (lowerRecursionErrorRaw Ξ p qc) x) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (lowerRemainderMassEndpointDerivative Ξ p qc) x‖≤
      ‖iteratedFDeriv ℝ (j+2) (lowerRecursionErrorRaw Ξ p qc) x‖ := by
  have hg : ContDiffAt ℝ ∞ (lowerRemainderEndpointDerivative Ξ p qc) x :=
    (hf.fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const
  exact (norm_iteratedFDeriv_directional_derivative_le hg lowerMassDirection
    norm_lowerMassDirection.le j).trans
      (norm_iteratedFDeriv_directional_derivative_le hf lowerEndpointDirection
        norm_lowerEndpointDirection.le (j+1))

end DepthPaper
