module

public import GeneralDepthPaper.LimitingBranchWindow

@[expose] public section


/-! The literal positive coupling window and its uniform interior margin
follow from the actual pressure entropy and the actual negative slope. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 1200000

theorem pressureEll_one_pos (Ξ:AdmissibleCovariance) {r:ℕ}
    (z:AtomicPoint r) (hz:IsAtomicPoint z) (hnd:Nondegenerate Ξ z hz) :
    0 < pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) 1 := by
  have he:0 < pressureEntropy (scaledThermodynamicPressure Ξ.toEvenMixture) 1 := by
    simpa only [pressureEntropy,thermodynamicEntropy,one_mul] using (positive_entropy Ξ z hz hnd).2.2.1
  simpa only [pressureEll,one_pow,div_one] using mul_pos (show (0:ℝ)<2 by norm_num) he

theorem limiting_coupling_window (Ξ:AdmissibleCovariance) {r:ℕ}
    (z:AtomicPoint r) (hz:IsAtomicPoint z) (hnd:Nondegenerate Ξ z hz)
    (m0:ℝ) (hm0:m0∈Ioo (0:ℝ) 1) (c:ℝ) (hc:0 < c)
    (hreg:∀m∈Icc m0 1,ContDiffAt ℝ ∞
      (pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture)) m)
    (hslope:∀m∈Icc m0 1,deriv
      (pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture)) m ≤ -2*c) :
    ∃eta:ℝ,0 < eta ∧
      eta < pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) 1/4 ∧
      eta < (pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) m0-
        pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) 1)/4 ∧
      0 < pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) 1-2*eta ∧
      StrictAntiOn (pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture)) (Icc m0 1) ∧
      ∀m∈Icc m0 1,
        pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) 1-2*eta+2*eta ≤
          pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) m ∧
        pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) m ≤
          pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) m0+2*eta-2*eta := by
  let ell:=pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture)
  have hanti:StrictAntiOn ell (Icc m0 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc m0 1)
      (fun m hm=>(hreg m hm).continuousAt.continuousWithinAt)
    intro m hm
    have hb:=hslope m (interior_subset hm)
    linarith
  have hends:m0∈Icc m0 1 ∧ (1:ℝ)∈Icc m0 1 := ⟨⟨le_rfl,hm0.2.le⟩,⟨hm0.2.le,le_rfl⟩⟩
  have hgap:0 < ell m0-ell 1 := sub_pos.mpr (hanti hends.1 hends.2 hm0.2)
  have hpos:0 < ell 1 := pressureEll_one_pos Ξ z hz hnd
  let eta:ℝ:=min (ell 1/8) ((ell m0-ell 1)/8)
  have heta:0 < eta := lt_min (by positivity) (by positivity)
  have he1:eta < ell 1/4 := (min_le_left _ _).trans_lt (by linarith)
  have heg:eta < (ell m0-ell 1)/4 := (min_le_right _ _).trans_lt (by linarith)
  refine ⟨eta,heta,he1,heg,by linarith,hanti,?_⟩
  intro m hm
  have hlo:=hanti.antitoneOn hm hends.2 hm.2
  have hhi:=hanti.antitoneOn hends.1 hm hm.1
  constructor <;> dsimp only [ell] at * <;> linarith

end GeneralDepthPaper
