module

public import FRSB.ForwardBridgeDensity
public import FRSB.WienerReflection

@[expose] public section


/-! Symmetry of the concrete forward gauge and density, proved from the
actual reflected Wiener measure and the actual even Parisi potential. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
namespace FRSB

lemma forwardBridgePoint_neg (β s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (path : ForwardBridgePath) (x : ℝ) (t : Overlap) :
    forwardBridgePoint β s hs (-path) (-x) t = -forwardBridgePoint β s hs path x t := by
  simp only [forwardBridgePoint, ContinuousMap.neg_apply]
  ring

theorem forwardBridgeAction_neg (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) :
    forwardBridgeAction β μ s hs (-path) (-x) = forwardBridgeAction β μ s hs path x := by
  apply integral_congr_ae
  filter_upwards with t
  change (if (t : ℝ) ≤ s then forwardBridgeFraction s t ^ 0 *
    parisiSpatialField β μ 0 (t, forwardBridgePoint β s hs (-path) (-x) t) else 0) = _
  by_cases ht : (t : ℝ) ≤ s
  · simp only [ht, ite_true, pow_zero, one_mul, parisiSpatialField]
    rw [forwardBridgePoint_neg, parisiPotential_even β μ t _ t.property]
  · simp only [ht, ite_false]

theorem forwardBridgeFactor_even (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    forwardBridgeFactor β μ s hs (-x) = forwardBridgeFactor β μ s hs x := by
  have hmeas : AEStronglyMeasurable (fun path => forwardBridgePathFactor β μ s hs path x)
      (canonicalWienerMeasure.map (fun path : ForwardBridgePath => -path)) := by
    rw [canonicalWienerMeasure_reflection]
    exact (integrable_forwardBridgePathFactor β μ s hs x).aestronglyMeasurable
  have hm := integral_map (μ := canonicalWienerMeasure)
    (φ := fun path : ForwardBridgePath => -path)
    (f := fun path => forwardBridgePathFactor β μ s hs path x) (by fun_prop) hmeas
  rw [canonicalWienerMeasure_reflection] at hm
  calc
    _ = ∫ path, forwardBridgePathFactor β μ s hs (-path) x ∂canonicalWienerMeasure := by
      apply integral_congr_ae
      filter_upwards with path
      have he := forwardBridgeAction_neg β μ s hs (-path) x
      simpa only [neg_neg, forwardBridgePathFactor] using congrArg (fun y => Real.exp (-y)) he
    _ = _ := hm.symm

theorem forwardBridgeCorrection_even (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    forwardBridgeCorrection β μ s hs (-x) = forwardBridgeCorrection β μ s hs x := by
  unfold forwardBridgeCorrection
  rw [forwardBridgeFactor_even]

theorem forwardBridgeDensity_even (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    forwardBridgeDensity β μ s hs (-x) = forwardBridgeDensity β μ s hs x := by
  unfold forwardBridgeDensity
  rw [parisiPotential_even β μ s x ⟨hs.1.le, hs.2⟩, forwardBridgeFactor_even]
  simp only [heatDensity, neg_sq]

end FRSB
