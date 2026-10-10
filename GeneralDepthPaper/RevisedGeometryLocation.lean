module

public import GeneralDepthPaper.StationaryGardnerAsymptotics

@[expose] public section

/-! A common support cutoff and common endpoint scale for all actual
stationary candidates in Revision (16), Theorem 4.12. -/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology
namespace GeneralDepthPaper

def GardnerLocationScale (C : ℝ) (p : ℕ) (m lam Q : ℝ) : Prop :=
  C⁻¹ * (p : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (-m ^ 2 * lam * (p : ℝ) / 2) ≤ 1 - Q ∧
  1 - Q ≤ C * (p : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (-m ^ 2 * lam * (p : ℝ) / 2)

namespace LimitingStandingData
variable {Ξ : AdmissibleCovariance} {r : ℕ} {seed : AtomicPoint r}

theorem revisedCandidateLocation_eventually (d : LimitingStandingData Ξ seed) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ p : ℕ in atTop, ∀ _he : Even p,
      ∀ theta ∈ d.parameterWindow,
      ∀ hz : IsAtomicPoint (d.stationaryBranch p theta),
        let z := d.stationaryBranch p theta
        let Q := distinguishedOverlap Ξ p d.cutoff d.stripRateLower d.stripRateUpper
          (z, (theta.2, theta.1))
        FRSB.parisiSupport (atomicMeasure z hz) ⊆ Icc (0 : ℝ) d.cutoff ∧
        (Q : ℝ) ∈ Ioo d.cutoff 1 ∧
        GardnerLocationScale C p theta.2 theta.1 Q := by
  obtain ⟨b, hb, D, hD, Hr⟩ := distinguished_endpoint_contact_eventually Ξ
    (isCompact_closedBall seed d.radius) d.ball_valid d.massLower_mem d.couplingLower_pos
    d.couplingLower_le_upper d.cutoff_mem d.ball_below_cutoff
    d.strip_rates.1 d.strip_rates.2.1 d.strip_rates.2.2
  obtain ⟨_, _, _, _, _, Hs⟩ := d.stationaryBranch_eventually
  let C := max 1 (max D b⁻¹) + 1
  have hC : 1 ≤ C := by dsimp [C]; linarith [le_max_left (1 : ℝ) (max D b⁻¹)]
  have hDC : D ≤ C := by
    dsimp [C]
    linarith [le_max_left D b⁻¹, le_max_right (1 : ℝ) (max D b⁻¹)]
  have hbC : b⁻¹ ≤ C := by
    dsimp [C]
    linarith [le_max_right D b⁻¹, le_max_right (1 : ℝ) (max D b⁻¹)]
  have hCi : C⁻¹ ≤ b := by
    simpa only [one_div, inv_inv] using
      one_div_le_one_div_of_le (inv_pos.mpr hb) hbC
  refine ⟨C, hC, ?_⟩
  filter_upwards [Hr, Hs,
    endpointStrip_above_cutoff_eventually (CQ := d.stripRateUpper) d.cutoff_mem.2
      d.strip_rates.1] with p hr hs habove he theta ht hz
  obtain ⟨hp, hn, HR⟩ := hr.2 he
  let z := d.stationaryBranch p theta
  let Q := distinguishedOverlap Ξ p d.cutoff d.stripRateLower d.stripRateUpper
    (z, (theta.2, theta.1))
  have hzball : z ∈ closedBall seed d.radius :=
    ball_subset_closedBall (hs he theta ht).1
  have hlast : atomicLocation z (Fin.last r) < d.cutoff :=
    d.ball_below_cutoff z hzball
  have H := HR (z, (theta.2, theta.1)) hzball ht.2 ht.1
  have hstrip : (Q : ℝ) ∈ endpointStrip d.stripRateLower d.stripRateUpper p :=
    Ioo_subset_Icc_self H.2.1
  refine ⟨?_, ⟨habove Q hstrip, (endpointStrip_mem_unit d.strip_rates.1 p hstrip).2⟩, ?_⟩
  · rw [parisiSupport_atomicMeasure]
    rintro q ⟨i, rfl⟩
    exact ⟨(atomicOverlap z hz i).property.1,
      (hz.1.monotone (Fin.le_last i)).trans hlast.le⟩
  · constructor
    · exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCi (Real.rpow_nonneg (Nat.cast_nonneg p) _))
        (Real.exp_pos _).le).trans H.2.2.2.2.1
    · exact H.2.2.2.2.2.1.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hDC (Real.rpow_nonneg (Nat.cast_nonneg p) _))
        (Real.exp_pos _).le)

end LimitingStandingData
end GeneralDepthPaper
