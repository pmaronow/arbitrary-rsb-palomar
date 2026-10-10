module

public import FRSB.BackwardsDefinitions
public import FRSB.ConstantMassParity

@[expose] public section


noncomputable section
open Set Filter
open scoped Topology
namespace FRSB

theorem backwardD_reflect (β : ℝ) (μ : Paper.ParisiMeasure) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) (n : ℕ) (x : ℝ) :
    backwardD β μ n (t, -x) = (-1 : ℝ) ^ n * backwardD β μ n (t, x) := by
  rw [backwardD, Paper.parisiSpatialField_eq_iteratedDeriv β μ n t (-x) ht,
    backwardD, Paper.parisiSpatialField_eq_iteratedDeriv β μ n t x ht]
  exact parisiPotential_iteratedDeriv_parity β μ t ht n x

theorem backwardZ_odd (β : ℝ) (μ : Paper.ParisiMeasure) (t x : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) : backwardZ β μ (t, -x) = -backwardZ β μ (t, x) := by
  dsimp [backwardZ, backwardZJet, backwardC]
  rw [backwardD_reflect β μ t ht 2 x, backwardD_reflect β μ t ht 3 x]
  norm_num
  ring

theorem backwardQ_even (β : ℝ) (μ : Paper.ParisiMeasure) (m t x : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) : backwardQ β μ m (t, -x) = backwardQ β μ m (t, x) := by
  dsimp [backwardQ, backwardQJet, backwardZxJet, backwardC]
  rw [backwardD_reflect β μ t ht 2 x, backwardD_reflect β μ t ht 3 x,
    backwardD_reflect β μ t ht 4 x]
  norm_num

theorem backwardH_even (β : ℝ) (μ : Paper.ParisiMeasure) (m t x : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) : backwardH β μ m (t, -x) = backwardH β μ m (t, x) := by
  rw [backwardH_eq_z_sq_mC_sub_twoQ, backwardH_eq_z_sq_mC_sub_twoQ,
    backwardZ_odd β μ t x ht, backwardQ_even β μ m t x ht]
  dsimp [backwardC]
  rw [backwardD_reflect β μ t ht 2 x]
  norm_num

theorem backwardHx_odd (β : ℝ) (μ : Paper.ParisiMeasure) (m t x : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) : backwardHx β μ m (t, -x) = -backwardHx β μ m (t, x) := by
  dsimp [backwardHx, backwardHxJet, backwardQxJet, backwardZxxJet, backwardZJet, backwardZxJet, backwardC]
  rw [backwardD_reflect β μ t ht 2 x, backwardD_reflect β μ t ht 3 x,
    backwardD_reflect β μ t ht 4 x, backwardD_reflect β μ t ht 5 x]
  norm_num
  ring

@[simp] theorem backwardZ_at_zero (β : ℝ) (μ : Paper.ParisiMeasure) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) : backwardZ β μ (t, 0) = 0 := by
  have hh := backwardZ_odd β μ t 0 ht
  rw [neg_zero] at hh
  linarith

@[simp] theorem backwardHx_at_zero (β : ℝ) (μ : Paper.ParisiMeasure) (m t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) : backwardHx β μ m (t, 0) = 0 := by
  have hh := backwardHx_odd β μ m t 0 ht
  rw [neg_zero] at hh
  linarith

theorem backwardB_at_zero (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) : backwardB β μ (t, 0) = 0 := by
  rw [backwardB_eq_gradient β μ t 0 ht]
  exact parisiGradient_at_zero β hβ μ t ht

theorem backwardB_strictMono (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) : StrictMono (fun x => backwardB β μ (t, x)) := by
  apply strictMono_of_deriv_pos
  intro x
  change 0 < deriv (fun x => backwardD β μ 1 (t, x)) x
  rw [(hasDerivAt_backwardD β μ 1 t x ht).deriv]
  exact backwardC_pos β hβ μ t x ht

theorem backwardB_nonneg (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (hx : 0 ≤ x) : 0 ≤ backwardB β μ (t, x) := by
  have hh := (backwardB_strictMono β hβ μ t ht).monotone hx
  rw [backwardB_at_zero β hβ μ t ht] at hh
  exact hh

theorem backwardB_pos (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (hx : 0 < x) : 0 < backwardB β μ (t, x) := by
  have hh := (backwardB_strictMono β hβ μ t ht) hx
  change backwardB β μ (t, 0) < backwardB β μ (t, x) at hh
  rw [backwardB_at_zero β hβ μ t ht] at hh
  exact hh

end FRSB
