module

public import FourPapersCommon.BinaryPrefixMass

@[expose] public section


/-! The exact entropy chain and the decrease of conditional entropy upon
conditioning on all other spins. Both are proved on the actual finite cube. -/
noncomputable section
open scoped BigOperators
namespace FourPapersCommon

def prefixConditional {n : ℕ} (p : StrictFiniteProbability (BinaryConfiguration n))
    (i : Fin n) (σ : BinaryConfiguration n) : ℝ :=
  prefixMass p (i.val+1) σ/prefixMass p i.val σ

def fullConditional {n : ℕ} (p : StrictFiniteProbability (BinaryConfiguration n))
    (i : Fin n) (σ : BinaryConfiguration n) : ℝ :=
  p.weight σ/(p.weight σ+p.weight (flipSpin i σ))

theorem prefixConditional_pos {n : ℕ} (p : StrictFiniteProbability (BinaryConfiguration n))
    (i : Fin n) (σ : BinaryConfiguration n) : 0 < prefixConditional p i σ :=
  div_pos (prefixMass_pos p _ σ) (prefixMass_pos p _ σ)

theorem fullConditional_pos {n : ℕ} (p : StrictFiniteProbability (BinaryConfiguration n))
    (i : Fin n) (σ : BinaryConfiguration n) : 0 < fullConditional p i σ :=
  div_pos (p.positive σ) (add_pos (p.positive σ) (p.positive _))

theorem prefixConditional_add_flip {n : ℕ} (p : StrictFiniteProbability (BinaryConfiguration n))
    (i : Fin n) (σ : BinaryConfiguration n) :
    prefixConditional p i σ+prefixConditional p i (flipSpin i σ)=1 := by
  unfold prefixConditional
  rw [prefixMass_flip_before p i le_rfl,← add_div,prefixMass_succ_add_flip]
  exact div_self (prefixMass_pos p _ σ).ne'

theorem weighted_conditional_ratio_total {n : ℕ} (p : StrictFiniteProbability (BinaryConfiguration n))
    (i : Fin n) :
    (∑ σ,p.weight σ*(prefixConditional p i σ/fullConditional p i σ))=1 := by
  have he (σ : BinaryConfiguration n) :
      p.weight σ*(prefixConditional p i σ/fullConditional p i σ) =
      p.weight σ*prefixConditional p i σ+
        p.weight (flipSpin i σ)*prefixConditional p i σ := by
    unfold fullConditional
    field_simp [(p.positive σ).ne',(add_pos (p.positive σ) (p.positive _)).ne']
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  have hs : (∑ σ,p.weight (flipSpin i σ)*prefixConditional p i σ) =
      ∑ σ,p.weight σ*prefixConditional p i (flipSpin i σ) := by
    have hh := (flipSpinEquiv i).sum_comp
      (fun σ => p.weight (flipSpin i σ)*prefixConditional p i σ)
    simpa only [flipSpinEquiv,Equiv.coe_fn_mk,flipSpin_involutive] using hh.symm
  rw [hs,← Finset.sum_add_distrib]
  simp_rw [← mul_add,prefixConditional_add_flip,mul_one]
  exact p.total

theorem expected_prefix_log_le_full_log {n : ℕ} (p : StrictFiniteProbability (BinaryConfiguration n))
    (i : Fin n) :
    (∑ σ,p.weight σ*Real.log (prefixConditional p i σ)) ≤
      ∑ σ,p.weight σ*Real.log (fullConditional p i σ) := by
  have hh := p.weighted_log_ratio_nonpos (fun σ => prefixConditional p i σ/fullConditional p i σ)
    (fun σ => div_pos (prefixConditional_pos p i σ) (fullConditional_pos p i σ))
    (weighted_conditional_ratio_total p i)
  simp_rw [Real.log_div (prefixConditional_pos p i _).ne' (fullConditional_pos p i _).ne',mul_sub] at hh
  rw [Finset.sum_sub_distrib] at hh
  linarith

theorem sum_prefix_log_eq_log_weight {n : ℕ} (p : StrictFiniteProbability (BinaryConfiguration n))
    (σ : BinaryConfiguration n) :
    (∑ i : Fin n,Real.log (prefixConditional p i σ)) = Real.log (p.weight σ) := by
  simp only [prefixConditional,Real.log_div (prefixMass_pos p _ σ).ne' (prefixMass_pos p _ σ).ne']
  calc
    _ = ∑ k ∈ Finset.range n,(Real.log (prefixMass p (k+1) σ)-Real.log (prefixMass p k σ)) :=
      Fin.sum_univ_eq_sum_range _ n
    _ = Real.log (prefixMass p n σ)-Real.log (prefixMass p 0 σ) :=
      Finset.sum_range_sub (fun k => Real.log (prefixMass p k σ)) n
    _ = _ := by simp

theorem entropy_eq_prefix_chain {n : ℕ} (p : StrictFiniteProbability (BinaryConfiguration n)) :
    p.entropy = -∑ i : Fin n,∑ σ,p.weight σ*Real.log (prefixConditional p i σ) := by
  unfold StrictFiniteProbability.entropy
  simp_rw [← sum_prefix_log_eq_log_weight p,Finset.mul_sum]
  rw [Finset.sum_comm]

theorem entropy_ge_sum_full_conditional {n : ℕ} (p : StrictFiniteProbability (BinaryConfiguration n)) :
    -(∑ i : Fin n,∑ σ,p.weight σ*Real.log (fullConditional p i σ)) ≤ p.entropy := by
  rw [entropy_eq_prefix_chain]
  exact neg_le_neg (Finset.sum_le_sum (fun i _ => expected_prefix_log_le_full_log p i))

end FourPapersCommon
