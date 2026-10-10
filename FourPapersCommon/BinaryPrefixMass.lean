module

public import FourPapersCommon.FiniteEntropy

@[expose] public section


/-! Actual prefix marginal probabilities on a finite spin cube. -/
noncomputable section
open scoped BigOperators
namespace FourPapersCommon
abbrev BinaryConfiguration (n : ℕ) := Fin n → Bool

def flipSpin {n : ℕ} (i : Fin n) (σ : BinaryConfiguration n) : BinaryConfiguration n :=
  Function.update σ i (!(σ i))

@[simp] theorem flipSpin_at {n : ℕ} (i : Fin n) (σ : BinaryConfiguration n) :
    flipSpin i σ i = !(σ i) := by simp [flipSpin]

theorem flipSpin_away {n : ℕ} (i j : Fin n) (σ : BinaryConfiguration n) (hji : j ≠ i) :
    flipSpin i σ j = σ j := by simp [flipSpin,hji]

@[simp] theorem flipSpin_involutive {n : ℕ} (i : Fin n) (σ : BinaryConfiguration n) :
    flipSpin i (flipSpin i σ) = σ := by
  funext j
  by_cases hji : j=i
  · subst j; simp
  · simp [flipSpin_away i j _ hji]

def flipSpinEquiv {n : ℕ} (i : Fin n) : BinaryConfiguration n ≃ BinaryConfiguration n where
  toFun := flipSpin i
  invFun := flipSpin i
  left_inv := flipSpin_involutive i
  right_inv := flipSpin_involutive i

def prefixCompatible {n : ℕ} (k : ℕ) (σ τ : BinaryConfiguration n) : Prop :=
  ∀ j : Fin n,j.val < k → τ j=σ j

instance prefixCompatible_decidable {n : ℕ} (k : ℕ) (σ τ : BinaryConfiguration n) :
    Decidable (prefixCompatible k σ τ) := by
  unfold prefixCompatible
  infer_instance

def prefixMass {n : ℕ} (p : StrictFiniteProbability (BinaryConfiguration n))
    (k : ℕ) (σ : BinaryConfiguration n) : ℝ :=
  ∑ τ : BinaryConfiguration n,if prefixCompatible k σ τ then p.weight τ else 0

theorem prefixCompatible_self {n : ℕ} (k : ℕ) (σ : BinaryConfiguration n) :
    prefixCompatible k σ σ := fun _ _ => rfl

theorem prefixMass_pos {n : ℕ} (p : StrictFiniteProbability (BinaryConfiguration n))
    (k : ℕ) (σ : BinaryConfiguration n) : 0 < prefixMass p k σ := by
  have hh := Finset.single_le_sum (s := (Finset.univ : Finset (BinaryConfiguration n)))
    (f := fun τ => if prefixCompatible k σ τ then p.weight τ else 0)
    (fun τ _ => by split_ifs; exact (p.positive τ).le; exact le_rfl) (Finset.mem_univ σ)
  rw [ite_eq_left (prefixCompatible_self k σ)] at hh
  exact (p.positive σ).trans_le hh

@[simp] theorem prefixMass_zero {n : ℕ} (p : StrictFiniteProbability (BinaryConfiguration n))
    (σ : BinaryConfiguration n) : prefixMass p 0 σ=1 := by
  simpa [prefixMass,prefixCompatible] using p.total

theorem prefixCompatible_full {n : ℕ} (σ τ : BinaryConfiguration n) :
    prefixCompatible n σ τ ↔ τ=σ := by
  constructor
  · intro h; exact funext (fun j => h j j.isLt)
  · intro h; subst τ; exact prefixCompatible_self n σ

@[simp] theorem prefixMass_full {n : ℕ} (p : StrictFiniteProbability (BinaryConfiguration n))
    (σ : BinaryConfiguration n) : prefixMass p n σ=p.weight σ := by
  simp only [prefixMass,prefixCompatible_full]
  simp

theorem prefixCompatible_succ {n : ℕ} (i : Fin n) (σ τ : BinaryConfiguration n) :
    prefixCompatible (i.val+1) σ τ ↔ prefixCompatible i.val σ τ ∧ τ i=σ i := by
  constructor
  · intro h
    exact ⟨fun j hj => h j (by omega),h i (by omega)⟩
  · rintro ⟨h,hi⟩ j hj
    by_cases hji : j.val < i.val
    · exact h j hji
    · have he : j=i := Fin.ext (by omega)
      simpa only [he] using hi

theorem prefixCompatible_flip_before {n : ℕ} (i : Fin n) {k : ℕ} (hk : k ≤ i.val)
    (σ τ : BinaryConfiguration n) : prefixCompatible k (flipSpin i σ) τ ↔ prefixCompatible k σ τ := by
  have he (j : Fin n) (hj : j.val < k) : flipSpin i σ j=σ j :=
    flipSpin_away i j σ (by intro hh; subst j; omega)
  constructor <;> intro h j hj
  · simpa only [he j hj] using h j hj
  · rw [he j hj]; exact h j hj

theorem prefixMass_flip_before {n : ℕ} (p : StrictFiniteProbability (BinaryConfiguration n))
    (i : Fin n) {k : ℕ} (hk : k ≤ i.val) (σ : BinaryConfiguration n) :
    prefixMass p k (flipSpin i σ)=prefixMass p k σ := by
  unfold prefixMass
  simp only [prefixCompatible_flip_before i hk]

theorem prefixMass_succ_add_flip {n : ℕ} (p : StrictFiniteProbability (BinaryConfiguration n))
    (i : Fin n) (σ : BinaryConfiguration n) :
    prefixMass p (i.val+1) σ+prefixMass p (i.val+1) (flipSpin i σ)=prefixMass p i.val σ := by
  unfold prefixMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro τ _
  simp only [prefixCompatible_succ,prefixCompatible_flip_before i le_rfl,flipSpin_at]
  by_cases hp : prefixCompatible i.val σ τ
  · simp only [hp,true_and,ite_eq_left hp]
    cases ht : τ i <;> cases hs : σ i <;> simp [ht,hs]
  · simp [hp]

end FourPapersCommon
