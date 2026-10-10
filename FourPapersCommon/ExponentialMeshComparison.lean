module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic

set_option backward.privateInPublic true

@[expose] public section


/-! A local uniform slab estimate telescopes over a finite nondescending
mesh. The comparison is for functions of arbitrary states and needs no
supremum. Repeated nodes, a zero coefficient, and an empty mesh are retained. -/
noncomputable section
open Set MeasureTheory
namespace FourPapersCommon
set_option autoImplicit false
set_option maxHeartbeats 800000

variable {X : Type*}

private theorem intervalIntegrable_subinterval
    (E : ℝ → ℝ) (hE : IntervalIntegrable E volume 0 1)
    (a b : ℝ) (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1) (hab : a≤b) :
    IntervalIntegrable E volume a b := by
  apply hE.mono_set
  rw [uIcc_of_le hab,uIcc_of_le (by norm_num : (0:ℝ)≤1)]
  exact Icc_subset_Icc ha.1 hb.2

private theorem integral_nonneg_subinterval
    (E : ℝ → ℝ) (hE : ∀t∈Icc (0:ℝ) 1,0≤E t)
    (a b : ℝ) (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1) (hab : a≤b) :
    0≤∫t in a..b,E t :=
  intervalIntegral.integral_nonneg hab (fun t ht=>hE t ⟨ha.1.trans ht.1,ht.2.trans hb.2⟩)

theorem exponentialMeshComparison
    (N : ℕ) (T : ℕ → ℝ) (hT : ∀i,i≤N→T i∈Icc (0:ℝ) 1)
    (hmono : ∀i,i<N→T i≤T (i+1)) (htop : T N=1)
    (R : ℝ) (hR : 0≤R) (E : ℝ → ℝ)
    (hEint : IntervalIntegrable E volume 0 1) (hE : ∀t∈Icc (0:ℝ) 1,0≤E t)
    (G : ℕ → X → ℝ) (hterminal : ∀x,G N x=0)
    (hcell : ∀i,i<N→∀D : ℝ,0≤D→(∀x,|G (i+1) x|≤D)→∀x,
      |G i x|≤Real.exp (R*(T (i+1)-T i))*(D+R*∫t in T i..T (i+1),E t))
    (i : ℕ) (hi : i≤N) (x : X) :
    |G i x|≤Real.exp (R*(1-T i))*R*∫t in T i..1,E t := by
  have H : ∀k,∀i,i≤N→N-i=k→∀x : X,
      |G i x|≤Real.exp (R*(1-T i))*R*∫t in T i..1,E t := by
    intro k
    induction k with
    | zero =>
        intro i hi he x
        have hiN : i=N := by omega
        subst i
        simp only [hterminal,htop,abs_zero,intervalIntegral.integral_same,mul_zero,le_refl]
    | succ k ih =>
        intro i hi he x
        have hil : i<N := by omega
        have hin : i+1≤N := by omega
        have hdist : N-(i+1)=k := by omega
        have hnext := ih (i+1) hin hdist
        have hTi := hT i hi
        have hTn := hT (i+1) hin
        have hstep := hmono i hil
        let A := Real.exp (R*(1-T (i+1)))
        let B := R*∫t in T (i+1)..1,E t
        let C := R*∫t in T i..T (i+1),E t
        have hI : 0≤∫t in T (i+1)..1,E t :=
          integral_nonneg_subinterval E hE _ _ hTn (by norm_num) hTn.2
        have hcellI : 0≤∫t in T i..T (i+1),E t :=
          integral_nonneg_subinterval E hE _ _ hTi hTn hstep
        have hB : 0≤B := mul_nonneg hR hI
        have hC : 0≤C := mul_nonneg hR hcellI
        have hA : 1≤A := Real.one_le_exp_iff.mpr (mul_nonneg hR (sub_nonneg.mpr hTn.2))
        have hAn : 0≤A := le_trans zero_le_one hA
        have hnext' : ∀x,|G (i+1) x|≤A*B := by
          intro x
          simpa only [A,B,mul_assoc] using hnext x
        have hsmall : C≤A*C := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hA hC
        have hsum := intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_subinterval E hEint _ _ hTi hTn hstep)
          (intervalIntegrable_subinterval E hEint _ _ hTn (by norm_num) hTn.2)
        have hexp : Real.exp (R*(T (i+1)-T i))*A=Real.exp (R*(1-T i)) := by
          dsimp [A]
          rw [←Real.exp_add]
          congr 1
          ring
        calc
          |G i x|≤Real.exp (R*(T (i+1)-T i))*(A*B+C) :=
            hcell i hil (A*B) (mul_nonneg hAn hB) hnext' x
          _ ≤Real.exp (R*(T (i+1)-T i))*(A*B+A*C) :=
            mul_le_mul_of_nonneg_left (add_le_add_right hsmall _) (Real.exp_pos _).le
          _ =Real.exp (R*(T (i+1)-T i))*A*
              (R*((∫t in T i..T (i+1),E t)+(∫t in T (i+1)..1,E t))) := by
            dsimp [B,C]
            ring
          _ =Real.exp (R*(1-T i))*R*∫t in T i..1,E t := by
            rw [hexp,hsum]
            ring
  exact H (N-i) i hi rfl x

theorem exponentialMeshComparison_le_full
    (N : ℕ) (T : ℕ → ℝ) (hT : ∀i,i≤N→T i∈Icc (0:ℝ) 1)
    (hmono : ∀i,i<N→T i≤T (i+1)) (htop : T N=1)
    (R : ℝ) (hR : 0≤R) (E : ℝ → ℝ)
    (hEint : IntervalIntegrable E volume 0 1) (hE : ∀t∈Icc (0:ℝ) 1,0≤E t)
    (G : ℕ → X → ℝ) (hterminal : ∀x,G N x=0)
    (hcell : ∀i,i<N→∀D : ℝ,0≤D→(∀x,|G (i+1) x|≤D)→∀x,
      |G i x|≤Real.exp (R*(T (i+1)-T i))*(D+R*∫t in T i..T (i+1),E t))
    (i : ℕ) (hi : i≤N) (x : X) :
    |G i x|≤Real.exp R*R*∫t in (0:ℝ)..1,E t := by
  have hTi := hT i hi
  have hI : 0≤∫t in T i..1,E t :=
    integral_nonneg_subinterval E hE _ _ hTi (by norm_num) hTi.2
  have hprefix : 0≤∫t in (0:ℝ)..T i,E t :=
    integral_nonneg_subinterval E hE _ _ (by norm_num) hTi hTi.1
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_subinterval E hEint _ _ (by norm_num) hTi hTi.1)
    (intervalIntegrable_subinterval E hEint _ _ hTi (by norm_num) hTi.2)
  have htail : (∫t in T i..1,E t)≤∫t in (0:ℝ)..1,E t := by linarith
  have hexp : Real.exp (R*(1-T i))≤Real.exp R := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hR hTi.1]
  calc
    |G i x|≤Real.exp (R*(1-T i))*R*∫t in T i..1,E t :=
      exponentialMeshComparison N T hT hmono htop R hR E hEint hE G hterminal hcell i hi x
    _ ≤Real.exp R*R*∫t in T i..1,E t :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hexp hR) hI
    _ ≤Real.exp R*R*∫t in (0:ℝ)..1,E t :=
      mul_le_mul_of_nonneg_left htail (mul_nonneg (Real.exp_pos R).le hR)

end FourPapersCommon
