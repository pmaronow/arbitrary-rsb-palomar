module

public import FourPapersCommon.ParisiSharpGradientCell
public import FourPapersCommon.ParisiCDFGridDistance
public import FourPapersCommon.ExponentialMeshComparison
public import Paper.ParisiGradientMesh
public import Paper.ParisiFiniteApproximation

@[expose] public section


/-! A common finite mesh gives the sharp gradient constant without a
cross-profile stochastic-state assumption. The mesh starts at any physical
time; zero-width initial cells contribute exactly zero. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace FourPapersCommon
open Paper

theorem parisiFiniteGradient_grid_sharp_bound (β : ℝ) (hβ : β ≠ 0)
    (μ ν : ParisiMeasure) (n : ℕ) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : ℝ) :
    |parisiFiniteGradient (parisiGridRSBScheme ν n) β (t,x) -
      parisiFiniteGradient (parisiGridRSBScheme μ n) β (t,x)| ≤
      Real.exp (β^2) * β^2 *
        parisiCDFDistance (parisiGridMeasure μ n) (parisiGridMeasure ν n) := by
  let T := parisiGradientMeshTime n t
  let E := fun r : ℝ => ‖parisiCDF (parisiGridMeasure μ n) r -
    parisiCDF (parisiGridMeasure ν n) r‖
  let G := fun i : ℕ => fun y : ℝ =>
    parisiFiniteGradient (parisiGridRSBScheme ν n) β (T i,y) -
      parisiFiniteGradient (parisiGridRSBScheme μ n) β (T i,y)
  have hT : ∀ i ≤ n+1, T i ∈ Icc (0:ℝ) 1 :=
    fun _ hi => parisiGradientMeshTime_mem n ht hi
  have hmono : ∀ i < n+1, T i ≤ T (i+1) :=
    fun i _ => parisiGradientMeshTime_mono n t (Nat.le_succ i)
  have htop : T (n+1) = 1 := parisiGradientMeshTime_terminal n ht.2
  have hterminal : ∀ y, G (n+1) y = 0 := by
    intro y
    simp only [G, htop, parisiFiniteGradient_terminal, sub_self]
  have hEint : IntervalIntegrable E volume 0 1 :=
    parisiCDF_difference_intervalIntegrable (parisiGridMeasure μ n) (parisiGridMeasure ν n) 0 1
  have hcell : ∀ i < n+1, ∀ D : ℝ, 0 ≤ D →
      (∀ y, |G (i+1) y| ≤ D) → ∀ y,
      |G i y| ≤ Real.exp (β^2*(T (i+1)-T i)) *
        (D+β^2*(∫ r in T i..T (i+1), E r)) := by
    intro i hi D hD hd y
    rcases parisiGradientMeshTime_step_cases n t i with he | hlt
    · have he' : T i = T (i+1) := he
      have hG : G i y = G (i+1) y := by
        dsimp only [G]
        rw [he']
      rw [hG, he']
      simpa only [sub_self, mul_zero, Real.exp_zero,
        intervalIntegral.integral_same, add_zero, one_mul] using hd y
    · have hb : T (i+1) = hjbGridTime n (i+1) :=
        parisiGradientMeshTime_step_lt_terminal n t i hlt
      have hsub := parisiGradientMeshTime_cell_subset n t i hlt
      have hleft := hsub ⟨le_rfl, hlt.le⟩
      have hright : hjbGridTime n (i+1) ∈
          Icc (hjbGridTime n i) (hjbGridTime n (i+1)) :=
        ⟨(hjbGridTime_step_lt n i).le, le_rfl⟩
      let sμ := parisiGridRSBScheme μ n
      let sν := parisiGridRSBScheme ν n
      have hmμ : sμ.m (i+1) ∈ Icc (0:ℝ) 1 :=
        ⟨sμ.m_nonneg (by omega), sμ.m_le_one (by omega)⟩
      have hmν : sν.m (i+1) ∈ Icc (0:ℝ) 1 :=
        ⟨sν.m_nonneg (by omega), sν.m_le_one (by omega)⟩
      have hterm : ∀ z,
          |parisiSlabGradient sν β (n+1-i) (sν.m (i+1))
              (hjbGridTime n (i+1)) (hjbGridTime n (i+1)) z -
            parisiSlabGradient sμ β (n+1-i) (sμ.m (i+1))
              (hjbGridTime n (i+1)) (hjbGridTime n (i+1)) z| ≤ D := by
        intro z
        dsimp only [sν,sμ]
        rw [← hjbGrid_cell_gradient ν n β i hi _ z hright,
          ← hjbGrid_cell_gradient μ n β i hi _ z hright]
        simpa only [G, hb] using hd z
      have hh := parisiSlabGradient_sharp_comparison sμ sν β hβ
        (n+1-i) (n+1-i) hmμ hmν (T i) (hjbGridTime n (i+1)) D
        hleft.2 hD hterm (T i) ⟨le_rfl,hleft.2⟩ y
      dsimp only [sν,sμ] at hh
      rw [← hjbGrid_cell_gradient ν n β i hi _ y hleft,
        ← hjbGrid_cell_gradient μ n β i hi _ y hleft] at hh
      have heint := parisiCDFDistance_grid_cell_integral μ ν n i hi
        (T i) (T (i+1)) hlt.le hleft.1 (by rw [hb])
      change (∫ r in T i..T (i+1), E r) = _ at heint
      change |G i y| ≤ _ at hh
      rw [← hb] at hh
      convert hh using 1
      rw [heint]
      ring
  have hh := exponentialMeshComparison_le_full (n+1) T hT hmono htop
    (β^2) (sq_nonneg β) E hEint (fun _ _ => norm_nonneg _) G hterminal hcell
    0 (by omega) x
  simpa only [G,T,parisiGradientMeshTime_zero n ht.1,E,parisiCDFDistance] using hh

end FourPapersCommon
