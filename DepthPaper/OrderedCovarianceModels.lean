module

public import DepthPaper.EffectiveCovarianceCongruence
public import DepthPaper.HighDegreeModel

@[expose] public section


/-! Exact finite polynomial models with ordered exponents beginning at
four. Adding a larger even monomial preserves all original coefficients. -/
noncomputable section
open Set
open scoped BigOperators
namespace DepthPaper
set_option maxHeartbeats 1400000

structure OrderedCovarianceModel (k : ℕ) where
  covariance : AdmissibleCovariance
  exponent : Fin (k+1)→ℕ
  increasing : StrictMono exponent
  first_exponent : exponent 0=4
  degrees_eq : covariance.degrees=Finset.univ.image exponent

namespace OrderedCovarianceModel

def coefficients {k : ℕ} (D : OrderedCovarianceModel k) : Fin (k+1)→ℝ :=
  fun i=>D.covariance.coefficient (D.exponent i)

theorem coefficient_pos {k : ℕ} (D : OrderedCovarianceModel k) (i : Fin (k+1)) :
    0<D.coefficients i := D.covariance.coefficient_pos _
  (D.degrees_eq ▸ Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)

theorem exponent_ge_four {k : ℕ} (D : OrderedCovarianceModel k) (i : Fin (k+1)) :
    4≤D.exponent i := by
  rw [←D.first_exponent]
  exact D.increasing.monotone (Fin.zero_le i)

theorem exponent_even {k : ℕ} (D : OrderedCovarianceModel k) (i : Fin (k+1)) :
    Even (D.exponent i) := D.covariance.degree_even _
  (D.degrees_eq ▸ Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)

theorem value_eq {k : ℕ} (D : OrderedCovarianceModel k) (q : ℝ) :
    D.covariance.value q=∑i,D.coefficients i*q^(D.exponent i) := by
  rw [AdmissibleCovariance.value,D.degrees_eq,Finset.sum_image]
  · rfl
  · exact fun i _ j _ hij=>D.increasing.injective hij

theorem larger_degree_not_mem {k : ℕ} (D : OrderedCovarianceModel k) {p : ℕ}
    (hp : D.exponent (Fin.last k)<p) : p∉D.covariance.degrees := by
  rw [D.degrees_eq]
  intro hmem
  obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hmem
  have hh:=D.increasing.monotone (Fin.le_last i)
  rw [hi] at hh
  omega

def extend {k : ℕ} (D : OrderedCovarianceModel k) (p : ℕ)
    (hp : D.exponent (Fin.last k)<p) (he : Even p) (lam : ℝ) (hlam : 0<lam) :
    OrderedCovarianceModel (k+1) where
  covariance:=D.covariance.addHighDegree p
    ((D.exponent_ge_four (Fin.last k)).trans hp.le) he (D.larger_degree_not_mem hp) lam hlam
  exponent:=Fin.lastCases p D.exponent
  increasing:=by
    intro i
    refine Fin.lastCases ?_ (fun i=>?_) i
    · intro j hij
      exact False.elim ((not_lt_of_ge (Fin.le_last j)) hij)
    · intro j
      refine Fin.lastCases ?_ (fun j=>?_) j
      · intro hij
        simp only [Fin.lastCases_castSucc,Fin.lastCases_last]
        exact (D.increasing.monotone (Fin.le_last i)).trans_lt hp
      · intro hij
        simp only [Fin.lastCases_castSucc]
        exact D.increasing (Fin.castSucc_lt_castSucc_iff.mp hij)
  first_exponent:=by
    change Fin.lastCases p D.exponent (0:Fin (k+1)).castSucc=4
    rw [Fin.lastCases_castSucc]
    exact D.first_exponent
  degrees_eq:=by
    change insert p D.covariance.degrees=Finset.univ.image (Fin.lastCases p D.exponent)
    rw [D.degrees_eq]
    ext j
    simp only [Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro (rfl|⟨i,rfl⟩)
      · exact ⟨Fin.last (k+1),by simp⟩
      · exact ⟨i.castSucc,by simp⟩
    · rintro ⟨i,rfl⟩
      refine Fin.lastCases ?_ (fun i=>?_) i
      · exact Or.inl (by simp)
      · exact Or.inr ⟨i,by simp⟩

end OrderedCovarianceModel

def quarticOrderedModel : OrderedCovarianceModel 0 where
  covariance:=quarticSeed
  exponent:=fun _=>4
  increasing:=by
    letI : Subsingleton (Fin (0+1)):=inferInstanceAs (Subsingleton (Fin 1))
    intro i j hij
    have hh : i=j:=Subsingleton.elim _ _
    exact False.elim (hij.ne hh)
  first_exponent:=rfl
  degrees_eq:=by simp [quarticSeed]

end DepthPaper
