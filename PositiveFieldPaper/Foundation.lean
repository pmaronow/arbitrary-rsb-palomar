module

public import FRSB.BackwardsJets
public import FRSB.UniformSpatialRegularity
public import FRSB.ConstantMassGrowthRefined
public import FRSB.ConstantMassParity
public import FRSB.ParisiMinimizerGeometry
public import FRSB.ForwardLeftAtoms
public import Paper.ParisiSelectedState

@[expose] public section


/-! Literal positive-field model data. The PDE is the already constructed
arbitrary-measure solution; the state starts at the actual external field.
The paper clock is rescaled from overlap time by `L = beta²`. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper
open scoped NNReal Topology ContDiff
namespace PositiveFieldPaper

abbrev ParisiMeasure := Paper.ParisiMeasure
abbrev BrownianSample := Paper.BrownianSample
abbrev brownianMeasure := Paper.canonicalBrownianMeasure

def L (β : ℝ) : ℝ := β^2

def U (β : ℝ) (ν : ParisiMeasure) (t x : ℝ) : ℝ :=
  Paper.parisiPotential β ν (t/β^2,x)

def D (β : ℝ) (ν : ParisiMeasure) (j : ℕ) (t x : ℝ) : ℝ :=
  Paper.parisiSpatialField β ν j (t/β^2,x)

def B (β : ℝ) (ν : ParisiMeasure) (t x : ℝ) : ℝ := D β ν 1 t x
def C (β : ℝ) (ν : ParisiMeasure) (t x : ℝ) : ℝ := D β ν 2 t x

def mass (β : ℝ) (ν : ParisiMeasure) (t : ℝ) : ℝ :=
  Paper.parisiCDF ν (t/β^2)

def leftMass (β : ℝ) (ν : ParisiMeasure) (t : ℝ) : ℝ :=
  FRSB.parisiLeftMass ν (t/β^2)

def Y (β h : ℝ) (hβ : β ≠ 0) (ν : ParisiMeasure)
    (t : ℝ) (sample : BrownianSample) : ℝ :=
  Paper.selectedParisiItoState β h hβ ν (t/β^2).toNNReal sample

def Q (β h : ℝ) (hβ : β ≠ 0) (ν : ParisiMeasure) (t : ℝ) : ℝ :=
  ∫ sample,B β ν t (Y β h hβ ν t sample)^2 ∂brownianMeasure

def S (β h : ℝ) (hβ : β ≠ 0) (ν : ParisiMeasure) (t : ℝ) : ℝ :=
  ∫ sample,C β ν t (Y β h hβ ν t sample)^2 ∂brownianMeasure

def F (β h : ℝ) (hβ : β ≠ 0) (ν : ParisiMeasure) (t : ℝ) : ℝ :=
  ∫ sample,D β ν 3 t (Y β h hβ ν t sample)^2 ∂brownianMeasure

def G (β h : ℝ) (hβ : β ≠ 0) (ν : ParisiMeasure) (t : ℝ) : ℝ :=
  ∫ sample,C β ν t (Y β h hβ ν t sample)^3 ∂brownianMeasure

def N (β h : ℝ) (hβ : β ≠ 0) (ν : ParisiMeasure) (t : ℝ) : ℝ :=
  Q β h hβ ν t-t*S β h hβ ν t

def J (β h : ℝ) (hβ : β ≠ 0) (ν : ParisiMeasure) (t m₀ : ℝ) : ℝ :=
  ∫ sample,D β ν 4 t (Y β h hβ ν t sample)^2-
    12*m₀*C β ν t (Y β h hβ ν t sample)*D β ν 3 t (Y β h hβ ν t sample)^2+
      6*m₀^2*C β ν t (Y β h hβ ν t sample)^4 ∂brownianMeasure

/-- The actual limiting Parisi functional, with the actual PDE evaluated at h. -/
def parisiFunctional (β h : ℝ) (ν : ParisiMeasure) : ℝ :=
  Paper.parisiPDEFunctional β h ν

/-- An actual minimizing probability measure, whose existence is already proved. -/
def parisiMinimizer (β h : ℝ) : ParisiMeasure := FRSB.parisiMinimizer β h

lemma overlapTime_mem {β t : ℝ} (hβ : β ≠ 0) (ht : t ∈ Icc (0 : ℝ) (L β)) :
    t/β^2 ∈ Icc (0 : ℝ) 1 :=
  ⟨div_nonneg ht.1 (sq_nonneg β),(div_le_one (sq_pos_of_ne_zero hβ)).mpr ht.2⟩

lemma overlapTime_mem_pos {β t : ℝ} (hβ : β ≠ 0) (ht : t ∈ Ioc (0 : ℝ) (L β)) :
    t/β^2 ∈ Ioc (0 : ℝ) 1 :=
  ⟨div_pos ht.1 (sq_pos_of_ne_zero hβ),(div_le_one (sq_pos_of_ne_zero hβ)).mpr ht.2⟩

lemma U_even (β : ℝ) (hβ : β ≠ 0) (ν : ParisiMeasure) (t x : ℝ)
    (ht : t ∈ Icc (0 : ℝ) (L β)) : U β ν t (-x) = U β ν t x :=
  FRSB.parisiPotential_even β ν _ x (overlapTime_mem hβ ht)

lemma U_nonneg (β : ℝ) (hβ : β ≠ 0) (ν : ParisiMeasure) (t x : ℝ)
    (ht : t ∈ Icc (0 : ℝ) (L β)) : 0 ≤ U β ν t x :=
  FRSB.parisiPotential_nonneg β ν _ x (overlapTime_mem hβ ht).2

lemma U_origin_growth (β : ℝ) (hβ : β ≠ 0) (ν : ParisiMeasure) (t x : ℝ)
    (ht : t ∈ Icc (0 : ℝ) (L β)) :
    0 ≤ U β ν t x-U β ν t 0 ∧ U β ν t x-U β ν t 0 ≤ |x| :=
  FRSB.parisiPotential_origin_growth β ν _ x (overlapTime_mem hβ ht)

lemma D_eq_iteratedDeriv (β : ℝ) (hβ : β ≠ 0) (ν : ParisiMeasure)
    (j : ℕ) (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) (L β)) :
    D β ν j t x=iteratedDeriv j (U β ν t) x :=
  Paper.parisiSpatialField_eq_iteratedDeriv β ν j _ x (overlapTime_mem hβ ht)

lemma B_eq_gradient (β : ℝ) (hβ : β ≠ 0) (ν : ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) (L β)) :
    B β ν t x=Paper.parisiGradient β ν (t/β^2,x) :=
  FRSB.backwardB_eq_gradient β ν _ x (overlapTime_mem hβ ht)

lemma C_eq_hessian (β : ℝ) (hβ : β ≠ 0) (ν : ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) (L β)) :
    C β ν t x=Paper.parisiHessian β ν (t/β^2,x) :=
  FRSB.backwardC_eq_hessian β ν _ x (overlapTime_mem hβ ht)

lemma C_pos (β : ℝ) (hβ : β ≠ 0) (ν : ParisiMeasure) (t x : ℝ)
    (ht : t ∈ Icc (0 : ℝ) (L β)) : 0<C β ν t x := by
  rw [C_eq_hessian β hβ ν t x ht]
  exact Paper.parisiHessian_pos β hβ ν _ x (overlapTime_mem hβ ht)

lemma C_le_one (β : ℝ) (hβ : β ≠ 0) (ν : ParisiMeasure) (t x : ℝ)
    (ht : t ∈ Icc (0 : ℝ) (L β)) : C β ν t x≤1 := by
  rw [C_eq_hessian β hβ ν t x ht]
  exact Paper.parisiHessian_le_one β hβ ν _

lemma norm_B_le_one (β : ℝ) (hβ : β ≠ 0) (ν : ParisiMeasure) (t x : ℝ)
    (ht : t ∈ Icc (0 : ℝ) (L β)) : ‖B β ν t x‖≤1 := by
  rw [B_eq_gradient β hβ ν t x ht]
  exact Paper.norm_parisiGradient_le_one β ν _

end PositiveFieldPaper
