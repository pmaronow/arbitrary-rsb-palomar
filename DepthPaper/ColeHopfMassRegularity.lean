module

public import Common.Mathlib.Probability.Distributions.Gaussian.ColeHopf
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.ContDiff.Basic

@[expose] public section


/-! Analyticity in the mass parameter, including zero. The zero-mass
branch is exactly the removable divided difference of the Gaussian cumulant
function, rather than a separately assumed smooth extension. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ContDiff NNReal
namespace DepthPaper
open ColeHopfFoundation.ProbabilityTheory

theorem gaussian_integrableExpSet_linearGrowth (g : ℝ→ℝ)
    (hg : HasLinearGrowth g) (hm : Measurable g) (v : ℝ≥0) (x : ℝ) :
    integrableExpSet (fun z=>g (x+z)) (gaussianReal 0 v)=univ := by
  ext a
  change Integrable (fun z=>Real.exp (a*g (x+z))) (gaussianReal 0 v) ↔ True
  exact iff_true_intro (integrable_exp_mul_comp_add hg hm a v x)

theorem coleHopf_eq_cgf_dslope (g : ℝ→ℝ) (hg : HasLinearGrowth g)
    (hm : Measurable g) (v : ℝ≥0) (x a : ℝ) :
    coleHopf a v g x=dslope (cgf (fun z=>g (x+z)) (gaussianReal 0 v)) 0 a := by
  have hset := gaussian_integrableExpSet_linearGrowth g hg hm v x
  have h0 : 0∈interior (integrableExpSet (fun z=>g (x+z)) (gaussianReal 0 v)) := by
    rw [hset,interior_univ]; exact mem_univ _
  by_cases ha : a=0
  · subst a
    rw [coleHopf_zero,dslope_same,deriv_cgf_zero h0]
    simp
  · rw [coleHopf_of_ne ha,dslope_of_ne _ ha]
    simp [slope,cgf,mgf,one_div]

theorem analyticAt_coleHopf_mass (g : ℝ→ℝ) (hg : HasLinearGrowth g)
    (hm : Measurable g) (v : ℝ≥0) (x a : ℝ) :
    AnalyticAt ℝ (fun m=>coleHopf m v g x) a := by
  have hset := gaussian_integrableExpSet_linearGrowth g hg hm v x
  have hc (b : ℝ) : AnalyticAt ℝ (cgf (fun z=>g (x+z)) (gaussianReal 0 v)) b := by
    apply analyticAt_cgf
    rw [hset,interior_univ]; exact mem_univ _
  simp_rw [coleHopf_eq_cgf_dslope g hg hm v x]
  by_cases ha : a=0
  · subst a
    obtain ⟨P,hP⟩ := hc 0
    exact ⟨P.fslope,hP.has_fpower_series_dslope_fslope⟩
  · have he : dslope (cgf (fun z=>g (x+z)) (gaussianReal 0 v)) 0 =ᶠ[𝓝 a]
        (fun m=>cgf (fun z=>g (x+z)) (gaussianReal 0 v) m/m) := by
      filter_upwards [isOpen_ne.mem_nhds ha] with m hm0
      rw [dslope_of_ne _ hm0]
      simp [slope,cgf_zero,div_eq_mul_inv,mul_comm]
    exact ((hc a).div analyticAt_id ha).congr he.symm

theorem contDiff_coleHopf_mass (g : ℝ→ℝ) (hg : HasLinearGrowth g)
    (hm : Measurable g) (v : ℝ≥0) (x : ℝ) :
    ContDiff ℝ ⊤ (fun m=>coleHopf m v g x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro a
  exact (analyticAt_coleHopf_mass g hg hm v x a).contDiffAt

/-- The derivative through the zero-mass boundary is half the genuine
Gaussian variance of the terminal datum. -/
theorem deriv_coleHopf_mass_zero (g : ℝ→ℝ) (hg : HasLinearGrowth g)
    (hm : Measurable g) (v : ℝ≥0) (x : ℝ) :
    deriv (fun m=>coleHopf m v g x) 0=
      ((∫z,g (x+z)^2 ∂gaussianReal 0 v)-(∫z,g (x+z) ∂gaussianReal 0 v)^2)/2 := by
  let X : ℝ→ℝ := fun z=>g (x+z)
  have hset := gaussian_integrableExpSet_linearGrowth g hg hm v x
  have h0 : 0∈interior (integrableExpSet X (gaussianReal 0 v)) := by
    change 0∈interior (integrableExpSet (fun z=>g (x+z)) (gaussianReal 0 v))
    rw [hset,interior_univ]; exact mem_univ _
  have hc : AnalyticAt ℝ (cgf X (gaussianReal 0 v)) 0 := analyticAt_cgf h0
  have hd := hc.hasFPowerSeriesAt.has_fpower_series_dslope_fslope.deriv
  have he : (fun m=>coleHopf m v g x)=dslope (cgf X (gaussianReal 0 v)) 0 := by
    funext m
    exact coleHopf_eq_cgf_dslope g hg hm v x m
  rw [he]
  rw [hd]
  change (FormalMultilinearSeries.ofScalars ℝ
    (fun n=>iteratedDeriv n (cgf X (gaussianReal 0 v)) 0/(n.factorial:ℝ))).fslope.coeff 1 = _
  rw [FormalMultilinearSeries.coeff_fslope,FormalMultilinearSeries.coeff_ofScalars]
  change iteratedDeriv 2 (cgf X (gaussianReal 0 v)) 0/2 = _
  rw [iteratedDeriv_two_cgf h0,deriv_cgf_zero h0]
  simp [X]

end DepthPaper
