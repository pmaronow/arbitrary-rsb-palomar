module

public import GeneralDepthPaper.ProbabilityKernelAverage
public import GeneralDepthPaper.CompactTiltKernel
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section


/-! The literal integral over the auxiliary tilt interval is a norm-one
bounded-function linear operator. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BoundedContinuousFunction
namespace GeneralDepthPaper

def unitTiltMeasure : Measure ℝ := volume.restrict (Icc (0:ℝ) 1)
instance : IsProbabilityMeasure unitTiltMeasure where
  measure_univ := by simp [unitTiltMeasure,Real.volume_Icc]

def unitTiltExtensionCLM : (CompactTiltLocation →ᵇ ℝ)→L[ℝ]((ℝ×ℝ) →ᵇ ℝ) :=
  BoundedContinuousFunction.compContinuousCLM ℝ ℝ
    ⟨fun s:ℝ×ℝ=>(projIcc 0 1 zero_le_one s.1,s.2),by fun_prop⟩

def unitTiltAverageCLM : (CompactTiltLocation →ᵇ ℝ)→L[ℝ](ℝ →ᵇ ℝ) :=
  (probabilityKernelAverageCLM unitTiltMeasure).comp unitTiltExtensionCLM

theorem unitTiltAverageCLM_apply (F : CompactTiltLocation →ᵇ ℝ) (x : ℝ) :
    unitTiltAverageCLM F x=∫t in (0:ℝ)..1,F (projIcc 0 1 zero_le_one t,x) := by
  change (∫t,F (projIcc 0 1 zero_le_one t,x) ∂volume.restrict (Icc 0 1))=_
  rw [intervalIntegral.integral_of_le zero_le_one]
  exact setIntegral_congr_set Ioc_ae_eq_Icc.symm

end GeneralDepthPaper
