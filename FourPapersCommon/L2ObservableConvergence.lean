module

public import FourPapersCommon.L2ObservableBound
public import Mathlib.Topology.UniformSpace.UniformConvergence

@[expose] public section


/-! Uniform convergence of actual bounded squared observables under a genuine
L² coupling and uniform convergence of their fields. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace FourPapersCommon
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem tendstoUniformlyOn_integral_squared_observable {ι : Type*} {F : Filter ι}
    (S : Set ℝ) (X : ι → ℝ → Ω → ℝ) (Y : ℝ → Ω → ℝ)
    (hX : ∀ n t,MemLp (X n t) 2 P) (hY : ∀ t,MemLp (Y t) 2 P)
    (f : ι → ℝ → ℝ → ℝ) (g : ℝ → ℝ → ℝ)
    (hif : ∀ n t,Integrable (fun ω => (f n t (X n t ω))^2) P)
    (hig : ∀ t,Integrable (fun ω => (g t (Y t ω))^2) P)
    {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hf : ∀ n,∀ t ∈ S,∀ x,|f n t x| ≤ C) (hg : ∀ t ∈ S,∀ x,|g t x| ≤ C)
    (hLip : ∀ t ∈ S,∀ x y,|g t x-g t y| ≤ K*|x-y|)
    (ε : ι → ℝ) (hε : ∀ n,0 ≤ ε n) (htε : Tendsto ε F (𝓝 0))
    (hfield : ∀ n,∀ t ∈ S,∀ x,|f n t x-g t x| ≤ ε n)
    (hstate : TendstoUniformlyOn (fun n t => ∫ ω,(X n t ω-Y t ω)^2 ∂P)
      (fun _ => 0) F S) :
    TendstoUniformlyOn (fun n t => ∫ ω,(f n t (X n t ω))^2 ∂P)
      (fun t => ∫ ω,(g t (Y t ω))^2 ∂P) F S := by
  let E : ι → ℝ → ℝ := fun n t => ∫ ω,(X n t ω-Y t ω)^2 ∂P
  let B : ι → ℝ → ℝ := fun n t => 2*C*ε n+2*C*K*Real.sqrt (E n t)
  have hE : Tendsto (Function.uncurry E) (F ×ˢ 𝓟 S) (𝓝 0) := by
    exact tendsto_prod_filter_iff.mpr
      (tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mp hstate)
  have he : Tendsto (fun z : ι × ℝ => ε z.1) (F ×ˢ 𝓟 S) (𝓝 0) := htε.comp tendsto_fst
  have hφ : Continuous (fun z : ℝ × ℝ => 2*C*z.1+2*C*K*Real.sqrt z.2) := by fun_prop
  have hB : TendstoUniformlyOn B (fun _ => 0) F S := by
    apply tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mpr
    apply tendsto_prod_filter_iff.mp
    change Tendsto (fun z : ι × ℝ => B z.1 z.2) (F ×ˢ 𝓟 S) (𝓝 0)
    have hp : Tendsto (fun z : ι × ℝ => (ε z.1,E z.1 z.2)) (F ×ˢ 𝓟 S) (𝓝 (0,0)) := by
      simpa only [nhds_prod_eq,Function.uncurry] using he.prodMk hE
    have hh := (hφ.continuousAt (x := (0,0))).tendsto.comp hp
    simpa only [B,Function.uncurry,Function.comp_def,mul_zero,add_zero,Real.sqrt_zero] using hh
  have hp (n : ι) (t : ℝ) (ht : t ∈ S) :
      |(∫ ω,(f n t (X n t ω))^2 ∂P)-(∫ ω,(g t (Y t ω))^2 ∂P)| ≤ B n t := by
    exact integral_observable_difference_le (X n t) (Y t) (hX n t) (hY t)
      (fun x => (f n t x)^2) (fun x => (g t x)^2) (hif n t) (hig t)
      (mul_nonneg (mul_nonneg (by norm_num) hC) (hε n)) (by positivity)
      (fun x => (abs_square_sub_le_of_abs_le hC (hf n t ht x) (hg t ht x)).trans
        (mul_le_mul_of_nonneg_left (hfield n t ht x) (by positivity)))
      (fun x y => by
        calc
          _ ≤ 2*C*|g t x-g t y| := abs_square_sub_le_of_abs_le hC (hg t ht x) (hg t ht y)
          _ ≤ 2*C*(K*|x-y|) := mul_le_mul_of_nonneg_left (hLip t ht x y) (by positivity)
          _ = _ := by ring)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro η hη
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hB η hη] with n hn
  intro t ht
  have hh := (hp n t ht).trans (le_abs_self (B n t)) |>.trans_lt (by
    simpa only [Real.dist_eq,zero_sub,abs_neg] using hn t ht)
  simpa only [Real.dist_eq,abs_sub_comm] using hh

end FourPapersCommon
