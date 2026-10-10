module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section


/-! Pointwise convergence of actual convex differentiable functions implies
derivative convergence at every differentiability point of their limit. -/
noncomputable section
open Set Filter
open scoped Topology
namespace FourPapersCommon

theorem tendsto_deriv_of_convex_pointwise {ι : Type*} {l : Filter ι}
    {F : ι → ℝ → ℝ} {f : ℝ → ℝ} {x d : ℝ}
    (hconv : ∀ i, ConvexOn ℝ univ (F i))
    (hdiff : ∀ i, DifferentiableAt ℝ (F i) x)
    (hlim : ∀ y, Tendsto (fun i=>F i y) l (𝓝 (f y)))
    (hd : HasDerivAt f d x) :
    Tendsto (fun i=>deriv (F i) x) l (𝓝 d) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hneg : ∀ᶠ t : ℝ in 𝓝[<] (0:ℝ),t<0 := self_mem_nhdsWithin
    obtain ⟨t,ht,hst⟩ := (hneg.and
      (hd.tendsto_slope_zero_left.eventually (eventually_gt_nhds ha))).exists
    have ht0 : t < 0 := ht
    have hs : Tendsto (fun i=>slope (F i) (x+t) x) l (𝓝 (slope f (x+t) x)) := by
      simpa only [slope_def_field] using ((hlim x).sub (hlim (x+t))).div_const (x-(x+t))
    have hslo : a < slope f (x+t) x := by
      rw [slope_comm,slope_def_field,add_sub_cancel_left]
      simpa only [smul_eq_mul,div_eq_mul_inv,mul_comm] using hst
    filter_upwards [hs.eventually (eventually_gt_nhds hslo)] with i hi
    exact hi.trans_le ((hconv i).slope_le_deriv (mem_univ _) (mem_univ _) (by linarith) (hdiff i))
  · intro b hb
    have hpos : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ),0<t := self_mem_nhdsWithin
    obtain ⟨t,ht,hst⟩ := (hpos.and
      (hd.tendsto_slope_zero_right.eventually (eventually_lt_nhds hb))).exists
    have ht0 : 0 < t := ht
    have hs : Tendsto (fun i=>slope (F i) x (x+t)) l (𝓝 (slope f x (x+t))) := by
      simpa only [slope_def_field] using ((hlim (x+t)).sub (hlim x)).div_const (x+t-x)
    have hshi : slope f x (x+t) < b := by
      rw [slope_def_field,add_sub_cancel_left]
      simpa only [smul_eq_mul,div_eq_mul_inv,mul_comm] using hst
    filter_upwards [hs.eventually (eventually_lt_nhds hshi)] with i hi
    exact ((hconv i).deriv_le_slope (mem_univ _) (mem_univ _) (by linarith) (hdiff i)).trans_lt hi

end FourPapersCommon
