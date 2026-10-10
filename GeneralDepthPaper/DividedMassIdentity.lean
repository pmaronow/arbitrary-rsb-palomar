module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section


/-! A removable mass-one quotient is genuinely an integral of the mixed
derivative. The boundary value follows from the ordinary derivative and
continuity, without assuming a derivative of the observable. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace GeneralDepthPaper
set_option maxHeartbeats 800000

theorem divided_mass_integral_identity {a c : ℝ} (ha : a<1) (hc : c≠0)
    (f df A : ℝ→ℝ) (hd : ∀m∈Icc a 1,HasDerivAt f (df m) m)
    (hdf : ContinuousOn df (Icc a 1)) (hzero : f 1=0)
    (hA : ContinuousWithinAt A (Icc a 1) 1)
    (hid : ∀m∈Ico a 1,f m=(1-m)/2*c*A m) :
    ∀m∈Icc a 1,A m= -2/c*(∫τ in (0:ℝ)..1,df (1-(1-m)*τ)) := by
  have hinterior : ∀m∈Ico a 1,A m= -2/c*(∫τ in (0:ℝ)..1,df (1-(1-m)*τ)) := by
    intro m hm
    have hmap : ∀τ∈Icc (0:ℝ) 1,1-(1-m)*τ∈Icc a 1 := by
      intro τ hτ
      constructor <;> nlinarith [hm.1,mul_nonneg (sub_pos.mpr hm.2).le hτ.1,
        mul_le_mul_of_nonneg_left hτ.2 (sub_pos.mpr hm.2).le]
    have hpath : Continuous (fun τ:ℝ=>1-(1-m)*τ) := by fun_prop
    have hcomp : ContinuousOn (fun τ=>df (1-(1-m)*τ)) (Icc (0:ℝ) 1) :=
      hdf.comp hpath.continuousOn hmap
    have hder : ∀τ∈uIcc (0:ℝ) 1,
        HasDerivAt (fun τ=>f (1-(1-m)*τ)) (-(1-m)*df (1-(1-m)*τ)) τ := by
      intro τ hτ
      rw [uIcc_of_le zero_le_one] at hτ
      have harg : HasDerivAt (fun τ:ℝ=>1-(1-m)*τ) (-(1-m)) τ := by
        simpa only [id_eq,mul_one] using ((hasDerivAt_id τ).const_mul (1-m)).const_sub 1
      simpa only [Function.comp_def,mul_comm] using (hd _ (hmap τ hτ)).comp τ harg
    have hi : IntervalIntegrable (fun τ=> -(1-m)*df (1-(1-m)*τ)) volume 0 1 :=
      (continuousOn_const.mul hcomp).intervalIntegrable_of_Icc zero_le_one
    have H := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hi
    rw [intervalIntegral.integral_const_mul] at H
    simp only [mul_one,sub_sub_cancel,mul_zero,sub_zero,hzero,sub_zero] at H
    rw [hid m hm] at H
    have hmne : 1-m≠0 := (sub_pos.mpr hm.2).ne'
    have H0 : (1-m)*(-(∫τ in (0:ℝ)..1,df (1-(1-m)*τ))-c*A m/2)=0 := by
      nlinarith [H]
    have H1 := (mul_eq_zero.mp H0).resolve_left hmne
    field_simp [hc]
    nlinarith [H1]
  have hbound : A 1= -2/c*df 1 := by
    have hclosure : (1:ℝ)∈closure (Ico a 1) := by
      rw [closure_Ico ha.ne]
      exact ⟨ha.le,le_rfl⟩
    haveI : NeBot (𝓝[Ico a 1] 1) := mem_closure_iff_nhdsWithin_neBot.mp hclosure
    have hsl := (hd 1 ⟨ha.le,le_rfl⟩).tendsto_slope.mono_left
      (nhdsWithin_mono 1 (show Ico a 1⊆{1}ᶜ by intro m hm;simpa only [mem_compl_iff,mem_singleton_iff] using hm.2.ne))
    have hright := hsl.const_mul (-2/c)
    have heq : (fun m=> -2/c*slope f 1 m)=ᶠ[𝓝[Ico a 1] 1] A := by
      filter_upwards [self_mem_nhdsWithin] with m hm
      rw [slope_def_field,hzero,sub_zero,hid m hm]
      have hmne : m-1≠0 := sub_ne_zero.mpr hm.2.ne
      field_simp
      ring
    have hleft := hA.tendsto.mono_left (nhdsWithin_mono 1 Ico_subset_Icc_self)
    exact tendsto_nhds_unique hleft (hright.congr' heq)
  intro m hm
  rcases eq_or_lt_of_le hm.2 with rfl|hm1
  · simp only [sub_self,zero_mul,sub_zero,intervalIntegral.integral_const,sub_zero,one_smul]
    exact hbound
  · exact hinterior m ⟨hm.1,hm1⟩

end GeneralDepthPaper
