module

public import GeneralDepthPaper.ResidualMassSpatialCommutation

@[expose] public section


/-! Every mass-jet Gaussian convolution has the actual spatial and heat
variance derivatives, so mixed derivatives may be taken in the source order. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open ColeHopfFoundation.ProbabilityTheory
open scoped ContDiff NNReal Topology
namespace GeneralDepthPaper

 theorem contDiff_residualSpatialMass_space (i j:ℕ) (m:ℝ):
     ContDiff ℝ ∞ (fun x=>iteratedDeriv j (fun r=>largeVarianceResidualSpatialJet i r x) m):=by
   have hc:=contDiff_residualSpatialMass_joint i j
   have hp:ContDiff ℝ ∞ (fun x:ℝ=>(m,x)):=contDiff_const.prodMk contDiff_id
   exact hc.comp hp

 theorem hasExpGrowth_residualSpatialMass_spaceJet (i j k:ℕ) {m:ℝ} (hm:m∈Ioo (0:ℝ) 2):
     HasExpGrowth (iteratedDeriv k (fun x=>iteratedDeriv j
       (fun r=>largeVarianceResidualSpatialJet i r x) m)):=by
   let ε:ℝ:=min m (2-m)/4
   have hmin:0<min m (2-m):=lt_min hm.1 (sub_pos.mpr hm.2)
   have hε:0<ε:=div_pos hmin (by norm_num)
   have hmε:m∈Icc ε (2-ε):=by
     have ha:=min_le_left m (2-m)
     have hb:=min_le_right m (2-m)
     dsimp only [ε]
     constructor <;> linarith
   obtain ⟨K,hK,hbound⟩:=residualSpatial_mass_open_decay (i+k) j hε
   refine ⟨K,0,le_rfl,?_⟩
   intro x
   rw [zero_mul,Real.exp_zero,mul_one,iteratedDeriv_residualSpatialMass_space]
   exact (hbound m hmε x).trans
     (mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg x])) hK.le |>.trans_eq (mul_one _))

 theorem iteratedDeriv_residualHeatMassJet_space (i j k:ℕ) {m:ℝ} (hm:m∈Ioo (0:ℝ) 2)
     (V:ℝ≥0) (x:ℝ):
     iteratedDeriv k (fun y=>residualHeatMassJet i j m V y) x=residualHeatMassJet (i+k) j m V x:=by
   unfold residualHeatMassJet
   rw [iteratedDeriv_integral_comp_add_gaussianReal
     ((contDiff_residualSpatialMass_space i j m).of_le (by simp))
       (fun a _=>hasExpGrowth_residualSpatialMass_spaceJet i j a hm) V (i:=k) le_rfl]
   simp only [iteratedDeriv_residualSpatialMass_space]

 theorem hasDerivAt_residualHeatMassJet_space (i j:ℕ) {m:ℝ} (hm:m∈Ioo (0:ℝ) 2)
     (V:ℝ≥0) (x:ℝ):
     HasDerivAt (fun y=>residualHeatMassJet i j m V y) (residualHeatMassJet (i+1) j m V x) x:=by
   have hf:ContDiff ℝ 1 (fun y=>residualHeatMassJet i j m V y):=
     contDiff_integral_comp_add_gaussianReal
       ((contDiff_residualSpatialMass_space i j m).of_le (by simp))
         (fun a _=>hasExpGrowth_residualSpatialMass_spaceJet i j a hm) V
   have hd:=((hf.differentiable (by norm_num)) x).hasDerivAt
   have he:deriv (fun y=>residualHeatMassJet i j m V y) x=residualHeatMassJet (i+1) j m V x:=by
     simpa only [iteratedDeriv_one] using iteratedDeriv_residualHeatMassJet_space i j 1 hm V x
   rwa [he] at hd

 theorem hasDerivAt_residualHeatMassJet_variance_all (i j:ℕ) {m V:ℝ}
     (hm:m∈Ioo (0:ℝ) 2) (hV:0<V) (x:ℝ):
     HasDerivAt (fun v=>residualHeatMassJet i j m v.toNNReal x)
       ((1/2:ℝ)*residualHeatMassJet (i+2) j m V.toNNReal x) V:=by
   have hh:=hasDerivAt_iteratedDeriv_integral_comp_add_gaussianReal_var
     (H:=fun y=>iteratedDeriv j (fun r=>largeVarianceResidualSpatialJet i r y) m)
     (n:=2) ((contDiff_residualSpatialMass_space i j m).of_le (by simp))
     (fun a _=>hasExpGrowth_residualSpatialMass_spaceJet i j a hm) (i:=0) (by norm_num) hV x
   change HasDerivAt (fun v=>residualHeatMassJet i j m v.toNNReal x)
     ((1/2:ℝ)*iteratedDeriv 2 (fun y=>residualHeatMassJet i j m V.toNNReal y) x) V at hh
   rw [iteratedDeriv_residualHeatMassJet_space i j 2 hm] at hh
   exact hh

end GeneralDepthPaper
