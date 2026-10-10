module

public import GeneralDepthPaper.ResidualHeatMassJets

@[expose] public section


/-! Gaussian convolution commutes with every actual spatial residual derivative,
and every variance derivative is half of two more spatial derivatives. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open ColeHopfFoundation.ProbabilityTheory
open scoped ContDiff NNReal Topology
namespace GeneralDepthPaper

 theorem contDiff_residual_spatial (m:ℝ):ContDiff ℝ ∞ (largeVarianceResidual m):=by
   have hh:ContDiff ℝ ∞ (fun x=>largeVarianceResidualSpatialJet 0 m x):=
     (contDiff_residualSpatial_joint 0).comp (contDiff_const.prodMk contDiff_id)
   have he:(fun x=>largeVarianceResidualSpatialJet 0 m x)=largeVarianceResidual m:=by
     funext x
     simpa using (iteratedDeriv_largeVarianceResidual_spatial 0 m x).symm
   rwa [he] at hh

 theorem hasExpGrowth_residual_spatialJet (i:ℕ) {m:ℝ} (hm:m∈Ioo (0:ℝ) 2):
     HasExpGrowth (iteratedDeriv i (largeVarianceResidual m)):=by
   let ε:ℝ:=min m (2-m)/4
   have hmin:0<min m (2-m):=lt_min hm.1 (sub_pos.mpr hm.2)
   have hε:0<ε:=div_pos hmin (by norm_num)
   have hmε:m∈Icc ε (2-ε):=by
     have ha:=min_le_left m (2-m)
     have hb:=min_le_right m (2-m)
     dsimp only [ε]
     constructor <;> linarith
   obtain ⟨K,hK,hbound⟩:=residualSpatial_mass_open_decay i 0 hε
   refine ⟨K,0,le_rfl,?_⟩
   intro x
   rw [zero_mul,Real.exp_zero,mul_one,iteratedDeriv_largeVarianceResidual_spatial]
   have hh:=hbound m hmε x
   simp only [iteratedDeriv_zero,Real.norm_eq_abs] at hh
   exact hh.trans (mul_le_mul_of_nonneg_left
     (Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg x])) hK.le |>.trans_eq (mul_one _))

 theorem iteratedDeriv_residualHeat_spatial (i:ℕ) {m:ℝ} (hm:m∈Ioo (0:ℝ) 2)
     (V:ℝ≥0) (x:ℝ):
     iteratedDeriv i (fun y=>residualHeatMassJet 0 0 m V y) x=residualHeatMassJet i 0 m V x:=by
   have he:(fun y=>residualHeatMassJet 0 0 m V y)=
       fun y=>∫z,largeVarianceResidual m (y+z) ∂gaussianReal 0 V:=by
     funext y
     simp only [residualHeatMassJet,iteratedDeriv_zero]
     apply integral_congr_ae
     exact ae_of_all _ fun z=>(iteratedDeriv_largeVarianceResidual_spatial 0 m (y+z)).symm
   rw [he,iteratedDeriv_integral_comp_add_gaussianReal
     ((contDiff_residual_spatial m).of_le (by simp))
       (fun a _=>hasExpGrowth_residual_spatialJet a hm) V (i:=i) le_rfl]
   simp only [residualHeatMassJet,iteratedDeriv_zero,iteratedDeriv_largeVarianceResidual_spatial]

 theorem hasDerivAt_residualHeatMassJet_variance (i:ℕ) {m V:ℝ} (hm:m∈Ioo (0:ℝ) 2)
     (hV:0<V) (x:ℝ):
     HasDerivAt (fun v=>residualHeatMassJet i 0 m v.toNNReal x)
       ((1/2:ℝ)*residualHeatMassJet (i+2) 0 m V.toNNReal x) V:=by
   have hh:=hasDerivAt_iteratedDeriv_integral_comp_add_gaussianReal_var
     (n:=i+2) ((contDiff_residual_spatial m).of_le (by simp))
     (fun a _=>hasExpGrowth_residual_spatialJet a hm) (i:=i) le_rfl hV x
   have he:∀v:ℝ,iteratedDeriv i
       (fun y=>∫z,largeVarianceResidual m (y+z) ∂gaussianReal 0 v.toNNReal) x=
         residualHeatMassJet i 0 m v.toNNReal x:=by
     intro v
     rw [iteratedDeriv_integral_comp_add_gaussianReal
       ((contDiff_residual_spatial m).of_le (by simp))
         (fun a _=>hasExpGrowth_residual_spatialJet a hm) v.toNNReal (i:=i) le_rfl]
     simp only [residualHeatMassJet,iteratedDeriv_zero,iteratedDeriv_largeVarianceResidual_spatial]
   have he':iteratedDeriv (i+2)
       (fun y=>∫z,largeVarianceResidual m (y+z) ∂gaussianReal 0 V.toNNReal) x=
         residualHeatMassJet (i+2) 0 m V.toNNReal x:=by
     rw [iteratedDeriv_integral_comp_add_gaussianReal
       ((contDiff_residual_spatial m).of_le (by simp))
         (fun a _=>hasExpGrowth_residual_spatialJet a hm) V.toNNReal (i:=i+2) le_rfl]
     simp only [residualHeatMassJet,iteratedDeriv_zero,iteratedDeriv_largeVarianceResidual_spatial]
   simpa only [he,he'] using hh

 theorem iteratedDeriv_residualHeat_variance (i k:ℕ) {m V:ℝ} (hm:m∈Ioo (0:ℝ) 2)
     (hV:0<V) (x:ℝ):
     iteratedDeriv k (fun v=>residualHeatMassJet i 0 m v.toNNReal x) V=
       (1/2:ℝ)^k*residualHeatMassJet (i+2*k) 0 m V.toNNReal x:=by
   induction k generalizing V with
   | zero=>simp
   | succ k ih=>
     rw [iteratedDeriv_succ]
     have he:iteratedDeriv k (fun v=>residualHeatMassJet i 0 m v.toNNReal x)=ᶠ[𝓝 V]
         (fun v=>(1/2:ℝ)^k*residualHeatMassJet (i+2*k) 0 m v.toNNReal x):=
       Filter.Eventually.mono (isOpen_Ioi.mem_nhds hV) (fun v hv=>ih hv)
     rw [he.deriv_eq]
     have hh:=(hasDerivAt_residualHeatMassJet_variance (i+2*k) hm hV x).const_mul ((1/2:ℝ)^k)
     rw [hh.deriv,pow_succ]
     have hindex:i+2*k+2=i+2*(k+1):=by omega
     rw [hindex]
     ring

 theorem iteratedDeriv_residualHeat_spatial_variance_mass (i j k:ℕ) {m V:ℝ}
     (hm:m∈Ioo (0:ℝ) 2) (hV:0<V) (x:ℝ):
     iteratedDeriv j (fun r=>iteratedDeriv k
       (fun v=>iteratedDeriv i (fun y=>residualHeatMassJet 0 0 r v.toNNReal y) x) V) m=
         (1/2:ℝ)^k*residualHeatMassJet (i+2*k) j m V.toNNReal x:=by
   have he:(fun r=>iteratedDeriv k
       (fun v=>iteratedDeriv i (fun y=>residualHeatMassJet 0 0 r v.toNNReal y) x) V)=ᶠ[𝓝 m]
         (fun r=>(1/2:ℝ)^k*residualHeatMassJet (i+2*k) 0 r V.toNNReal x):=by
     refine Filter.Eventually.mono (isOpen_Ioo.mem_nhds hm) ?_
     intro r hr
     simp only [iteratedDeriv_residualHeat_spatial i hr]
     exact iteratedDeriv_residualHeat_variance i k hr hV x
   rw [he.iteratedDeriv_eq j,iteratedDeriv_const_mul_field,iteratedDeriv_residualHeatMassJet_mass _ _ hm]

end GeneralDepthPaper
