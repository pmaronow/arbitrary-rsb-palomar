module

public import DepthPaper.LargeVarianceLemma

@[expose] public section


/-! Literal Appendix B proof displays, with the manuscript's signed residual
(cosh^m minus its leading exponential term). -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology
namespace DepthPaper

 def sourceRho (m x:ℝ):ℝ:=coshPower m x-2*Real.exp (-m*Real.log 2)*Real.cosh (m*x)
 def sourceHeatRho (m:ℝ) (V:ℝ≥0) (x:ℝ):ℝ:=∫z,sourceRho m (x+z) ∂gaussianReal 0 V
 def sourceZeta (m:ℝ) (V:ℝ≥0) (x:ℝ):ℝ:=sourceHeatRho m V x/largeVarianceMain m V x

 theorem sourceRho_eq_neg (m x:ℝ):sourceRho m x=-largeVarianceResidual m x:=by
   unfold sourceRho largeVarianceResidual
   ring

 theorem sourceHeatRho_eq_neg (m:ℝ) (V:ℝ≥0) (x:ℝ):
     sourceHeatRho m V x=-residualHeatMassJet 0 0 m V x:=by
   unfold sourceHeatRho residualHeatMassJet
   simp only [iteratedDeriv_zero,sourceRho_eq_neg]
   have he:(fun z=>largeVarianceResidualSpatialJet 0 m (x+z))=
       fun z=>largeVarianceResidual m (x+z):=by
     funext z
     simpa using (iteratedDeriv_largeVarianceResidual_spatial 0 m (x+z)).symm
   rw [he,integral_neg]

 theorem gaussian_coshPower_signed_normalization {m:ℝ} (hm:m∈Ioo (0:ℝ) 2)
     (V:ℝ≥0) (x:ℝ):
     largeVarianceMoment m V x=largeVarianceMain m V x*(1+sourceZeta m V x):=by
   rw [sourceZeta,sourceHeatRho_eq_neg,residualHeat_base_eq_deficit hm]
   field_simp [(largeVarianceMain_pos m V x).ne'] <;> ring

 theorem residualHeat_source_order (i j k:ℕ) {m V:ℝ} (hm:m∈Ioo (0:ℝ) 2)
     (hV:0<V) (x:ℝ):
     iteratedDeriv i (fun y=>iteratedDeriv j (fun r=>iteratedDeriv k
       (fun v=>residualHeatMassJet 0 0 r v.toNNReal y) V) m) x=
       (1/2:ℝ)^k*residualHeatMassJet (i+2*k) j m V.toNNReal x:=by
   have he:(fun y=>iteratedDeriv j (fun r=>iteratedDeriv k
       (fun v=>residualHeatMassJet 0 0 r v.toNNReal y) V) m)=
         fun y=>(1/2:ℝ)^k*residualHeatMassJet (2*k) j m V.toNNReal y:=by
     funext y
     have hmEq:(fun r=>iteratedDeriv k
         (fun v=>residualHeatMassJet 0 0 r v.toNNReal y) V)=ᶠ[𝓝 m]
           (fun r=>(1/2:ℝ)^k*residualHeatMassJet (2*k) 0 r V.toNNReal y):=by
       refine Filter.Eventually.mono (isOpen_Ioo.mem_nhds hm) ?_
       intro r hr
       change iteratedDeriv k (fun v=>residualHeatMassJet 0 0 r v.toNNReal y) V=_
       simpa only [zero_add] using iteratedDeriv_residualHeat_variance 0 k hr hV y
     rw [hmEq.iteratedDeriv_eq j,iteratedDeriv_const_mul_field,iteratedDeriv_residualHeatMassJet_mass _ _ hm]
   rw [he,iteratedDeriv_const_mul_field,iteratedDeriv_residualHeatMassJet_space _ _ _ hm]
   congr 2
   omega

 theorem source_gaussian_mixed_derivatives (i j k:ℕ) {m V:ℝ} (hm:m∈Ioo (0:ℝ) 2)
     (hV:0<V) (x:ℝ):
     iteratedDeriv i (fun y=>iteratedDeriv j (fun r=>iteratedDeriv k
       (fun v=>sourceHeatRho r v.toNNReal y) V) m) x=
       (1/2:ℝ)^k*∫z,iteratedDeriv (i+2*k) (fun y=>iteratedDeriv j
         (fun r=>sourceRho r y) m) (x+z) ∂gaussianReal 0 V.toNNReal:=by
   simp only [sourceHeatRho_eq_neg,iteratedDeriv_fun_neg]
   rw [residualHeat_source_order i j k hm hV]
   have he:(fun z=>iteratedDeriv (i+2*k) (fun y=>iteratedDeriv j
       (fun r=>sourceRho r y) m) (x+z))=
         fun z=>-(iteratedDeriv j (fun r=>largeVarianceResidualSpatialJet (i+2*k) r (x+z)) m):=by
     funext z
     simp only [sourceRho_eq_neg,iteratedDeriv_fun_neg]
     have hbase:(fun y=>largeVarianceResidual m y)=
         fun y=>largeVarianceResidualSpatialJet 0 m y:=by
       funext y
       simpa using iteratedDeriv_largeVarianceResidual_spatial 0 m y
     have hmass:(fun y=>iteratedDeriv j (fun r=>largeVarianceResidual r y) m)=
         fun y=>iteratedDeriv j (fun r=>largeVarianceResidualSpatialJet 0 r y) m:=by
       funext y
       congr 1
       funext r
       simpa using iteratedDeriv_largeVarianceResidual_spatial 0 r y
     rw [hmass,iteratedDeriv_residualSpatialMass_space]
     simp only [zero_add]
   rw [he,integral_neg]
   unfold residualHeatMassJet
   ring

end DepthPaper
