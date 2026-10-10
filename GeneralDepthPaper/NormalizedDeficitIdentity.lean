module

public import GeneralDepthPaper.NormalizedDeficitBounds
public import GeneralDepthPaper.LargeVarianceZeroth

@[expose] public section


/-! The analytic deficit is the actual normalized difference of Gaussian
moments. Its logarithm has a uniformly positive denominator. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GeneralDepthPaper

 theorem residualHeat_base_eq_deficit {m:ℝ} (hm:m∈Ioo (0:ℝ) 2) (V:ℝ≥0) (x:ℝ):
     residualHeatMassJet 0 0 m V x=largeVarianceMain m V x-largeVarianceMoment m V x:=by
   have he:(fun z=>largeVarianceResidualSpatialJet 0 m (x+z))=
       fun z=>largeVarianceResidual m (x+z):=by
     funext z
     simpa using (iteratedDeriv_largeVarianceResidual_spatial 0 m (x+z)).symm
   have hres:Integrable (fun z=>largeVarianceResidual m (x+z)) (gaussianReal 0 V):=by
     have hi:=integrable_residualHeatMassJet 0 0 hm V x
     simpa only [iteratedDeriv_zero,he] using hi
   have hsum:Integrable (fun z=>2*Real.exp (-m*Real.log 2)*Real.cosh (m*(x+z))) (gaussianReal 0 V):=by
     convert hres.add (integrable_coshPower m V x) using 1
     funext z
     dsimp only [Pi.add_apply]
     unfold largeVarianceResidual
     ring
   unfold residualHeatMassJet
   simp only [iteratedDeriv_zero,he]
   unfold largeVarianceResidual largeVarianceMoment
   rw [integral_sub hsum (integrable_coshPower m V x),integral_largeVarianceMain]

 theorem normalizedDeficit_eq_ratio {m:ℝ} (hm:m∈Ioo (0:ℝ) 2) (V x:ℝ) (hV:0≤V):
     normalizedDeficit m V x=1-largeVarianceMoment m V.toNNReal x/largeVarianceMain m V.toNNReal x:=by
   have hn:normalizerInverse m V x=(largeVarianceMain m V.toNNReal x)⁻¹:=by
     calc
       _=normalizerInverse m (V.toNNReal:ℝ) x:=by rw [Real.coe_toNNReal V hV]
       _=_:=normalizerInverse_eq_inv_main m V.toNNReal x
   rw [normalizedDeficit,residualHeat_base_eq_deficit hm,hn]
   field_simp [(largeVarianceMain_pos m V.toNNReal x).ne'] <;> ring

 theorem one_sub_normalizedDeficit_pos {m:ℝ} (hm:m∈Ioo (0:ℝ) 2) (V x:ℝ) (hV:0≤V):
     0<1-normalizedDeficit m V x:=by
   rw [normalizedDeficit_eq_ratio hm V x hV]
   have hp:=div_pos (largeVarianceMoment_pos m V.toNNReal x) (largeVarianceMain_pos m V.toNNReal x)
   linarith

 theorem normalizedDeficit_bounds {m:ℝ} (hm:0<m) (hm1:m≤1) (V x:ℝ) (hV:0≤V):
     0≤normalizedDeficit m V x ∧ normalizedDeficit m V x≤1/2:=by
   have hm':m∈Ioo (0:ℝ) 2:=⟨hm,hm1.trans_lt (by norm_num)⟩
   rw [normalizedDeficit_eq_ratio hm' V x hV]
   have hM:=largeVarianceMain_pos m V.toNNReal x
   have hh:=largeVarianceMoment_main_bounds hm.le hm1 V.toNNReal x
   constructor
   · have hle:largeVarianceMoment m V.toNNReal x/largeVarianceMain m V.toNNReal x≤1:=
       (div_le_one hM).mpr hh.2
     linarith
   · have hle:(1/2:ℝ)≤largeVarianceMoment m V.toNNReal x/largeVarianceMain m V.toNNReal x:=
       (le_div_iff₀ hM).mpr (by linarith [hh.1])
     linarith

 theorem norm_log_one_sub_normalizedDeficit {m:ℝ} (hm:0<m) (hm1:m≤1) (V x:ℝ) (hV:0≤V):
     ‖Real.log (1-normalizedDeficit m V x)‖≤2*‖normalizedDeficit m V x‖:=by
   have hb:=normalizedDeficit_bounds hm hm1 V x hV
   have hp:0<1-normalizedDeficit m V x:=by linarith [hb.2]
   have hlog:Real.log (1-normalizedDeficit m V x)≤0:=Real.log_nonpos (by linarith) (by linarith [hb.1])
   have hh:=Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
   rw [Real.log_inv] at hh
   have hb':-(Real.log (1-normalizedDeficit m V x))*(1-normalizedDeficit m V x)≤normalizedDeficit m V x:=by
     have hh':-(Real.log (1-normalizedDeficit m V x))≤
         normalizedDeficit m V x/(1-normalizedDeficit m V x):=by
       convert hh using 1 <;> field_simp <;> ring
     exact (le_div_iff₀ hp).mp hh'
   rw [Real.norm_of_nonpos hlog,Real.norm_of_nonneg hb.1]
   nlinarith [hb.2,mul_nonneg (neg_nonneg.mpr hlog) hb.1]

 theorem largeVarianceError_eq_log_deficit {m:ℝ} (hm:m∈Ioo (0:ℝ) 2) (V:ℝ≥0) (x:ℝ):
     largeVarianceError m V x=(1/m)*Real.log (1-normalizedDeficit m V x):=by
   rw [largeVarianceError_eq_log_ratio hm.1.ne',normalizedDeficit_eq_ratio hm V x V.coe_nonneg]
   simp only [Real.toNNReal_coe]
   congr 2
   ring

end GeneralDepthPaper
