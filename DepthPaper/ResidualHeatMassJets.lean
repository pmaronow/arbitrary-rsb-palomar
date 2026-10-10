module

public import DepthPaper.OpenMassMixedDecay
public import DepthPaper.JointMassJets
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Common.Mathlib.Probability.Distributions.Gaussian.HeatSemigroup

@[expose] public section


/-! Gaussian convolution of genuine residual jets, including differentiation
in the mass parameter at m=1 with actual two-sided domination. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open ColeHopfFoundation.ProbabilityTheory
open scoped ContDiff NNReal Topology
namespace DepthPaper

 def residualHeatMassJet (i j:ℕ) (m:ℝ) (V:ℝ≥0) (x:ℝ):ℝ :=
   ∫z,iteratedDeriv j (fun r=>largeVarianceResidualSpatialJet i r (x+z)) m ∂gaussianReal 0 V

 theorem continuous_residualSpatialMass_section (i j:ℕ) (m x:ℝ):
     Continuous (fun z=>iteratedDeriv j (fun r=>largeVarianceResidualSpatialJet i r (x+z)) m):=
   (contDiff_residualSpatialMass_joint i j).continuous.comp
     (continuous_const.prodMk (continuous_const.add continuous_id))

 theorem integrable_residualHeatMassJet (i j:ℕ) {m:ℝ} (hm:m∈Ioo (0:ℝ) 2)
     (V:ℝ≥0) (x:ℝ):
     Integrable (fun z=>iteratedDeriv j (fun r=>largeVarianceResidualSpatialJet i r (x+z)) m)
       (gaussianReal 0 V):=by
   let ε:ℝ:=min m (2-m)/4
   have hmin:0<min m (2-m):=lt_min hm.1 (sub_pos.mpr hm.2)
   have hε:0<ε:=div_pos hmin (by norm_num)
   have hmε:m∈Icc ε (2-ε):=by
     have ha:=min_le_left m (2-m)
     have hb:=min_le_right m (2-m)
     dsimp only [ε]
     constructor <;> linarith [hmin]
   obtain ⟨K,hK,hbound⟩:=residualSpatial_mass_open_decay i j hε
   refine (integrable_const K).mono' (continuous_residualSpatialMass_section i j m x).aestronglyMeasurable
     (ae_of_all _ fun z=>?_)
   exact (hbound m hmε (x+z)).trans
     (mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg (x+z)])) hK.le |>.trans_eq (mul_one _))

 theorem residualHeatMassJet_uniform_bound (i j:ℕ) {ε:ℝ} (hε:0<ε):
     ∃K:ℝ,0<K ∧ ∀m∈Icc ε (2-ε),∀V:ℝ≥0,∀x,‖residualHeatMassJet i j m V x‖≤K:=by
   obtain ⟨K,hK,hbound⟩:=residualSpatial_mass_open_decay i j hε
   refine ⟨K,hK,?_⟩
   intro m hm V x
   unfold residualHeatMassJet
   apply (norm_integral_le_integral_norm _).trans
   have hm':m∈Ioo (0:ℝ) 2:=⟨hε.trans_le hm.1,by linarith [hm.2]⟩
   have hh:=integral_mono (integrable_residualHeatMassJet i j hm' V x).norm (integrable_const K)
     (fun z=> (hbound m hm (x+z)).trans
       (mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg (x+z)])) hK.le |>.trans_eq (mul_one _)))
   simpa using hh

 theorem hasDerivAt_residualHeatMassJet_mass (i j:ℕ) {m:ℝ} (hm:m∈Ioo (0:ℝ) 2)
     (V:ℝ≥0) (x:ℝ):HasDerivAt (fun r=>residualHeatMassJet i j r V x)
       (residualHeatMassJet i (j+1) m V x) m:=by
   let ε:ℝ:=min m (2-m)/4
   have hmin:0<min m (2-m):=lt_min hm.1 (sub_pos.mpr hm.2)
   have hε:0<ε:=div_pos hmin (by norm_num)
   have hball:∀r∈Metric.ball m ε,r∈Icc ε (2-ε):=by
     intro r hr
     have habs:|r-m|<ε:=by simpa only [Metric.mem_ball,Real.dist_eq] using hr
     have ha:=min_le_left m (2-m)
     have hb:=min_le_right m (2-m)
     have hh:=abs_lt.mp habs
     dsimp only [ε] at *
     constructor <;> linarith [hmin]
   obtain ⟨K,hK,hbound⟩:=residualSpatial_mass_open_decay i (j+1) hε
   have hd (r z:ℝ):HasDerivAt
       (fun u=>iteratedDeriv j (fun v=>largeVarianceResidualSpatialJet i v (x+z)) u)
       (iteratedDeriv (j+1) (fun v=>largeVarianceResidualSpatialJet i v (x+z)) r) r:=by
     have hh:=((contDiff_largeVarianceResidualSpatialJet_mass i (x+z)).differentiable_iteratedDeriv j
       (by exact_mod_cast WithTop.coe_lt_top j) r).hasDerivAt
     simpa only [iteratedDeriv_succ] using hh
   have hh:=hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ:=gaussianReal 0 V)
     (F:=fun r z=>iteratedDeriv j (fun v=>largeVarianceResidualSpatialJet i v (x+z)) r)
     (F':=fun r z=>iteratedDeriv (j+1) (fun v=>largeVarianceResidualSpatialJet i v (x+z)) r)
     (bound:=fun _=>K) (Metric.ball_mem_nhds m hε)
     (Eventually.of_forall fun r=>(continuous_residualSpatialMass_section i j r x).aestronglyMeasurable)
     (integrable_residualHeatMassJet i j hm V x)
     (continuous_residualSpatialMass_section i (j+1) m x).aestronglyMeasurable
     (ae_of_all _ fun z r hr=>(hbound r (hball r hr) (x+z)).trans
       (mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg (x+z)])) hK.le |>.trans_eq (mul_one _)))
     (integrable_const K) (ae_of_all _ fun z r _=>hd r z)
   exact hh.2

 theorem iteratedDeriv_residualHeatMassJet_mass (i j:ℕ) {m:ℝ} (hm:m∈Ioo (0:ℝ) 2)
     (V:ℝ≥0) (x:ℝ):
     iteratedDeriv j (fun r=>residualHeatMassJet i 0 r V x) m=residualHeatMassJet i j m V x:=by
   induction j generalizing m with
   | zero=>simp
   | succ j ih=>
     rw [iteratedDeriv_succ]
     have he:iteratedDeriv j (fun r=>residualHeatMassJet i 0 r V x)=ᶠ[𝓝 m]
         (fun r=>residualHeatMassJet i j r V x):=
       Filter.Eventually.mono (isOpen_Ioo.mem_nhds hm) (fun r hr=>ih hr)
     rw [he.deriv_eq]
     exact (hasDerivAt_residualHeatMassJet_mass i j hm V x).deriv

end DepthPaper
