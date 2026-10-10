module

public import GeneralDepthPaper.DerivativeChain
public import GeneralDepthPaper.ResidualHeatVarianceJets
public import GeneralDepthPaper.NormalizerJetBounds

@[expose] public section


/-! Genuine smoothness of the Gaussian residual and reciprocal-normalizer
sections needed for repeated product rules. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open ColeHopfFoundation.ProbabilityTheory
open scoped ContDiff NNReal Topology
namespace GeneralDepthPaper

 theorem contDiff_residualHeat_base_space {m:ℝ} (hm:m∈Ioo (0:ℝ) 2) (V:ℝ≥0):
     ContDiff ℝ ∞ (fun x=>residualHeatMassJet 0 0 m V x):=by
   have he:(fun x=>residualHeatMassJet 0 0 m V x)=
       fun x=>∫z,largeVarianceResidual m (x+z) ∂gaussianReal 0 V:=by
     funext x
     simp only [residualHeatMassJet,iteratedDeriv_zero]
     apply integral_congr_ae
     exact ae_of_all _ fun z=>(iteratedDeriv_largeVarianceResidual_spatial 0 m (x+z)).symm
   rw [he]
   exact contDiff_infty.mpr (fun n=>contDiff_integral_comp_add_gaussianReal
     ((contDiff_residual_spatial m).of_le (by simp))
       (fun a _=>hasExpGrowth_residual_spatialJet a hm) V)

 theorem hasDerivAt_residualHeat_space (i:ℕ) {m:ℝ} (hm:m∈Ioo (0:ℝ) 2) (V:ℝ≥0) (x:ℝ):
     HasDerivAt (fun y=>residualHeatMassJet i 0 m V y) (residualHeatMassJet (i+1) 0 m V x) x:=by
   have hf:=contDiff_residualHeat_base_space hm V
   have hd:=((hf.differentiable_iteratedDeriv i (by exact_mod_cast WithTop.coe_lt_top i)) x).hasDerivAt
   have he:iteratedDeriv i (fun y=>residualHeatMassJet 0 0 m V y)=
       fun y=>residualHeatMassJet i 0 m V y:=funext (iteratedDeriv_residualHeat_spatial i hm V)
   have he':iteratedDeriv (i+1) (fun y=>residualHeatMassJet 0 0 m V y) x=
       residualHeatMassJet (i+1) 0 m V x:=iteratedDeriv_residualHeat_spatial (i+1) hm V x
   rw [←iteratedDeriv_succ] at hd
   rwa [he,he'] at hd

 theorem contDiff_residualHeat_space (i:ℕ) {m:ℝ} (hm:m∈Ioo (0:ℝ) 2) (V:ℝ≥0):
     ContDiff ℝ ∞ (fun x=>residualHeatMassJet i 0 m V x):=by
   rw [←contDiffOn_univ]
   exact contDiffOn_of_derivative_chain isOpen_univ
     (fun j x=>residualHeatMassJet j 0 m V x)
     (fun j x _=>hasDerivAt_residualHeat_space j hm V x) i

 theorem contDiffOn_residualHeat_mass (i j:ℕ) (V:ℝ≥0) (x:ℝ):
     ContDiffOn ℝ ∞ (fun m=>residualHeatMassJet i j m V x) (Ioo (0:ℝ) 2):=
   contDiffOn_of_derivative_chain isOpen_Ioo
     (fun j m=>residualHeatMassJet i j m V x)
     (fun j m hm=>hasDerivAt_residualHeatMassJet_mass i j hm V x) j

 theorem contDiffOn_residualHeat_variance (i:ℕ) {m:ℝ} (hm:m∈Ioo (0:ℝ) 2) (x:ℝ):
     ContDiffOn ℝ ∞ (fun V=>residualHeatMassJet i 0 m V.toNNReal x) (Ioi (0:ℝ)):=by
   have hh:=contDiffOn_of_derivative_chain isOpen_Ioi
     (fun k V=>(1/2:ℝ)^k*residualHeatMassJet (i+2*k) 0 m V.toNNReal x)
     (fun k V hV=>by
       have hd:=(hasDerivAt_residualHeatMassJet_variance (i+2*k) hm hV x).const_mul ((1/2:ℝ)^k)
       convert hd using 1
       rw [pow_succ]
       have hi:i+2*k+2=i+2*(k+1):=by omega
       rw [hi]
       ring) 0
   convert hh using 1 <;> simp

 theorem NormalizerExpr.contDiff_weightedEval_space (e:NormalizerExpr) (m V:ℝ):
     ContDiff ℝ ∞ (e.weightedEval m V):=by
   rw [←contDiffOn_univ]
   exact contDiffOn_of_derivative_chain isOpen_univ
     (fun i x=>(weightedDx^[i] e).weightedEval m V x)
     (fun i x _=>by simpa only [Function.iterate_succ_apply'] using
       ((weightedDx^[i] e).hasDerivAt_weightedEval_space m V x)) 0

 theorem NormalizerExpr.contDiff_weightedEval_mass (e:NormalizerExpr) (V x:ℝ):
     ContDiff ℝ ∞ (fun m=>e.weightedEval m V x):=by
   rw [←contDiffOn_univ]
   exact contDiffOn_of_derivative_chain isOpen_univ
     (fun j m=>(weightedDm^[j] e).weightedEval m V x)
     (fun j m _=>by simpa only [Function.iterate_succ_apply'] using
       ((weightedDm^[j] e).hasDerivAt_weightedEval_mass m V x)) 0

 theorem NormalizerExpr.contDiff_weightedEval_variance (e:NormalizerExpr) (m x:ℝ):
     ContDiff ℝ ∞ (fun V=>e.weightedEval m V x):=by
   rw [←contDiffOn_univ]
   exact contDiffOn_of_derivative_chain isOpen_univ
     (fun k V=>(weightedDV^[k] e).weightedEval m V x)
     (fun k V _=>by simpa only [Function.iterate_succ_apply'] using
       ((weightedDV^[k] e).hasDerivAt_weightedEval_variance m V x)) 0

end GeneralDepthPaper
