module

public import GeneralDepthPaper.DoobKernelMeasures
public import FRSB.ConstantMassLaw
public import PositiveFieldPaper.ClockModel

@[expose] public section


/-! A canonical strong realization of the constant-mass terminal Cole–Hopf
diffusion. Its law is identified from the proved conditional transition theorem;
the desired h-transform law is not an assumption. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper FRSB
open ColeHopfFoundation.ProbabilityTheory
open scoped NNReal ENNReal
namespace GeneralDepthPaper

 def terminalParisiMeasure (m : ℝ) : Paper.ParisiMeasure :=
   parisiMix (diracOverlap 1 (by norm_num)) (diracOverlap 0 (by norm_num)) m

 theorem terminalParisiMeasure_cdf {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) {s : ℝ}
     (hs : s ∈ Ico (0:ℝ) 1) : parisiCDF (terminalParisiMeasure m) s=m := by
   rw [terminalParisiMeasure,parisiCDF_mix _ _ m s hm,parisiCDF_dirac,parisiCDF_dirac]
   simp only [if_neg (not_le.mpr hs.2),if_pos hs.1,mul_zero,mul_one,zero_add]

 theorem terminalParisiMeasure_potential {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1)
     (W : ℝ≥0) (hW : 0 < W) {r : ℝ} (hr : r ∈ Icc (0:ℝ) (W:ℝ)) (x : ℝ) :
     parisiPotential (Real.sqrt (W:ℝ)) (terminalParisiMeasure m) (r/(W:ℝ),x)=
       terminalDoobPotential m W r.toNNReal x := by
   have hβ : Real.sqrt (W:ℝ) ≠ 0 := (Real.sqrt_pos.mpr (show 0<(W:ℝ) from hW)).ne'
   have hs : r/(W:ℝ) ∈ Icc (0:ℝ) 1 :=
     ⟨div_nonneg hr.1 W.coe_nonneg,(div_le_one (show 0<(W:ℝ) from hW)).mpr hr.2⟩
   have he := parisiPotential_coleHopf_constant_interval (Real.sqrt (W:ℝ)) hβ
     (terminalParisiMeasure m) (a:=0) (b:=1) (m:=m) le_rfl zero_lt_one le_rfl
     (fun s hs=>terminalParisiMeasure_cdf hm hs) hs ⟨hs.2,le_rfl⟩ x
   simp only [parisiPotential_terminal] at he
   have hv : ((Real.sqrt (W:ℝ))^2*(1-r/(W:ℝ))).toNNReal=W-r.toNNReal := by
     apply NNReal.coe_injective
     rw [Real.sq_sqrt W.coe_nonneg,Real.coe_toNNReal _
       (mul_nonneg W.coe_nonneg (sub_nonneg.mpr hs.2)),NNReal.coe_sub
       (by exact_mod_cast (show r.toNNReal ≤ W by
         rw [←NNReal.coe_le_coe,Real.coe_toNNReal _ hr.1];exact hr.2)),Real.coe_toNNReal _ hr.1]
     field_simp
   rw [hv] at he
   exact he

 def terminalDoobState (m : ℝ) (W : ℝ≥0) (hW : 0 < W) (x : ℝ) (t : ℝ≥0) :
     Paper.BrownianSample → ℝ :=
   selectedParisiItoState (Real.sqrt (W:ℝ)) x
     (Real.sqrt_pos.mpr (show 0<(W:ℝ) from hW)).ne' (terminalParisiMeasure m)
     ((t:ℝ)/(W:ℝ)).toNNReal

 theorem terminalDoobState_initial (m : ℝ) (W : ℝ≥0) (hW : 0 < W) (x : ℝ)
     (sample : Paper.BrownianSample) : terminalDoobState m W hW x 0 sample=x := by
   unfold terminalDoobState
   simp only [NNReal.coe_zero,zero_div,Real.toNNReal_zero]
   rw [selectedParisiItoState_eq _ _ _ _ (by simp)]
   exact selectedParisiState_initial _ _ _ _ _

 theorem terminalDoobState_law {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1)
     (W : ℝ≥0) (hW : 0 < W) (x : ℝ) (t : ℝ≥0) (ht : 0 < t) (htW : t ≤ W) :
     canonicalBrownianMeasure.map (terminalDoobState m W hW x t)=terminalDoobMeasure m W t x := by
   let β := Real.sqrt (W:ℝ)
   have hβ : β ≠ 0 := (Real.sqrt_pos.mpr (show 0<(W:ℝ) from hW)).ne'
   let T := ((t:ℝ)/(W:ℝ)).toNNReal
   have hTpos : 0 < T := Real.toNNReal_pos.mpr (div_pos (show 0<(t:ℝ) from ht) (show 0<(W:ℝ) from hW))
   have hT : (T:ℝ) ≤ 1 := by
     rw [Real.coe_toNNReal _ (div_nonneg t.coe_nonneg W.coe_nonneg)]
     exact (div_le_one (show 0<(W:ℝ) from hW)).mpr (show (t:ℝ) ≤ W from htW)
   have hC : ∀s∈Ico (0:ℝ) (0+T),parisiCDF (terminalParisiMeasure m) s=m := by
     intro s hs
     exact terminalParisiMeasure_cdf hm ⟨hs.1,hs.2.trans_le (by simpa only [zero_add] using hT)⟩
   have he := selectedParisiState_constantMass_restricted_transitionLaw β x hβ
     (terminalParisiMeasure m) 0 T hTpos (by simpa using hT) m hC univ .univ
   simp only [Measure.restrict_univ,zero_add] at he
   have hi : canonicalBrownianMeasure.map (selectedParisiItoState β x hβ (terminalParisiMeasure m) 0)=Measure.dirac x := by
     have hf : selectedParisiItoState β x hβ (terminalParisiMeasure m) 0=fun _ : Paper.BrownianSample=>x := by
       funext sample
       rw [selectedParisiItoState_eq _ _ _ _ (by simp)]
       exact selectedParisiState_initial _ _ _ _ _
     rw [hf,Measure.map_const]
     simp
   rw [hi] at he
   have hk : parisiConstantMassKernel β (terminalParisiMeasure m) 0 T m x=terminalDoobMeasure m W t x := by
     rw [parisiConstantMassKernel_apply_actual β hβ _ 0 T hTpos (by simpa using hT) m hC]
     have hv : (β^2*(T:ℝ)).toNNReal=t := by
       apply NNReal.coe_injective
       rw [Real.coe_toNNReal _ (mul_nonneg (sq_nonneg β) T.coe_nonneg),
         Real.coe_toNNReal _ (div_nonneg t.coe_nonneg W.coe_nonneg)]
       dsimp only [β]
       rw [Real.sq_sqrt W.coe_nonneg]
       field_simp
     rw [hv]
     unfold terminalDoobMeasure terminalDoobWeight
     congr 1
     funext y
     have hp := terminalParisiMeasure_potential hm W hW
       (r:=(t:ℝ)) ⟨t.coe_nonneg,show (t:ℝ) ≤ W from htW⟩ y
     have hp0 := terminalParisiMeasure_potential hm W hW (r:=0) ⟨le_rfl,W.coe_nonneg⟩ x
     simp only [Real.toNNReal_coe,zero_div,Real.toNNReal_zero] at hp hp0
     simp only [NNReal.coe_zero,zero_add]
     rw [Real.coe_toNNReal _ (div_nonneg t.coe_nonneg W.coe_nonneg)]
     rw [hp,hp0]
   change canonicalBrownianMeasure.map (terminalDoobState m W hW x t)=_ at he
   rw [Measure.dirac_bind (parisiConstantMassKernel β (terminalParisiMeasure m) 0 T m).measurable] at he
   exact he.trans hk

end GeneralDepthPaper
