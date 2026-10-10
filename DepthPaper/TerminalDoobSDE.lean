module

public import DepthPaper.TerminalDoobDiffusion

@[expose] public section


/-! Literal Brownian integral equation for the terminal h-transform diffusion.
The state is the genuinely constructed Parisi state; the drift is the actual
spatial derivative of the terminal Cole–Hopf potential. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
open scoped NNReal ENNReal
namespace DepthPaper

 theorem terminalDoobPotential_deriv {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1)
     (W : ℝ≥0) (hW : 0 < W) {r : ℝ} (hr : r ∈ Icc (0:ℝ) (W:ℝ)) (x : ℝ) :
     deriv (terminalDoobPotential m W r.toNNReal) x=
       parisiGradient (Real.sqrt (W:ℝ)) (terminalParisiMeasure m) (r/(W:ℝ),x) := by
   have hβ : Real.sqrt (W:ℝ) ≠ 0 := (Real.sqrt_pos.mpr (show 0<(W:ℝ) from hW)).ne'
   have hs : r/(W:ℝ) ∈ Icc (0:ℝ) 1 :=
     ⟨div_nonneg hr.1 W.coe_nonneg,(div_le_one (show 0<(W:ℝ) from hW)).mpr hr.2⟩
   have hd:=hasDerivAt_parisiPotential_spatial (Real.sqrt (W:ℝ)) hβ
     (terminalParisiMeasure m) (r/(W:ℝ)) x hs
   exact (hd.congr_of_eventuallyEq (.of_forall fun y=>(terminalParisiMeasure_potential hm W hW hr y).symm)).deriv

 theorem terminalDoobState_eq_Y (m : ℝ) (W : ℝ≥0) (hW : 0 < W) (x : ℝ)
     (r : ℝ) (hr : 0 ≤ r) (sample : Paper.BrownianSample) :
     terminalDoobState m W hW x r.toNNReal sample=
       PositiveFieldPaper.Y (Real.sqrt (W:ℝ)) x
         (Real.sqrt_pos.mpr (show 0<(W:ℝ) from hW)).ne' (terminalParisiMeasure m) r sample := by
   simp only [terminalDoobState,PositiveFieldPaper.Y,Real.coe_toNNReal _ hr,Real.sq_sqrt W.coe_nonneg]

 theorem isBrownianReal_terminalDoob_driver (W : ℝ≥0) (hW : 0 < W) :
     IsBrownianReal (PositiveFieldPaper.paperBrownian (Real.sqrt (W:ℝ))) canonicalBrownianMeasure :=
   PositiveFieldPaper.isBrownianReal_paperBrownian _ (Real.sqrt_pos.mpr (show 0<(W:ℝ) from hW))

 theorem terminalDoobState_integral_equation {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1)
     (W : ℝ≥0) (hW : 0 < W) (x : ℝ) (t : ℝ≥0) (ht : t ≤ W)
     (sample : Paper.BrownianSample) :
     terminalDoobState m W hW x t sample=x+
       PositiveFieldPaper.paperBrownian (Real.sqrt (W:ℝ)) t sample+
         ∫r in (0:ℝ)..(t:ℝ),m*deriv (terminalDoobPotential m W r.toNNReal)
           (terminalDoobState m W hW x r.toNNReal sample) := by
   let β:=Real.sqrt (W:ℝ)
   have hβ:β≠0 := (Real.sqrt_pos.mpr (show 0<(W:ℝ) from hW)).ne'
   have hβsq:β^2=(W:ℝ):=Real.sq_sqrt W.coe_nonneg
   have htI:(t:ℝ)∈Icc (0:ℝ) (PositiveFieldPaper.L β):=by
     simpa only [PositiveFieldPaper.L,hβsq] using (show (t:ℝ)∈Icc (0:ℝ) (W:ℝ) from ⟨t.coe_nonneg,ht⟩)
   have he:=PositiveFieldPaper.optimal_diffusion_integral_equation β x hβ
     (terminalParisiMeasure m) htI sample
   rw [←terminalDoobState_eq_Y m W hW x (t:ℝ) t.coe_nonneg sample,Real.toNNReal_coe] at he
   apply he.trans
   congr 1
   apply intervalIntegral.integral_congr_Ioo_of_le t.coe_nonneg
   intro r hr
   have hrW:r∈Icc (0:ℝ) (W:ℝ):=⟨hr.1.le,hr.2.le.trans ht⟩
   have hrm:r/(W:ℝ)∈Ico (0:ℝ) 1:=
     ⟨div_nonneg hr.1.le W.coe_nonneg,(div_lt_one (show 0<(W:ℝ) from hW)).mpr (hr.2.trans_le ht)⟩
   have hrI:r∈Icc (0:ℝ) (PositiveFieldPaper.L β):=by simpa only [PositiveFieldPaper.L,hβsq] using hrW
   simp only [PositiveFieldPaper.mass,hβsq,terminalParisiMeasure_cdf hm hrm,
     PositiveFieldPaper.B_eq_gradient β hβ _ r _ hrI]
   rw [←terminalDoobState_eq_Y m W hW x r hr.1.le sample,terminalDoobPotential_deriv hm W hW hrW]

 theorem continuous_terminalDoobState (m : ℝ) (W : ℝ≥0) (hW : 0 < W) (x : ℝ)
     (sample : Paper.BrownianSample) : Continuous (fun t:ℝ≥0=>terminalDoobState m W hW x t sample) := by
   have hc:Continuous (fun t:ℝ≥0=>((t:ℝ)/(W:ℝ)).toNNReal):=by fun_prop
   exact ((boundedDriftItoCharacteristics_selectedParisiState (Real.sqrt (W:ℝ)) x
     (Real.sqrt_pos.mpr (show 0<(W:ℝ) from hW)).ne' (terminalParisiMeasure m)).continuous_state sample).comp hc

end DepthPaper
