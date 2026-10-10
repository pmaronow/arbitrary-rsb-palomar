module

public import GeneralDepthPaper.TerminalDoobSDE

@[expose] public section


/-! Appendix B.2: a canonical adapted strong diffusion with the exact Gaussian
h-transform density and the literal measure comparison. All stochastic and
normalization inputs are proved in the imported construction. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
open scoped NNReal ENNReal
namespace GeneralDepthPaper

 def terminalDoobDensity (m:ℝ) (W t:ℝ≥0) (x y:ℝ):ℝ :=
   gaussianPDFReal x t y*terminalDoobWeight m W t x y

 theorem measurable_terminalDoobWeight (m:ℝ) (W t:ℝ≥0) (x:ℝ) :
     Measurable (terminalDoobWeight m W t x) := by
   have hc:Continuous (terminalDoobPotential m W t):=by
     change Continuous (fun y=>ColeHopfFoundation.ProbabilityTheory.coleHopf m (W-t)
       (fun z=>Real.log (Real.cosh z)) y)
     simpa only [Real.toNNReal_coe,Function.comp_def,id_eq] using
       (ColeHopfFoundation.ProbabilityTheory.continuous_coleHopf
         (Real.continuous_cosh.log fun z=>(Real.cosh_pos z).ne') hasLinearGrowth_logCosh m).comp
         (continuous_id.prodMk (continuous_const (y:=((W-t:ℝ≥0):ℝ))))
   exact (hc.measurable.sub_const _).const_mul m |>.exp

 theorem terminalDoobMeasure_eq_density (m:ℝ) (W t:ℝ≥0) (ht:0<t) (x:ℝ) :
     terminalDoobMeasure m W t x=
       volume.withDensity (fun y=>ENNReal.ofReal (terminalDoobDensity m W t x y)) := by
   rw [terminalDoobMeasure,gaussianReal_of_var_ne_zero x ht.ne',
     ←withDensity_mul volume (measurable_gaussianPDF x t)
       ((measurable_terminalDoobWeight m W t x).ennreal_ofReal)]
   congr 1
   funext y
   exact (ENNReal.ofReal_mul (gaussianPDFReal_nonneg x t y)).symm

 theorem terminalDoobDensity_explicit (m:ℝ) (W t:ℝ≥0) (x y:ℝ) :
     terminalDoobDensity m W t x y=gaussianPDFReal x t y*
       Real.exp (m*terminalDoobPotential m W t y)/
         Real.exp (m*terminalDoobPotential m W 0 x) := by
   unfold terminalDoobDensity terminalDoobWeight
   rw [mul_sub,Real.exp_sub]
   ring

 theorem stronglyMeasurable_terminalDoobState (m:ℝ) (W:ℝ≥0) (hW:0<W)
     (x:ℝ) (t:ℝ≥0) :
     StronglyMeasurable[canonicalBrownianFiltration ((t:ℝ)/(W:ℝ)).toNNReal]
       (terminalDoobState m W hW x t) :=
   FRSB.stronglyAdapted_selectedParisiState _ _ _ _ _

 /-- Exact law for the actually constructed terminal diffusion, with the
 Brownian driver and drift equation included in the same closed result. -/
 theorem terminal_doob_diffusion {m:ℝ} (hm:0 < m) (hm1:m ≤ 1) (W:ℝ≥0) (hW:0<W) (x:ℝ) :
     IsBrownianReal (PositiveFieldPaper.paperBrownian (Real.sqrt (W:ℝ))) canonicalBrownianMeasure ∧
     (∀sample,terminalDoobState m W hW x 0 sample=x) ∧
     (∀sample,Continuous (fun t:ℝ≥0=>terminalDoobState m W hW x t sample)) ∧
     (∀t:ℝ≥0, t≤W → ∀sample,
       terminalDoobState m W hW x t sample=x+
         PositiveFieldPaper.paperBrownian (Real.sqrt (W:ℝ)) t sample+
           ∫r in (0:ℝ)..(t:ℝ),m*deriv (terminalDoobPotential m W r.toNNReal)
             (terminalDoobState m W hW x r.toNNReal sample)) ∧
     (∀t:ℝ≥0,0<t → t≤W →
       canonicalBrownianMeasure.map (terminalDoobState m W hW x t)=
         volume.withDensity (fun y=>ENNReal.ofReal (terminalDoobDensity m W t x y))) ∧
     (∀t:ℝ≥0,0<t → t≤W →
       (1/4:ℝ≥0∞)•limitingDoobMeasure m t x ≤ terminalDoobMeasure m W t x ∧
         terminalDoobMeasure m W t x ≤ (4:ℝ≥0∞)•limitingDoobMeasure m t x) := by
   exact ⟨isBrownianReal_terminalDoob_driver W hW,
     terminalDoobState_initial m W hW x,continuous_terminalDoobState m W hW x,
     fun t ht=>terminalDoobState_integral_equation ⟨hm.le,hm1⟩ W hW x t ht,
     fun t ht htW=>(terminalDoobState_law ⟨hm.le,hm1⟩ W hW x t ht htW).trans
       (terminalDoobMeasure_eq_density m W t ht x),
     fun t _ htW=>terminalDoobMeasure_comparison_four hm hm1 W t htW x⟩

end GeneralDepthPaper
