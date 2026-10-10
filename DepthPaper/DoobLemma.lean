module

public import DepthPaper.TerminalDoobUniqueness

@[expose] public section


/-! Literal Appendix B.2 for every continuous solution on the canonical
Brownian space. The solution equation is exactly the paper's hypothesis;
its law, probability normalization and comparison are consequences. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
open scoped NNReal ENNReal
namespace DepthPaper

 theorem terminal_doob_law_of_solution {m:ℝ} (hm:0 < m) (hm1:m ≤ 1)
     (W:ℝ≥0) (hW:0<W) (x:ℝ)
     (X:ℝ≥0→Paper.BrownianSample→ℝ)
     (hX:∀sample,Continuous (fun t=>X t sample))
     (hXe:∀t:ℝ≥0,t≤W → ∀sample,X t sample=x+
       PositiveFieldPaper.paperBrownian (Real.sqrt (W:ℝ)) t sample+
         ∫r in (0:ℝ)..(t:ℝ),m*deriv (terminalDoobPotential m W r.toNNReal) (X r.toNNReal sample))
     (t:ℝ≥0) (ht:0<t) (htW:t≤W) :
     canonicalBrownianMeasure.map (X t)=
       volume.withDensity (fun y=>ENNReal.ofReal (terminalDoobDensity m W t x y)) ∧
     (1/4:ℝ≥0∞)•limitingDoobMeasure m t x ≤ canonicalBrownianMeasure.map (X t) ∧
       canonicalBrownianMeasure.map (X t) ≤ (4:ℝ≥0∞)•limitingDoobMeasure m t x := by
   have hpoint:X t=terminalDoobState m W hW x t:=by
     funext sample
     have hh:=terminalDoobState_unique ⟨hm.le,hm1⟩ W hW x sample
       (fun r=>X r.toNNReal sample) ((hX sample).comp continuous_real_toNNReal)
       (by
         intro r hr
         have he:=hXe r.toNNReal
           (by rw [←NNReal.coe_le_coe,Real.coe_toNNReal _ hr.1];exact hr.2) sample
         simpa only [Real.coe_toNNReal _ hr.1] using he)
       ⟨t.coe_nonneg,htW⟩
     simpa only [Real.toNNReal_coe] using hh
   rw [hpoint,terminalDoobState_law ⟨hm.le,hm1⟩ W hW x t ht htW]
   exact ⟨terminalDoobMeasure_eq_density m W t ht x,
     terminalDoobMeasure_comparison_four hm hm1 W t htW x⟩

end DepthPaper
