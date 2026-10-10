module

public import DepthPaper.TerminalDoobLaw

@[expose] public section


/-! Pathwise uniqueness for Appendix B.2 in the canonical Brownian realization.
Any continuous path satisfying the literal terminal drift equation equals the
constructed path; the endpoint law is therefore independent of the solution
choice in this realization. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
open scoped NNReal ENNReal
namespace DepthPaper

 theorem terminalDoobState_unique {m:ℝ} (hm:m∈Icc (0:ℝ) 1)
     (W:ℝ≥0) (hW:0<W) (x:ℝ) (sample:Paper.BrownianSample)
     (X:ℝ→ℝ) (hX:Continuous X)
     (hXe:∀t∈Icc (0:ℝ) (W:ℝ),X t=x+
       PositiveFieldPaper.paperBrownian (Real.sqrt (W:ℝ)) t.toNNReal sample+
         ∫r in (0:ℝ)..t,m*deriv (terminalDoobPotential m W r.toNNReal) (X r)) :
     EqOn X (fun t=>terminalDoobState m W hW x t.toNNReal sample) (Icc (0:ℝ) (W:ℝ)) := by
   let β:=Real.sqrt (W:ℝ)
   have hβ:β≠0:=(Real.sqrt_pos.mpr (show 0<(W:ℝ) from hW)).ne'
   let N:ℝ→ℝ:=fun t=>PositiveFieldPaper.paperBrownian β t.toNNReal sample
   have hN:Continuous N:=by
     unfold N PositiveFieldPaper.paperBrownian
     exact ((continuous_canonicalBrownian sample).comp
       ((continuous_const.mul continuous_real_toNNReal))).const_mul β
   let f:ℝ→ℝ→ℝ:=fun t y=>m*parisiGradient β (terminalParisiMeasure m) (t/(W:ℝ),y+N t)
   have hf:IsBoundedMeasurableDrift f 1 1:=by
     constructor
     · exact (continuous_const.mul ((continuous_parisiGradient β _).comp
         ((continuous_fst.div_const _).prodMk (continuous_snd.add (hN.comp continuous_fst))))).measurable
     · intro t y
       change ‖m*parisiGradient β (terminalParisiMeasure m) (t/(W:ℝ),y+N t)‖≤1
       rw [norm_mul,Real.norm_of_nonneg hm.1]
       exact (mul_le_mul_of_nonneg_left (norm_parisiGradient_le_one β _ _) hm.1).trans
         (by simpa only [mul_one] using hm.2)
     · intro t
       apply LipschitzWith.of_dist_le_mul
       intro y z
       change dist (m*parisiGradient β (terminalParisiMeasure m) (t/(W:ℝ),y+N t))
         (m*parisiGradient β (terminalParisiMeasure m) (t/(W:ℝ),z+N t))≤1*dist y z
       rw [Real.dist_eq,←mul_sub,abs_mul,abs_of_nonneg hm.1]
       have hh:|parisiGradient β (terminalParisiMeasure m) (t/(W:ℝ),y+N t)-
           parisiGradient β (terminalParisiMeasure m) (t/(W:ℝ),z+N t)|≤dist y z:=by
         simpa only [NNReal.coe_one,one_mul,dist_add_right,Real.dist_eq] using
           (lipschitzWith_parisiGradient β hβ (terminalParisiMeasure m) (t/(W:ℝ))).dist_le_mul (y+N t) (z+N t)
       exact (mul_le_mul_of_nonneg_left hh hm.1).trans (by gcongr;exact hm.2)
   have hconvert (Z:ℝ→ℝ) (hZe:∀t∈Icc (0:ℝ) (W:ℝ),Z t=x+N t+
       ∫r in (0:ℝ)..t,m*deriv (terminalDoobPotential m W r.toNNReal) (Z r)) :
       ∀t∈Icc (0:ℝ) (W:ℝ),(Z t-N t)=x+∫r in (0:ℝ)..t,f r (Z r-N r):=by
     intro t ht
     rw [hZe t ht]
     have he:(∫r in (0:ℝ)..t,m*deriv (terminalDoobPotential m W r.toNNReal) (Z r))=
         ∫r in (0:ℝ)..t,f r (Z r-N r):=by
       apply intervalIntegral.integral_congr_Ioo_of_le ht.1
       intro r hr
       change m*deriv (terminalDoobPotential m W r.toNNReal) (Z r)=f r (Z r-N r)
       rw [terminalDoobPotential_deriv hm W hW ⟨hr.1.le,hr.2.le.trans ht.2⟩]
       simp only [f,sub_add_cancel,β]
     rw [he]
     ring
   let Z:ℝ→ℝ:=fun t=>terminalDoobState m W hW x t.toNNReal sample
   have hZ:Continuous Z:=(continuous_terminalDoobState m W hW x sample).comp continuous_real_toNNReal
   have hZe:∀t∈Icc (0:ℝ) (W:ℝ),Z t=x+N t+
       ∫r in (0:ℝ)..t,m*deriv (terminalDoobPotential m W r.toNNReal) (Z r):=by
     intro t ht
     have he:=terminalDoobState_integral_equation hm W hW x t.toNNReal
       (by rw [←NNReal.coe_le_coe,Real.coe_toNNReal _ ht.1];exact ht.2) sample
     simpa only [Real.coe_toNNReal _ ht.1] using he
   have hy:=IntegralPicard.real_solution_unique W.coe_nonneg hf (fun t=>X t-N t)
     (hX.sub hN) (hconvert X hXe)
   have hz:=IntegralPicard.real_solution_unique W.coe_nonneg hf (fun t=>Z t-N t)
     (hZ.sub hN) (hconvert Z hZe)
   intro t ht
   have he: X t-N t=Z t-N t:=(hy t ht).trans (hz t ht).symm
   change X t=Z t
   linarith

end DepthPaper
