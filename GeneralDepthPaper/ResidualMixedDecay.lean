module

public import GeneralDepthPaper.PositiveResidualJetBounds

@[expose] public section


/-! Uniform decay of genuine mixed spatial/mass residual derivatives.
The compact polynomial bounds and endpoint cancellation are both used. -/
noncomputable section
open Set
open scoped ContDiff Polynomial
namespace GeneralDepthPaper

 theorem residualSpatial_mass_decay_positive (i j:ℕ) {ε:ℝ} (hε:0<ε) (hε1:ε≤1):
     ∃K:ℝ,0<K ∧ ∀m∈Icc ε 1,∀x≥0,
       ‖iteratedDeriv j (fun r=>largeVarianceResidualSpatialJet i r x) m‖≤
         K*Real.exp (-(ε/2)*x):=by
   obtain ⟨K1,hK1,hbound1⟩:=bivariateValue_mass_uniform_bounds
     (Polynomial.C (Polynomial.X^i)) j ε 1
   obtain ⟨K2,hK2,hbound2⟩:=bivariateValue_mass_uniform_bounds
     (Polynomial.C ((-Polynomial.X)^i-Polynomial.X^i)) j ε 1
   obtain ⟨K3,hK3,hbound3⟩:=bivariateValue_mass_uniform_bounds (coshPowerEndpointQuotient i) j ε 1
   obtain ⟨KR,hKR,hboundR⟩:=residual_mass_uniform_jets j hε
   let C:ℝ:=(j.factorial:ℝ)/(ε/2)^j*Real.exp ((ε/2)*(1+Real.log 2))
   have hC:0<C:=by
     dsimp only [C]
     have hfac:0<(j.factorial:ℝ):=by exact_mod_cast Nat.factorial_pos j
     positivity
   let K:ℝ:=(2:ℝ)^j*K1*KR+(2:ℝ)^j*K2*C+2*((2:ℝ)^j*K3)*C
   refine ⟨K,by dsimp only [K];positivity,?_⟩
   intro m hm x hx
   have hm0:0≤m:=hε.le.trans hm.1
   have hlog2:0≤Real.log 2:=Real.log_nonneg (by norm_num)
   let R:ℝ:=1+x+Real.log 2
   have hR:1≤R:=by dsimp only [R];linarith
   have hp:R^j*Real.exp (-ε*x)≤C*Real.exp (-(ε/2)*x):=by
     have hh:=polynomial_times_exp_bound j (ε:=ε/2) (c:=1+Real.log 2) (u:=x)
       (by positivity) (by linarith) hx
     have he:Real.exp (-ε*x)=Real.exp (-(ε/2)*x)*Real.exp (-(ε/2)*x):=by
       rw [←Real.exp_add];congr 1;ring
     rw [he]
     have hh':=mul_le_mul_of_nonneg_right hh (Real.exp_pos (-(ε/2)*x)).le
     convert hh' using 1 <;> dsimp only [R,C] <;> ring
   let f1:ℝ→ℝ:=fun r=>r^i*largeVarianceResidual r x
   let f2:ℝ→ℝ:=fun r=>((-r)^i-r^i)*Real.exp (r*(-x-Real.log 2))
   let f3:ℝ→ℝ:=fun r=>bivariateValue (coshPowerEndpointQuotient i) r (Real.tanh x)*coshPower r x
   have hf1:ContDiff ℝ ∞ f1:=(contDiff_id.pow i).mul (contDiff_residual_mass x)
   have hf2:ContDiff ℝ ∞ f2:=((contDiff_id.neg.pow i).sub (contDiff_id.pow i)).mul
     (contDiff_id.mul contDiff_const).exp
   have hf3:ContDiff ℝ ∞ f3:=(contDiff_bivariateValue_mass _ _).mul (contDiff_coshPower_mass x)
   have hb1:‖iteratedDeriv j f1 m‖≤(2:ℝ)^j*K1*KR*Real.exp (-(ε/2)*x):=by
     have hh:=norm_iteratedDeriv_mul_le j (m:=m) (contDiff_id.pow i) (contDiff_residual_mass x)
       (A:=K1) (B:=KR*Real.exp (-(ε/2)*x)) (by positivity) (by positivity)
       (fun k hk=>by
         have hb:=hbound1 k hk m hm 0 (by norm_num)
         simpa [bivariateValue] using hb)
       (fun k hk=>by simpa only [abs_of_nonneg hx] using hboundR k hk m hm x)
     simp only [id_eq] at hh
     convert hh using 1 <;> try dsimp only [f1]
     all_goals ring
   have hb2:‖iteratedDeriv j f2 m‖≤(2:ℝ)^j*K2*C*Real.exp (-(ε/2)*x):=by
     have hh:=norm_iteratedDeriv_mul_le j (m:=m) ((contDiff_id.neg.pow i).sub (contDiff_id.pow i))
       (contDiff_id.mul contDiff_const).exp
       (A:=K2) (B:=R^j*Real.exp (-ε*x)) (by positivity) (by positivity)
       (fun k hk=>by
         have hb:=hbound2 k hk m hm 0 (by norm_num)
         simpa [bivariateValue] using hb)
       (negativeExp_mass_uniform_jets j hε hm hx)
     have hh':=hh.trans (mul_le_mul_of_nonneg_left hp (show 0≤(2:ℝ)^j*K2 by positivity))
     simp only [id_eq,Pi.neg_apply] at hh'
     convert hh' using 1 <;> try dsimp only [f2,R]
     all_goals ring
   have hb3:‖iteratedDeriv j f3 m‖≤(2:ℝ)^j*K3*R^j*Real.exp (m*x):=by
     have hT:Real.tanh x∈Icc (-1:ℝ) 1:=⟨(Real.neg_one_lt_tanh x).le,(Real.tanh_lt_one x).le⟩
     have hh:=norm_iteratedDeriv_mul_le j (m:=m) (contDiff_bivariateValue_mass _ _) (contDiff_coshPower_mass x)
       (A:=K3) (B:=R^j*Real.exp (m*x)) (by positivity) (by positivity)
       (fun k hk=>hbound3 k hk m hm _ hT) (coshPower_mass_uniform_jets j hm0 hx)
     convert hh using 1 <;> dsimp only [f3,R] <;> ring
   have hb3':‖Real.tanh x-1‖*‖iteratedDeriv j f3 m‖≤
       2*((2:ℝ)^j*K3)*C*Real.exp (-(ε/2)*x):=by
     have hh:=mul_le_mul (tanh_endpoint_gap_bound x) hb3 (norm_nonneg _) (by positivity)
     have hexp:Real.exp (-2*x)*Real.exp (m*x)≤Real.exp (-ε*x):=by
       rw [←Real.exp_add]
       apply Real.exp_le_exp.mpr
       nlinarith [mul_le_mul_of_nonneg_right hm.2 hx,mul_le_mul_of_nonneg_right hε1 hx]
     calc
       ‖Real.tanh x-1‖*‖iteratedDeriv j f3 m‖
         ≤2*((2:ℝ)^j*K3)*R^j*(Real.exp (-2*x)*Real.exp (m*x)):=hh.trans_eq (by ring)
       _≤2*((2:ℝ)^j*K3)*(R^j*Real.exp (-ε*x)):=by
         have hh:=mul_le_mul_of_nonneg_left hexp (show 0≤2*((2:ℝ)^j*K3)*R^j by positivity)
         convert hh using 1 <;> ring
       _≤2*((2:ℝ)^j*K3)*(C*Real.exp (-(ε/2)*x)):=
         mul_le_mul_of_nonneg_left hp (by positivity)
       _=2*((2:ℝ)^j*K3)*C*Real.exp (-(ε/2)*x):=by ring
   have he:(fun r=>largeVarianceResidualSpatialJet i r x)=f1+f2-(fun r=>(Real.tanh x-1)*f3 r):=by
     funext r
     simpa only [f1,f2,f3,Pi.add_apply,Pi.sub_apply,mul_assoc] using
       largeVarianceResidualSpatialJet_endpoint_decomposition i r x
   rw [he,iteratedDeriv_sub (f:=f1+f2) (g:=fun r=>(Real.tanh x-1)*f3 r)
       ((hf1.add hf2).contDiffAt.of_le (by simp))
       ((contDiff_const.mul hf3).contDiffAt.of_le (by simp)),
     iteratedDeriv_add (f:=f1) (g:=f2) (hf1.contDiffAt.of_le (by simp)) (hf2.contDiffAt.of_le (by simp)),
     iteratedDeriv_const_mul_field]
   calc
     ‖iteratedDeriv j f1 m+iteratedDeriv j f2 m-(Real.tanh x-1)*iteratedDeriv j f3 m‖
       ≤‖iteratedDeriv j f1 m‖+‖iteratedDeriv j f2 m‖+
         ‖Real.tanh x-1‖*‖iteratedDeriv j f3 m‖:=by
           exact (norm_sub_le _ _).trans (by rw [norm_mul];gcongr;exact norm_add_le _ _)
     _≤K*Real.exp (-(ε/2)*x):=by
       have hh:=add_le_add (add_le_add hb1 hb2) hb3'
       convert hh using 1 <;> dsimp only [K] <;> ring

 theorem residualSpatial_mass_decay (i j:ℕ) {ε:ℝ} (hε:0<ε):
     ∃K:ℝ,0<K ∧ ∀m∈Icc ε 1,∀x,
       ‖iteratedDeriv j (fun r=>largeVarianceResidualSpatialJet i r x) m‖≤
         K*Real.exp (-(ε/2)*|x|):=by
   by_cases hε1:ε≤1
   · obtain ⟨K,hK,hbound⟩:=residualSpatial_mass_decay_positive i j hε hε1
     refine ⟨K,hK,?_⟩
     intro m hm x
     rcases le_total 0 x with hx|hx
     · simpa only [abs_of_nonneg hx] using hbound m hm x hx
     · have he:(fun r=>largeVarianceResidualSpatialJet i r (-x))=
           fun r=>(-1:ℝ)^i*largeVarianceResidualSpatialJet i r x:=by
         funext r;exact largeVarianceResidualSpatialJet_neg i r x
       have hnorm:‖iteratedDeriv j (fun r=>largeVarianceResidualSpatialJet i r (-x)) m‖=
           ‖iteratedDeriv j (fun r=>largeVarianceResidualSpatialJet i r x) m‖:=by
         rw [he,iteratedDeriv_const_mul_field,norm_mul,norm_pow]
         norm_num
       have hb:=hbound m hm (-x) (neg_nonneg.mpr hx)
       rw [hnorm] at hb
       simpa only [abs_of_nonpos hx] using hb
   · refine ⟨1,by norm_num,?_⟩
     intro m hm x
     exact False.elim (hε1 (hm.1.trans hm.2))

 theorem iteratedDeriv_residual_spatial_mass_decay (i j:ℕ) {ε:ℝ} (hε:0<ε):
     ∃K:ℝ,0<K ∧ ∀m∈Icc ε 1,∀x,
       ‖iteratedDeriv j (fun r=>iteratedDeriv i (largeVarianceResidual r) x) m‖≤
         K*Real.exp (-(ε/2)*|x|):=by
   simpa only [iteratedDeriv_largeVarianceResidual_spatial] using residualSpatial_mass_decay i j hε

end GeneralDepthPaper
