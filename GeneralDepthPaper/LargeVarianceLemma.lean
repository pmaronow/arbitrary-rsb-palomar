module

public import GeneralDepthPaper.SourceLogarithmicErrorBounds
public import GeneralDepthPaper.LargeVarianceCompactZeroth

@[expose] public section


/-! Literal Appendix B.1: actual Cole–Hopf expansion and every mixed derivative
of its actual error, uniformly on a compact positive mass set. -/
noncomputable section
open Set
open scoped BigOperators NNReal
namespace GeneralDepthPaper

 theorem largeVarianceError_uniform_order {ε:ℝ} (hε:0<ε) (J:ℕ):
     ∃CJ:ℝ,0<CJ ∧ ∀m∈Icc ε 1,∀V≥1,∀x:ℝ,∀i j k:ℕ,i+j+k≤J →
       ‖iteratedDeriv i (fun y=>iteratedDeriv j (fun r=>iteratedDeriv k
         (fun v=>largeVarianceError r v.toNNReal y) V) m) x‖≤
           CJ*V^CJ*Real.exp (-(ε^2/2)*V):=by
   classical
   let A:=Fin (J+1)×Fin (J+1)×Fin (J+1)
   have hf:∀a:A,∃C:ℝ,0<C ∧ ∃d:ℕ,∀m∈Icc ε 1,∀V≥1,∀x,
       ‖iteratedDeriv a.1.val (fun y=>iteratedDeriv a.2.1.val (fun r=>iteratedDeriv a.2.2.val
         (fun v=>largeVarianceError r v.toNNReal y) V) m) x‖≤
           C*V^d*Real.exp (-(ε^2)*V/2):=
     fun a=>largeVarianceError_source_mixed_exponential_bound a.1.val a.2.1.val a.2.2.val hε
   choose C hC d hb using hf
   let CT:ℝ:=1+∑a:A,C a
   let D:ℕ:=∑a:A,d a
   let CJ:ℝ:=max CT D
   have hs:0≤∑a:A,C a:=Finset.sum_nonneg (fun a _=>(hC a).le)
   have hCT:0<CT:=by dsimp only [CT];linarith
   have hCJ:0<CJ:=hCT.trans_le (le_max_left _ _)
   refine ⟨CJ,hCJ,?_⟩
   intro m hm V hV x i j k hijk
   have hi:i<J+1:=by omega
   have hj:j<J+1:=by omega
   have hk:k<J+1:=by omega
   let a:A:=(⟨i,hi⟩,⟨j,hj⟩,⟨k,hk⟩)
   have hCa:C a≤CJ:=by
     have hh:C a≤∑a:A,C a:=Finset.single_le_sum (fun b _=>(hC b).le) (Finset.mem_univ a)
     exact (hh.trans (by dsimp only [CT];linarith)).trans (le_max_left _ _)
   have hd:d a≤D:=Finset.single_le_sum (fun b _=>Nat.zero_le _) (Finset.mem_univ a)
   have hdreal:(d a:ℝ)≤(D:ℝ):=by exact_mod_cast hd
   have hdCJ:(d a:ℝ)≤CJ:=hdreal.trans (le_max_right _ _)
   have hp:V^(d a)≤V^CJ:=by
     rw [←Real.rpow_natCast]
     exact Real.rpow_le_rpow_of_exponent_le hV hdCJ
   have hbd:=hb a m hm V hV x
   change ‖iteratedDeriv i (fun y=>iteratedDeriv j (fun r=>iteratedDeriv k
     (fun v=>largeVarianceError r v.toNNReal y) V) m) x‖≤C a*V^(d a)*Real.exp (-(ε^2)*V/2) at hbd
   have hmulp:C a*V^(d a)≤CJ*V^CJ:=mul_le_mul hCa hp (by positivity) hCJ.le
   have he:-(ε^2)*V/2=-(ε^2/2)*V:=by ring
   exact hbd.trans (mul_le_mul_of_nonneg_right hmulp (Real.exp_pos _).le |>.trans_eq (by rw [he]))

 theorem large_variance (I:Set ℝ) (hI:IsCompact I) (hsub:I⊆Ioc (0:ℝ) 1):
     ∃Vbar c:ℝ,1≤Vbar ∧ 0<c ∧
       (∀m∈I,∀V:ℝ≥0,∀x:ℝ,
         ColeHopfFoundation.ProbabilityTheory.coleHopf m V (fun y=>Real.log (Real.cosh y)) x=
           m*(V:ℝ)/2+(1/m-1)*Real.log 2+(1/m)*Real.log (Real.cosh (m*x))+
             largeVarianceError m V x) ∧
       ∀J:ℕ,∃CJ:ℝ,0<CJ ∧ ∀m∈I,∀V:ℝ,Vbar≤V →∀x:ℝ,∀i j k:ℕ,i+j+k≤J →
         ‖iteratedDeriv i (fun y=>iteratedDeriv j (fun r=>iteratedDeriv k
           (fun v=>largeVarianceError r v.toNNReal y) V) m) x‖≤CJ*V^CJ*Real.exp (-c*V):=by
   by_cases hne:I.Nonempty
   · obtain ⟨ε,hεI,hεmin⟩:=hI.exists_isMinOn hne continuousOn_id
     have hε:0<ε:=(hsub hεI).1
     refine ⟨1,ε^2/2,le_rfl,by positivity,?_,?_⟩
     · intro m hm V x
       exact coleHopf_largeVariance_expansion m V x
     · intro J
       obtain ⟨CJ,hCJ,hbound⟩:=largeVarianceError_uniform_order hε J
       refine ⟨CJ,hCJ,?_⟩
       intro m hm V hV x i j k hijk
       exact hbound m ⟨hεmin hm,(hsub hm).2⟩ V hV x i j k hijk
   · refine ⟨1,1,le_rfl,by norm_num,?_,?_⟩
     · intro m hm
       exact (hne ⟨m,hm⟩).elim
     · intro J
       refine ⟨1,by norm_num,?_⟩
       intro m hm
       exact (hne ⟨m,hm⟩).elim

end GeneralDepthPaper
