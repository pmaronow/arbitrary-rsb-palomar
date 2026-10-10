module

public import DepthPaper.CoshPowerEndpointFactor
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.Topology.Algebra.Polynomial

@[expose] public section


/-! Joint smoothness and actual mass derivatives of a bivariate polynomial.
The finite coefficient formula is used to obtain genuine compact bounds for
the endpoint quotient in the large-variance residual argument. -/
noncomputable section
open Set
open scoped Polynomial ContDiff
namespace DepthPaper

 def bivariateValue (P:Polynomial (Polynomial ℝ)) (m t:ℝ):ℝ :=
   (P.map (Polynomial.evalRingHom m)).eval t

 def bivariateMassJet (P:Polynomial (Polynomial ℝ)) (j:ℕ) (m t:ℝ):ℝ :=
   P.sum (fun n q=>(Polynomial.derivative^[j] q).eval m*t^n)

 theorem bivariateValue_sum (P:Polynomial (Polynomial ℝ)) (m t:ℝ):
     bivariateValue P m t=P.sum (fun n q=>q.eval m*t^n):=by
   simp only [bivariateValue,Polynomial.eval_map,Polynomial.eval₂_eq_sum]
   rfl

 theorem hasDerivAt_bivariateMassJet (P:Polynomial (Polynomial ℝ)) (j:ℕ) (m t:ℝ):
     HasDerivAt (fun r=>bivariateMassJet P j r t) (bivariateMassJet P (j+1) m t) m:=by
   unfold bivariateMassJet
   simp only [Polynomial.sum_def]
   have hh:=HasDerivAt.sum (u:=P.support) (fun n _=>
     ((Polynomial.derivative^[j] (P.coeff n)).hasDerivAt m).mul_const (t^n))
   convert hh using 1
   · funext r
     simp only [Finset.sum_apply]
   · apply Finset.sum_congr rfl
     intro n hn
     rw [Function.iterate_succ_apply']

 theorem iteratedDeriv_bivariateValue_mass (P:Polynomial (Polynomial ℝ)) (j:ℕ) (m t:ℝ):
     iteratedDeriv j (fun r=>bivariateValue P r t) m=bivariateMassJet P j m t:=by
   induction j generalizing m with
   | zero=>simp only [iteratedDeriv_zero,bivariateValue_sum,bivariateMassJet,Function.iterate_zero,Function.id_def]
   | succ j ih=>
     rw [iteratedDeriv_succ]
     have he:iteratedDeriv j (fun r=>bivariateValue P r t)=fun r=>bivariateMassJet P j r t:=funext ih
     rw [he]
     exact (hasDerivAt_bivariateMassJet P j m t).deriv

 theorem contDiff_bivariateMassJet (P:Polynomial (Polynomial ℝ)) (j:ℕ):
     ContDiff ℝ ∞ (fun p:ℝ×ℝ=>bivariateMassJet P j p.1 p.2):=by
   unfold bivariateMassJet
   simp only [Polynomial.sum_def]
   apply ContDiff.sum
   intro n hn
   have hc:ContDiff ℝ ∞ (fun r:ℝ=>(Polynomial.derivative^[j] (P.coeff n)).eval r):=by
     convert Polynomial.contDiff_aeval (R:=ℝ) (𝕜:=ℝ) (Polynomial.derivative^[j] (P.coeff n)) ∞ using 1
     funext r
     simp [Polynomial.aeval_def,Polynomial.eval₂_at_apply]
   exact (hc.comp contDiff_fst).mul (contDiff_snd.pow n)

 theorem bivariateMassJet_uniform_bound (P:Polynomial (Polynomial ℝ)) (j:ℕ) (a b:ℝ):
     ∃K:ℝ,0≤K ∧ ∀m∈Icc a b,∀t∈Icc (-1:ℝ) 1,‖bivariateMassJet P j m t‖≤K:=by
   obtain ⟨K,hK⟩:=(isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
     (contDiff_bivariateMassJet P j).continuous.continuousOn
   refine ⟨max K 0,le_max_right _ _,?_⟩
   intro m hm t ht
   exact (hK (m,t) ⟨hm,ht⟩).trans (le_max_left _ _)

end DepthPaper
