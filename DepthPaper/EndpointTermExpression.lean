module

public import DepthPaper.HighDegreeCorrection
public import DepthPaper.EndpointCurvatureJets

@[expose] public section


/-! The actual endpoint correction E in Lemma 4.4, extended polynomially
in the mass and coupling parameter. No endpoint-root equation is assumed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace DepthPaper
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 64

def endpointBaseIntegral (Ξ : AdmissibleCovariance) (Q : ℝ) : ℝ :=
  Ξ.value 1-Ξ.value Q-(1-Q)*Ξ.first Q

def endpointPowerIntegral (p : ℕ) (Q : ℝ) : ℝ :=
  1+(p-1:ℕ)*Q^p-(p:ℝ)*Q^(p-1)

def endpointIntegralExpression (Ξ : AdmissibleCovariance) (p : ℕ)
    (w : ℝ×ℝ) : ℝ := endpointBaseIntegral Ξ w.2+w.1*endpointPowerIntegral p w.2

def endpointTermExpression (Ξ : AdmissibleCovariance) {r : ℕ} (p : ℕ)
    (x : CutoffInputParameter r) : ℝ :=
  (1-x.2.1)/2*endpointIntegralExpression Ξ p x.2.2

theorem endpointBaseIntegral_eq_integral (Ξ : AdmissibleCovariance) (Q : ℝ) :
    endpointBaseIntegral Ξ Q=∫q in Q..1,(1-q)*Ξ.second q := by
  rw [integral_endpoint_weight_covariance]
  unfold endpointBaseIntegral covarianceCorrectionPrimitive
  ring

theorem endpointPowerIntegral_eq_integral (p : ℕ) (hp : 2 ≤ p) (Q : ℝ) :
    endpointPowerIntegral p Q=∫q in Q..1,(1-q)*(p:ℝ)*(p-1:ℕ)*q^(p-2) := by
  have hd (q:ℝ) : HasDerivAt
      (fun q:ℝ=>(p:ℝ)*q^(p-1)-(p-1:ℕ)*q^p)
      ((1-q)*(p:ℝ)*(p-1:ℕ)*q^(p-2)) q := by
    have hpow : q*q^(p-2)=q^(p-1) := by
      rw [←pow_succ',show p-2+1=p-1 by omega]
    convert ((hasDerivAt_pow (p-1) q).const_mul (p:ℝ)).sub
      ((hasDerivAt_pow p q).const_mul ((p-1:ℕ):ℝ)) using 1
    simp only [show p-1-1=p-2 by omega]
    rw [←hpow]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun q _=>hd q)
    ((by fun_prop : Continuous (fun q:ℝ=>(1-q)*(p:ℝ)*(p-1:ℕ)*q^(p-2))).intervalIntegrable _ _)]
  simp only [one_pow,mul_one,endpointPowerIntegral]
  have hc : ((p-1:ℕ):ℝ)=(p:ℝ)-1 := by rw [Nat.cast_sub (by omega)];norm_num
  rw [hc]
  ring

theorem endpointIntegralExpression_eq_integral (Ξ : AdmissibleCovariance)
    (p : ℕ) (hp : 4 ≤ p) (he : Even p) (hn : p∉Ξ.degrees)
    (lam : ℝ) (hlam : 0<lam) (Q : ℝ) :
    endpointIntegralExpression Ξ p (lam,Q)=
      ∫q in Q..1,(1-q)*(Ξ.addHighDegree p hp he hn lam hlam).second q := by
  unfold endpointIntegralExpression
  rw [endpointBaseIntegral_eq_integral,endpointPowerIntegral_eq_integral p (by omega)]
  have hbase : IntervalIntegrable (fun q=>(1-q)*Ξ.second q) volume Q 1 :=
    ((continuous_const.sub continuous_id).mul Ξ.continuous_second).intervalIntegrable _ _
  have hpow : IntervalIntegrable (fun q:ℝ=>(1-q)*(p:ℝ)*(p-1:ℕ)*q^(p-2)) volume Q 1 :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  rw [←intervalIntegral.integral_const_mul,←intervalIntegral.integral_add hbase (hpow.const_mul lam)]
  apply intervalIntegral.integral_congr
  intro q hq
  dsimp only
  rw [Ξ.addHighDegree_second]
  ring

theorem endpointTermExpression_eq_integral (Ξ : AdmissibleCovariance)
    {r : ℕ} (p : ℕ) (hp : 4 ≤ p) (he : Even p) (hn : p∉Ξ.degrees)
    (z : AtomicPoint r) (m lam Q : ℝ) (hlam : 0<lam) :
    endpointTermExpression Ξ p (z,(m,(lam,Q)))=
      (1-m)/2*(∫q in Q..1,(1-q)*(Ξ.addHighDegree p hp he hn lam hlam).second q) := by
  unfold endpointTermExpression
  rw [endpointIntegralExpression_eq_integral Ξ p hp he hn lam hlam]

theorem contDiff_endpointBaseIntegral (Ξ : AdmissibleCovariance) :
    ContDiff ℝ ∞ (endpointBaseIntegral Ξ) :=
  (contDiff_const.sub Ξ.contDiff_value).sub
    ((contDiff_const.sub contDiff_id).mul Ξ.contDiff_first)

theorem contDiff_endpointPowerIntegral (p : ℕ) :
    ContDiff ℝ ∞ (endpointPowerIntegral p) := by unfold endpointPowerIntegral;fun_prop

theorem contDiff_endpointIntegralExpression (Ξ : AdmissibleCovariance) (p : ℕ) :
    ContDiff ℝ ∞ (endpointIntegralExpression Ξ p) :=
  ((contDiff_endpointBaseIntegral Ξ).comp contDiff_snd).add
    (contDiff_fst.mul ((contDiff_endpointPowerIntegral p).comp contDiff_snd))

theorem contDiff_endpointTermExpression (Ξ : AdmissibleCovariance) {r : ℕ} (p : ℕ) :
    ContDiff ℝ ∞ (endpointTermExpression (r:=r) Ξ p) := by
  exact (show ContDiff ℝ ∞ (fun x:CutoffInputParameter r=>(1-x.2.1)/2) by fun_prop).mul
    ((contDiff_endpointIntegralExpression Ξ p).comp (by fun_prop))

theorem hasDerivAt_endpointBaseIntegral (Ξ : AdmissibleCovariance) (Q : ℝ) :
    HasDerivAt (endpointBaseIntegral Ξ) (-(1-Q)*Ξ.second Q) Q := by
  convert ((Ξ.hasDerivAt_value Q).const_sub (Ξ.value 1)).sub
    (((hasDerivAt_id Q).const_sub 1).mul (Ξ.hasDerivAt_first Q)) using 1
  · rfl
  · dsimp only [id_eq]
    ring

theorem hasDerivAt_endpointPowerIntegral (p : ℕ) (hp : 2 ≤ p) (Q : ℝ) :
    HasDerivAt (endpointPowerIntegral p) (-(1-Q)*(p:ℝ)*(p-1:ℕ)*Q^(p-2)) Q := by
  have hpow : Q*Q^(p-2)=Q^(p-1) := by rw [←pow_succ',show p-2+1=p-1 by omega]
  convert (((hasDerivAt_pow p Q).const_mul ((p-1:ℕ):ℝ)).const_add 1).sub
    ((hasDerivAt_pow (p-1) Q).const_mul (p:ℝ)) using 1
  · rfl
  · simp only [show p-1-1=p-2 by omega]
    rw [←hpow]
    ring

theorem hasDerivAt_endpointTermExpression_endpoint (Ξ : AdmissibleCovariance)
    {r : ℕ} (p : ℕ) (hp : 2 ≤ p) (z : AtomicPoint r) (m lam Q : ℝ) :
    HasDerivAt (fun q=>endpointTermExpression Ξ p (z,(m,(lam,q))))
      (-(1-m)/2*(1-Q)*highDegreeSecondExpression Ξ p (lam,Q)) Q := by
  convert ((hasDerivAt_endpointBaseIntegral Ξ Q).add
    ((hasDerivAt_endpointPowerIntegral p hp Q).const_mul lam)).const_mul ((1-m)/2) using 1
  · rfl
  · unfold highDegreeSecondExpression
    ring

end DepthPaper
