module

public import DepthPaper.AtomicMeasureTopology
public import DepthPaper.RevisedSecondDerivativeComparison

@[expose] public section

/-! Actual second derivatives of finite atomic contact integrals along a
coordinate line. These are independent of the covariance representation. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace DepthPaper
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 64

def atomicMassVelocity {r : ℕ} (v : AtomicPoint r) : Fin (r+1) → ℝ :=
  Fin.lastCases (-∑i, v.2 i) v.2

theorem atomicLocation_affine_line {r : ℕ} (z v : AtomicPoint r) (t : ℝ)
    (i : Fin (r+1)) : atomicLocation (z+t • v) i=atomicLocation z i+t*atomicLocation v i := by
  cases i using Fin.cases with
  | zero => simp
  | succ j => simp [atomicLocation_succ]

theorem atomicWeight_affine_line {r : ℕ} (z v : AtomicPoint r) (t : ℝ)
    (i : Fin (r+1)) : atomicWeight (z+t • v) i=atomicWeight z i+t*atomicMassVelocity v i := by
  classical
  cases i using Fin.lastCases with
  | last =>
    simp only [atomicWeight_last,atomicMassVelocity,Fin.lastCases_last]
    change 1-(∑i : Fin r,(z.2 i+t*v.2 i))=(1-∑i : Fin r,z.2 i)+t*(-∑i : Fin r,v.2 i)
    rw [Finset.sum_add_distrib,←Finset.mul_sum]
    ring
  | cast j => simp [atomicWeight_castSucc,atomicMassVelocity]

theorem hasDerivAt_deriv_affine_weighted_contact {f : ℝ → ℝ} {q w dw dq : ℝ}
    (hf : ContDiffAt ℝ 2 f q) (hprime : deriv f q=0) :
    HasDerivAt (deriv (fun t : ℝ => (w+t*dw)*f (q+t*dq)))
      (w*deriv (deriv f) q*dq^2) 0 := by
  have harg (t : ℝ) : HasDerivAt (fun s : ℝ => q+s*dq) dq t := by
    simpa only [id_eq,one_mul] using ((hasDerivAt_id t).mul_const dq).const_add q
  have hw (t : ℝ) : HasDerivAt (fun s : ℝ => w+s*dw) dw t := by
    simpa only [id_eq,one_mul] using ((hasDerivAt_id t).mul_const dw).const_add w
  have hf0 : HasDerivAt (fun t : ℝ => f (q+t*dq)) 0 0 := by
    have hbase : HasDerivAt f 0 (q+(0 : ℝ)*dq) := by
      simpa only [zero_mul,add_zero,hprime] using (hf.differentiableAt (by norm_num)).hasDerivAt
    simpa only [zero_mul,Function.comp_def] using hbase.comp (0 : ℝ) (harg 0)
  have hfd : HasDerivAt (fun t : ℝ => deriv f (q+t*dq))
      (deriv (deriv f) q*dq) 0 := by
    have hbase : HasDerivAt (deriv f) (deriv (deriv f) q) (q+(0 : ℝ)*dq) := by
      simpa using ((hf.derivWithin (m:=1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
    simpa only [Function.comp_def] using hbase.comp (0 : ℝ) (harg 0)
  let D : ℝ → ℝ := fun t => dw*f (q+t*dq)+(w+t*dw)*deriv f (q+t*dq)*dq
  have hD : HasDerivAt D (w*deriv (deriv f) q*dq^2) 0 := by
    have hd := (hf0.const_mul dw).add (((hw 0).mul hfd).mul_const dq)
    convert hd using 1
    simp only [zero_mul,add_zero,hprime,mul_zero,zero_add]
    ring
  have he : deriv (fun t : ℝ => (w+t*dw)*f (q+t*dq)) =ᶠ[𝓝 (0 : ℝ)] D := by
    have hnear := (hf.eventually (by norm_num : (2 : ℕ∞ω)≠∞))
    have htend : Tendsto (fun t : ℝ => q+t*dq) (𝓝 0) (𝓝 q) := by
      simpa using (harg 0).continuousAt.tendsto
    filter_upwards [htend.eventually hnear] with t ht
    have hb := (ht.differentiableAt (by norm_num)).hasDerivAt.comp t (harg t)
    have hd := ((hw t).mul hb).deriv
    have hfun : ((fun s : ℝ => w+s*dw) * (f ∘ fun s : ℝ => q+s*dq)) =
        (fun s : ℝ => (w+s*dw)*f (q+s*dq)) := by funext s; rfl
    rw [hfun] at hd
    simpa only [D,Function.comp_def,mul_assoc] using hd
  exact hD.congr_of_eventuallyEq he

def atomicContactIntegralLine {r : ℕ} (f : ℝ → ℝ) (z v : AtomicPoint r) (t : ℝ) : ℝ :=
  ∑i : Fin r, atomicWeight (z+t • v) i.succ*f ((z+t • v).1 i)

theorem contDiffAt_atomicContactIntegralLine {r : ℕ} (f : ℝ → ℝ)
    (z v : AtomicPoint r) (hf : ∀i : Fin r,ContDiffAt ℝ 2 f (z.1 i)) :
    ContDiffAt ℝ 2 (atomicContactIntegralLine f z v) 0 := by
  have he : atomicContactIntegralLine f z v = fun t => ∑i : Fin r,
      (atomicWeight z i.succ+t*atomicMassVelocity v i.succ)*f (z.1 i+t*v.1 i) := by
    funext t
    apply Finset.sum_congr rfl
    intro i _
    rw [atomicWeight_affine_line]
    rfl
  rw [he]
  apply ContDiffAt.sum
  intro i _
  apply (contDiffAt_const.add (contDiffAt_id.mul contDiffAt_const)).mul
  have ht : ContDiffAt ℝ 2 (fun t : ℝ => z.1 i+t*v.1 i) 0 :=
    contDiffAt_const.add (contDiffAt_id.mul contDiffAt_const)
  have hb : ContDiffAt ℝ 2 f (z.1 i+(0 : ℝ)*v.1 i) := by simpa using hf i
  exact hb.comp (0 : ℝ) ht

theorem hasDerivAt_deriv_atomicContactIntegralLine {r : ℕ} (f : ℝ → ℝ)
    (z v : AtomicPoint r) (hf : ∀i : Fin r,ContDiffAt ℝ 2 f (z.1 i))
    (hprime : ∀i : Fin r,deriv f (z.1 i)=0) :
    HasDerivAt (deriv (atomicContactIntegralLine f z v))
      (∑i : Fin r,atomicWeight z i.succ*deriv (deriv f) (z.1 i)*(v.1 i)^2) 0 := by
  let F : Fin r → ℝ → ℝ := fun i t =>
    (atomicWeight z i.succ+t*atomicMassVelocity v i.succ)*f (z.1 i+t*v.1 i)
  have hF (i : Fin r) : ContDiffAt ℝ 2 (F i) 0 := by
    apply (contDiffAt_const.add (contDiffAt_id.mul contDiffAt_const)).mul
    have ht : ContDiffAt ℝ 2 (fun t : ℝ => z.1 i+t*v.1 i) 0 :=
      contDiffAt_const.add (contDiffAt_id.mul contDiffAt_const)
    have hb : ContDiffAt ℝ 2 f (z.1 i+(0 : ℝ)*v.1 i) := by simpa using hf i
    exact hb.comp (0 : ℝ) ht
  have he : atomicContactIntegralLine f z v=fun t => ∑i : Fin r,F i t := by
    funext t
    apply Finset.sum_congr rfl
    intro i _
    simp only [atomicContactIntegralLine,F,atomicWeight_affine_line]
    rfl
  have hderiv : deriv (fun t => ∑i : Fin r,F i t) =ᶠ[𝓝 (0 : ℝ)] fun t => ∑i : Fin r,deriv (F i) t := by
    have hh : ∀ᶠ t in 𝓝 (0 : ℝ), ∀i : Fin r,DifferentiableAt ℝ (F i) t := by
      apply eventually_all.mpr
      intro i
      exact ((hF i).eventually (by norm_num)).mono fun t ht => ht.differentiableAt (by norm_num)
    filter_upwards [hh] with t ht
    exact (HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (ht i).hasDerivAt).deriv
  rw [he]
  have hd : HasDerivAt (fun t => ∑i : Fin r,deriv (F i) t)
      (∑i : Fin r,atomicWeight z i.succ*deriv (deriv f) (z.1 i)*(v.1 i)^2) 0 :=
    HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      hasDerivAt_deriv_affine_weighted_contact (hf i) (hprime i)
  exact hd.congr_of_eventuallyEq hderiv

theorem integral_atomicMeasure_affine_contact_line {r : ℕ} (f : ℝ → ℝ)
    (z v : AtomicPoint r) (t : ℝ) (ht : IsAtomicPoint (z+t • v)) (hzero : f 0=0) :
    (∫q : Paper.Overlap,f q ∂(atomicMeasure (z+t • v) ht : Measure Paper.Overlap))=
      atomicContactIntegralLine f z v t := by
  rw [integral_atomicMeasure,Fin.sum_univ_succ]
  simp only [atomicOverlap,atomicLocation_zero,hzero,mul_zero,zero_add,atomicLocation_succ]
  rfl

end DepthPaper
