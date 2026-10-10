module

public import GeneralDepthPaper.HighDegreeRegularity
public import GeneralDepthPaper.LargeVarianceMassDecay

@[expose] public section


/-! The literal exponentially thin endpoint strip and actual top variance.
The variance differs from λp by a bound independent of p and every point
of the strip; no root equation is assumed. -/
noncomputable section
open Set Filter
open scoped Topology
namespace GeneralDepthPaper
set_option maxHeartbeats 800000

def endpointStrip (cQ CQ : ℝ) (p : ℕ) : Set ℝ :=
  Icc (1-Real.exp (-cQ*(p:ℝ))) (1-Real.exp (-CQ*(p:ℝ)))

def endpointVarianceExpression (Ξ : AdmissibleCovariance) (p : ℕ) (qc : ℝ)
    (w : ℝ×ℝ) : ℝ :=
  Ξ.first w.2-Ξ.first qc+w.1*(p:ℝ)*(w.2^(p-1)-qc^(p-1))

def endpointVariance (Ξ : AdmissibleCovariance) (p : ℕ) (hp : 4≤p)
    (he : Even p) (hn : p∉Ξ.degrees) (lam : ℝ) (hlam : 0 < lam) (qc Q : ℝ) : ℝ :=
  (Ξ.addHighDegree p hp he hn lam hlam).first Q-
    (Ξ.addHighDegree p hp he hn lam hlam).first qc

theorem endpointVariance_eq_expression (Ξ : AdmissibleCovariance) (p : ℕ) (hp : 4≤p)
    (he : Even p) (hn : p∉Ξ.degrees) (lam : ℝ) (hlam : 0 < lam) (qc Q : ℝ) :
    endpointVariance Ξ p hp he hn lam hlam qc Q=endpointVarianceExpression Ξ p qc (lam,Q) := by
  simp only [endpointVariance,Ξ.addHighDegree_first,endpointVarianceExpression]
  ring

theorem endpointStrip_mem_unit {cQ CQ : ℝ} (hc : 0 < cQ) (p : ℕ)
    {Q : ℝ} (hQ : Q∈endpointStrip cQ CQ p) : Q∈Ico (0:ℝ) 1 := by
  constructor
  · have he : Real.exp (-cQ*(p:ℝ))≤1:=Real.exp_le_one_iff.mpr
      (by nlinarith [mul_nonneg hc.le (Nat.cast_nonneg p)])
    exact (sub_nonneg.mpr he).trans hQ.1
  · exact hQ.2.trans_lt (sub_lt_self 1 (Real.exp_pos _))

theorem endpointStrip_distance_bound {cQ CQ : ℝ} (p : ℕ)
    {Q : ℝ} (hQ : Q∈endpointStrip cQ CQ p) :
    1-Q≤Real.exp (-cQ*(p:ℝ)) := by linarith [hQ.1]

theorem one_sub_pow_bound {x : ℝ} (hx : x∈Icc (0:ℝ) 1) (n : ℕ) :
    1-x^n≤(n:ℝ)*(1-x) := by
  induction n with
  | zero=>simp
  | succ n ih=>
    have hp : 0≤1-x^n:=sub_nonneg.mpr (pow_le_one₀ hx.1 hx.2)
    have hm := mul_le_mul_of_nonneg_right hx.2 hp
    rw [pow_succ]
    norm_num only [Nat.cast_succ] at *
    nlinarith

theorem nat_mul_pow_sub_one_bound {qc : ℝ} (hc : qc∈Ioo (0:ℝ) 1) (p : ℕ) (hp : 1≤p) :
    (p:ℝ)*qc^(p-1)≤Real.exp (-Real.log qc)/(-Real.log qc) := by
  have hε : 0 < -Real.log qc:=neg_pos.mpr (Real.log_neg hc.1 hc.2)
  have h:=polynomial_times_exp_bound 1 (ε := -Real.log qc) (c := 1)
    (u := ((p-1:ℕ):ℝ)) hε (by norm_num) (Nat.cast_nonneg _)
  have hnat : 1+((p-1:ℕ):ℝ)=(p:ℝ) := by
    norm_cast
    omega
  have he : Real.exp (-(-Real.log qc)*((p-1:ℕ):ℝ))=qc^(p-1) := by
    rw [neg_neg,mul_comm,Real.exp_nat_mul,Real.exp_log hc.1]
  simp only [pow_one,Nat.factorial_one,Nat.cast_one,mul_one,hnat,he] at h
  exact h.trans_eq (by ring)

def endpointVarianceErrorBound (Ξ : AdmissibleCovariance) (qc cQ L : ℝ) : ℝ :=
  2*Ξ.first 1+L*(2/cQ^2+Real.exp (-Real.log qc)/(-Real.log qc))

theorem endpointVarianceExpression_sub_linear_bound (Ξ : AdmissibleCovariance)
    {qc cQ CQ L : ℝ} (hc : qc∈Ioo (0:ℝ) 1) (hcQ : 0 < cQ) (hL : 0≤L)
    (p : ℕ) (hp : 1≤p) {lam Q : ℝ} (hlam : lam∈Icc (0:ℝ) L)
    (hQ : Q∈endpointStrip cQ CQ p) :
    |endpointVarianceExpression Ξ p qc (lam,Q)-lam*(p:ℝ)|≤
      endpointVarianceErrorBound Ξ qc cQ L := by
  have hQu : Q∈Icc (0:ℝ) 1:=⟨(endpointStrip_mem_unit hcQ p hQ).1,
    (endpointStrip_mem_unit hcQ p hQ).2.le⟩
  have hfirst : |Ξ.first Q-Ξ.first qc|≤2*Ξ.first 1 := by
    have hQf : |Ξ.first Q|≤Ξ.first 1 := by
      rw [abs_of_nonneg (Ξ.first_nonneg hQu.1)]
      exact Ξ.first_strictMonoOn.monotoneOn hQu.1 (show (1:ℝ)∈Ici 0 by norm_num) hQu.2
    have hcf : |Ξ.first qc|≤Ξ.first 1 := by
      rw [abs_of_nonneg (Ξ.first_nonneg hc.1.le)]
      exact Ξ.first_strictMonoOn.monotoneOn hc.1.le (show (1:ℝ)∈Ici 0 by norm_num) hc.2.le
    exact (abs_sub _ _).trans (by linarith)
  have hg : 1-Q^(p-1)≤(p:ℝ)*Real.exp (-cQ*(p:ℝ)) := by
    have hn : ((p-1:ℕ):ℝ)≤(p:ℝ):=by exact_mod_cast Nat.sub_le p 1
    exact (one_sub_pow_bound hQu (p-1)).trans
      ((mul_le_mul hn (endpointStrip_distance_bound p hQ)
        (sub_nonneg.mpr hQu.2) (Nat.cast_nonneg p)))
  have hbexp := polynomial_times_exp_bound 2 (ε := cQ) (c := 0) (u := (p:ℝ))
    hcQ le_rfl (Nat.cast_nonneg p)
  norm_num only [zero_add,mul_zero,Real.exp_zero,mul_one,Nat.factorial] at hbexp
  have hpow : (p:ℝ)*qc^(p-1)≤Real.exp (-Real.log qc)/(-Real.log qc):=
    nat_mul_pow_sub_one_bound hc p hp
  have he : endpointVarianceExpression Ξ p qc (lam,Q)-lam*(p:ℝ)=
      (Ξ.first Q-Ξ.first qc)-lam*(p:ℝ)*(1-Q^(p-1))-lam*(p:ℝ)*qc^(p-1) := by
    dsimp only [endpointVarianceExpression]
    ring
  rw [he]
  apply (abs_sub _ _).trans
  apply (add_le_add (abs_sub _ _) (le_refl _)).trans
  have hgap0 : 0≤1-Q^(p-1):=sub_nonneg.mpr (pow_le_one₀ hQu.1 hQu.2)
  simp only [abs_mul,abs_of_nonneg hlam.1,
    abs_of_nonneg hgap0,abs_of_nonneg (pow_nonneg hc.1.le (p-1))]
  simp only [abs_of_nonneg (show 0≤(p:ℝ) from Nat.cast_nonneg p)]
  have h1 := mul_le_mul_of_nonneg_left hg (mul_nonneg hlam.1 (Nat.cast_nonneg p))
  have h2 := mul_le_mul_of_nonneg_left hbexp hlam.1
  have h3 := mul_le_mul_of_nonneg_left hpow hlam.1
  have h4 := mul_le_mul_of_nonneg_right hlam.2
    (show 0≤2/cQ^2+Real.exp (-Real.log qc)/(-Real.log qc) by
      have hl : 0 < -Real.log qc:=neg_pos.mpr (Real.log_neg hc.1 hc.2)
      positivity)
  dsimp only [endpointVarianceErrorBound]
  nlinarith [hfirst]

end GeneralDepthPaper
