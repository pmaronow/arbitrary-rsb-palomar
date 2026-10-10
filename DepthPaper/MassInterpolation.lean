module

public import DepthPaper.EndpointMixedJetBounds
public import DepthPaper.CutoffInputJetCalculus
public import Mathlib.Topology.Order.ProjIcc

@[expose] public section


/-! Affine interpolation towards mass one. It preserves the actual open
cutoff domain and contracts every parameter direction on the unit interval. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

def massInterpolation {r : ℕ} (t : ℝ) (x : CutoffInputParameter r) :
    CutoffInputParameter r := (x.1,(1-(1-x.2.1)*t,x.2.2))

def massInterpolationLinear {r : ℕ} (t : ℝ) :
    CutoffInputParameter r→L[ℝ]CutoffInputParameter r :=
  ContinuousLinearMap.id ℝ _+(t-1) •
    ((ContinuousLinearMap.inr ℝ (AtomicPoint r) (ℝ×(ℝ×ℝ))).comp
      ((ContinuousLinearMap.inl ℝ ℝ (ℝ×ℝ)).comp
        ((ContinuousLinearMap.fst ℝ ℝ (ℝ×ℝ)).comp
          (ContinuousLinearMap.snd ℝ (AtomicPoint r) (ℝ×(ℝ×ℝ))))))

theorem massInterpolationLinear_apply {r : ℕ} (t : ℝ) (x : CutoffInputParameter r) :
    massInterpolationLinear t x=(x.1,(t*x.2.1,x.2.2)) := by
  ext <;> simp [massInterpolationLinear] <;> ring

theorem continuous_massInterpolationLinear {r : ℕ} :
    Continuous (massInterpolationLinear (r:=r)) := by
  unfold massInterpolationLinear
  fun_prop

theorem massInterpolation_eq_affine {r : ℕ} (t : ℝ) (x : CutoffInputParameter r) :
    massInterpolation t x=(1-t) • lowerMassDirection+massInterpolationLinear t x := by
  rw [massInterpolationLinear_apply]
  ext <;> simp [massInterpolation,lowerMassDirection] <;> ring

theorem norm_massInterpolationLinear_le {r : ℕ} {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    ‖massInterpolationLinear (r:=r) t‖ ≤ 1 := by
  apply (massInterpolationLinear (r:=r) t).opNorm_le_bound zero_le_one
  intro x
  rw [massInterpolationLinear_apply,one_mul]
  have hm : ‖t*x.2.1‖ ≤ ‖x.2.1‖ := by
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)).trans_eq (one_mul _)
  simp only [Prod.norm_def]
  exact max_le_max le_rfl (max_le_max hm le_rfl)

theorem contDiff_massInterpolation {r : ℕ} :
    ContDiff ℝ ∞ (fun p : ℝ×CutoffInputParameter r=> massInterpolation p.1 p.2) := by
  unfold massInterpolation
  fun_prop

theorem massInterpolation_mem_smoothDomain (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (qc : ℝ) {x : CutoffInputParameter r}
    (hx : x∈cutoffInputSmoothDomain Ξ p qc) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    massInterpolation t x∈cutoffInputSmoothDomain Ξ p qc := by
  have hm0 : 0 < 1-(1-x.2.1)*t := by
    rcases ht.1.eq_or_lt with h|h
    · simp [←h]
    · nlinarith [ht.2,mul_pos h hx.1.1]
  have hm2 : 1-(1-x.2.1)*t < 2 := by
    rcases ht.1.eq_or_lt with h|h
    · norm_num [←h]
    · nlinarith [ht.2,mul_pos h (sub_pos.mpr hx.1.2)]
  exact ⟨⟨hm0,hm2⟩,hx.2.1,hx.2.2.1,hx.2.2.2⟩

theorem iteratedFDeriv_comp_massInterpolation {r : ℕ} {f : CutoffInputParameter r→ℝ}
    (t : ℝ) {x : CutoffInputParameter r}
    (hf : ContDiffAt ℝ ∞ f (massInterpolation t x)) (j : ℕ) :
    iteratedFDeriv ℝ j (fun y=> f (massInterpolation t y)) x=
      (iteratedFDeriv ℝ j f (massInterpolation t x)).compContinuousLinearMap
        (fun _=> massInterpolationLinear t) := by
  have hfa' : ContDiffAt ℝ ∞ (fun y=> f ((1-t) • lowerMassDirection+y))
      (massInterpolationLinear t x) := by
    rw [massInterpolation_eq_affine] at hf
    exact hf.comp _ (contDiffAt_const.add contDiffAt_id)
  simp_rw [massInterpolation_eq_affine]
  change iteratedFDeriv ℝ j ((fun y=> f ((1-t) • lowerMassDirection+y)) ∘
    (massInterpolationLinear t)) x=_
  rw [iteratedFDeriv_comp_CLM_local (massInterpolationLinear t) hfa' j,
    iteratedFDeriv_comp_add_left]

theorem norm_iteratedFDeriv_comp_massInterpolation_le {r : ℕ} {f : CutoffInputParameter r→ℝ}
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) {x : CutoffInputParameter r}
    (hf : ContDiffAt ℝ ∞ f (massInterpolation t x)) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y=> f (massInterpolation t y)) x‖ ≤ ‖iteratedFDeriv ℝ j f (massInterpolation t x)‖ := by
  rw [iteratedFDeriv_comp_massInterpolation t hf j]
  exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
    ((mul_le_mul_of_nonneg_left (Finset.prod_le_one₀ (fun _ _=> norm_nonneg _)
      (fun _ _=> norm_massInterpolationLinear_le ht)) (norm_nonneg _)).trans_eq (mul_one _))

end DepthPaper
