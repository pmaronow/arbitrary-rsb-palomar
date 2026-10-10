module

public import DepthPaper.AtomicStationary

@[expose] public section


/-! The actual contact geometry persists along convergent stationary charts.
The uniform origin sign comes from the covariance's minimum interaction
degree four, rather than an additional contact-stability assumption. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

def AtomicContactGeometry (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) : Prop :=
  (∀q∈Icc (0:ℝ) 1,firstVariation Ξ (atomicMeasure z hz) q≤0 ∧
    (firstVariation Ξ (atomicMeasure z hz) q=0 ↔ ∃i,q=atomicLocation z i)) ∧
  (∀i : Fin r,closedJet 1 2 (firstVariation Ξ (atomicMeasure z hz)) (z.1 i)<0)

theorem AtomicContactGeometry.isMinimizer {Ξ : AdmissibleCovariance} {r : ℕ}
    {z : AtomicPoint r} {hz : IsAtomicPoint z} (h : AtomicContactGeometry Ξ z hz) :
    IsParisiMinimizer Ξ (atomicMeasure z hz) := by
  apply isParisiMinimizer_of_nonpos_zero_support Ξ _ (fun q hq=>(h.1 q hq).1)
  intro q hq
  rw [support_atomicMeasure] at hq
  obtain ⟨i,rfl⟩:=hq
  exact (h.1 _ (atomicLocation_mem_unit hz i)).2.mpr ⟨i,rfl⟩

namespace SmoothCovarianceFamily
variable {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]

theorem stationary_contact_geometry_convergence (F : SmoothCovarianceFamily Θ)
    {θ : Θ} (hθ : θ∈F.domain) {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (hbase : AtomicContactGeometry (F.covariance θ) z hz)
    (θn : ℕ→Θ) (hθn : ∀n,θn n∈F.domain) (zN : ℕ→AtomicPoint r)
    (hzN : ∀n,IsAtomicPoint (zN n)) (hθt : Tendsto θn atTop (𝓝 θ))
    (hzt : Tendsto zN atTop (𝓝 z))
    (hs : ∀n,fderiv ℝ (atomicFunctionalExtension (F.covariance (θn n)) r) (zN n)=0) :
    ∀ᶠn in atTop,AtomicContactGeometry (F.covariance (θn n)) (zN n) (hzN n) := by
  have hfirst : Tendsto (fun n=>(F.covariance (θn n)).first (1/2)) atTop
      (𝓝 ((F.covariance θ).first (1/2))) := by
    have hc:=(F.contDiffAt_first hθ (1/2)).continuousAt
    exact hc.tendsto.comp (hθt.prodMk_nhds (tendsto_const_nhds (x:=(1/2:ℝ))))
  obtain ⟨C,hC⟩ := (Metric.isBounded_range_of_tendsto _ hfirst).exists_norm_le
  have hC' (n : ℕ) : (F.covariance (θn n)).first (1/2)≤C :=
    (le_abs_self _).trans (hC _ ⟨n,rfl⟩)
  have hCp : 0<C := ((F.covariance (θn 0)).first_pos (by norm_num)).trans_le (hC' 0)
  have hcontacts (n : ℕ):=atomic_stationary_contacts _ (zN n) (hzN n) (hs n)
  have hpos (i : Fin r) : z.1 i∈Ioo (0:ℝ) 1 :=
    ⟨by simpa only [atomicLocation_zero,atomicLocation_succ] using hz.1 (Fin.succ_pos i),
      (hz.1.monotone (Fin.le_last i.succ)).trans_lt hz.2.1⟩
  have hzero : ∀q∈Icc (0:ℝ) 1,firstVariation (F.covariance θ) (atomicMeasure z hz) q=0 ↔
      q=0 ∨ ∃i : Fin r,z.1 i=q := by
    intro q hq
    rw [(hbase.1 q hq).2]
    constructor
    · rintro ⟨i,hi⟩
      cases i using Fin.cases with
      | zero => exact Or.inl hi
      | succ j => exact Or.inr ⟨j,hi.symm⟩
    · rintro (rfl|⟨i,hi⟩)
      · exact ⟨0,rfl⟩
      · exact ⟨i.succ,hi.symm⟩
  have hn:=contact_perturbation_closed_C2
    (firstVariation (F.covariance θ) (atomicMeasure z hz))
    (fun n=>firstVariation (F.covariance (θn n)) (atomicMeasure (zN n) (hzN n)))
    z.1 (fun n=>(zN n).1) (by norm_num) le_rfl (originRadius_pos hCp)
    (contDiffOn_firstVariation_atomicMeasure _ z hz)
    (fun n=>contDiffOn_firstVariation_atomicMeasure _ (zN n) (hzN n))
    (fun q hq=>(hbase.1 q hq).1) hzero hpos hbase.2
    (F.firstVariation_atomic_C2_convergence hθ z hz θn hθn zN hzN hθt hzt)
    (fun i=>((continuous_apply i).comp continuous_fst).continuousAt.tendsto.comp hzt)
    (fun n=>firstVariation_zero _ _)
    (fun n q hq=>firstVariation_neg_near_origin _ _ (hC' n) hq)
    (fun n i=>by simpa only [atomicLocation_succ] using (hcontacts n).1 i.succ)
    (fun n i=>(hcontacts n).2 i)
  filter_upwards [hn] with n hn
  refine ⟨?_,hn.2.2⟩
  intro q hq
  refine ⟨hn.1 q hq,?_⟩
  rw [hn.2.1 q hq]
  constructor
  · rintro (rfl|⟨i,rfl⟩)
    · exact ⟨0,rfl⟩
    · exact ⟨i.succ,rfl⟩
  · rintro ⟨i,rfl⟩
    cases i using Fin.cases with
    | zero => exact Or.inl rfl
    | succ j => exact Or.inr ⟨j,rfl⟩

theorem eventually_stationary_contact_geometry (F : SmoothCovarianceFamily Θ)
    {θ : Θ} (hθ : θ∈F.domain) {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (hbase : AtomicContactGeometry (F.covariance θ) z hz)
    (zF : Θ→AtomicPoint r) (hvalue : zF θ=z) (hcont : ContinuousAt zF θ)
    (hs : ∀ᶠt in 𝓝 θ,IsAtomicPoint (zF t) ∧ atomicGradientFamily F r (t,zF t)=0) :
    ∀ᶠt in 𝓝 θ,∀ht:IsAtomicPoint (zF t),AtomicContactGeometry (F.covariance t) (zF t) ht := by
  by_contra h
  have hd : ∀ᶠt in 𝓝 θ,t∈F.domain := F.isOpen_domain.mem_nhds hθ
  have hbad:= (not_eventually.mp h).and_eventually
    (hd.and hs)
  obtain ⟨θn,hθt,hn⟩:=exists_seq_forall_of_frequently hbad
  have hθn (n : ℕ) : θn n∈F.domain := (hn n).2.1
  have hzN (n : ℕ) : IsAtomicPoint (zF (θn n)) := (hn n).2.2.1
  have hzt : Tendsto (fun n=>zF (θn n)) atTop (𝓝 z) := by
    simpa only [hvalue,Function.comp_def] using hcont.tendsto.comp hθt
  have hstationary (n : ℕ) :
      fderiv ℝ (atomicFunctionalExtension (F.covariance (θn n)) r) (zF (θn n))=0 :=
    (hn n).2.2.2
  have hg:=F.stationary_contact_geometry_convergence hθ z hz hbase θn hθn
    (fun n=>zF (θn n)) hzN hθt hzt hstationary
  obtain ⟨n,hg⟩:=hg.exists
  exact (hn n).1 (fun ht=>hg)

end SmoothCovarianceFamily
end DepthPaper
