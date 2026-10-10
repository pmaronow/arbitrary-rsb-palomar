module

public import GeneralDepthPaper.AtomicStationary

@[expose] public section


/-! The actual contact geometry persists along convergent stationary charts.
The uniform origin sign follows from the seed's strict subcriticality
and smooth coefficient convergence, retaining quadratic interactions. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace GeneralDepthPaper
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

theorem stationary_contact_geometry_convergence_uniform (F : SmoothCovarianceFamily Θ)
    {θ : Θ} (hθ : θ∈F.domain) {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (hbase : AtomicContactGeometry (F.covariance θ) z hz)
    (θn : ℕ→Θ) (hθn : ∀n,θn n∈F.domain)
    (a : ℝ) (ha : a < 1) (haN : ∀ n, (F.covariance (θn n)).second 0 ≤ a)
    (zN : ℕ→AtomicPoint r)
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
    z.1 (fun n=>(zN n).1) (by norm_num) le_rfl (originRadius_pos ha hCp)
    (contDiffOn_firstVariation_atomicMeasure _ z hz)
    (fun n=>contDiffOn_firstVariation_atomicMeasure _ (zN n) (hzN n))
    (fun q hq=>(hbase.1 q hq).1) hzero hpos hbase.2
    (F.firstVariation_atomic_C2_convergence hθ z hz θn hθn zN hzN hθt hzt)
    (fun i=>((continuous_apply i).comp continuous_fst).continuousAt.tendsto.comp hzt)
    (fun n=>firstVariation_zero _ _)
    (fun n q hq=>firstVariation_neg_near_origin _ _ (haN n) ha (hC' n) hq)
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

theorem stationary_contact_geometry_convergence (F : SmoothCovarianceFamily Θ)
    {θ : Θ} (hθ : θ∈F.domain) {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (hbase : AtomicContactGeometry (F.covariance θ) z hz)
    (hsub : (F.covariance θ).IsSubcritical)
    (θn : ℕ→Θ) (hθn : ∀n,θn n∈F.domain) (zN : ℕ→AtomicPoint r)
    (hzN : ∀n,IsAtomicPoint (zN n)) (hθt : Tendsto θn atTop (𝓝 θ))
    (hzt : Tendsto zN atTop (𝓝 z))
    (hs : ∀n,fderiv ℝ (atomicFunctionalExtension (F.covariance (θn n)) r) (zN n)=0) :
    ∀ᶠn in atTop,AtomicContactGeometry (F.covariance (θn n)) (zN n) (hzN n) := by
  let a : ℝ := ((F.covariance θ).second 0 + 1) / 2
  have ha : a < 1 := by dsimp only [a]; change (F.covariance θ).second 0 < 1 at hsub; linarith
  have hsa : (F.covariance θ).second 0 < a := by
    dsimp only [a]; change (F.covariance θ).second 0 < 1 at hsub; linarith
  have ht : Tendsto (fun n => (F.covariance (θn n)).second 0) atTop
      (𝓝 ((F.covariance θ).second 0)) := by
    have hc := (F.contDiffAt_second hθ 0).continuousAt
    have hp : Tendsto (fun n => (θn n, (0 : ℝ))) atTop (𝓝 (θ, (0 : ℝ))) :=
      hθt.prodMk_nhds (tendsto_const_nhds (x := (0 : ℝ)))
    have hct : Tendsto (fun w : Θ × ℝ => (F.covariance w.1).second w.2)
        (𝓝 (θ, (0 : ℝ))) (𝓝 ((F.covariance θ).second 0)) := hc.tendsto
    simpa only [Function.comp_def] using hct.comp hp
  have he : ∀ᶠ n in atTop, (F.covariance (θn n)).second 0 ≤ a :=
    (ht.eventually (eventually_lt_nhds hsa)).mono (fun _ h => h.le)
  obtain ⟨N, hN⟩ := he.exists_forall_of_atTop
  have hn := F.stationary_contact_geometry_convergence_uniform hθ z hz hbase
    (fun n => θn (n + N)) (fun n => hθn (n + N)) a ha
    (fun n => hN (n + N) (by omega))
    (fun n => zN (n + N)) (fun n => hzN (n + N))
    (hθt.comp (tendsto_add_atTop_nat N)) (hzt.comp (tendsto_add_atTop_nat N))
    (fun n => hs (n + N))
  have hm : ∀ᶠ n in Filter.map (fun n : ℕ => n + N) atTop,
      AtomicContactGeometry (F.covariance (θn n)) (zN n) (hzN n) :=
    Filter.eventually_map.mpr hn
  rwa [Filter.map_add_atTop_eq_nat N] at hm

theorem eventually_stationary_contact_geometry (F : SmoothCovarianceFamily Θ)
    {θ : Θ} (hθ : θ∈F.domain) {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (hbase : AtomicContactGeometry (F.covariance θ) z hz)
    (hsub : (F.covariance θ).IsSubcritical)
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
  have hg:=F.stationary_contact_geometry_convergence hθ z hz hbase hsub θn hθn
    (fun n=>zF (θn n)) hzN hθt hzt hstationary
  obtain ⟨n,hg⟩:=hg.exists
  exact (hn n).1 (fun ht=>hg)

end SmoothCovarianceFamily
end GeneralDepthPaper
