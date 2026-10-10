module

public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Compactness.Compact

set_option backward.privateInPublic true

@[expose] public section


/-! A genuine smooth root of a strictly increasing scalar equation on a
fixed compact interval.  This is an analytic foundation for the actual
high-degree endpoint equation; physical sign and derivative estimates are
discharged in its separate application. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 900000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The chosen interior zero; the default value is irrelevant wherever the
proved interval sign and strict monotonicity conditions hold. -/
def intervalImplicitRoot (G : E × ℝ → ℝ) (a b : ℝ) (θ : E) : ℝ := by
  classical
  exact if h : ∃ q ∈ Ioo a b, G (θ,q) = 0 then h.choose else a

theorem existsUnique_interval_root (g : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hreg : ∀ q ∈ Icc a b, ContDiffAt ℝ ∞ g q)
    (ha : g a < 0) (hb : 0 < g b)
    (hderiv : ∀ q ∈ Icc a b, 0 < deriv g q) :
    ∃! q : ℝ, q ∈ Ioo a b ∧ g q = 0 := by
  have hc : ContinuousOn g (Icc a b) :=
    fun q hq => (hreg q hq).continuousAt.continuousWithinAt
  have hm : StrictMonoOn g (Icc a b) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _) hc (f' := deriv g)
    · intro q hq
      rw [interior_Icc] at hq
      exact ((hreg q ⟨hq.1.le,hq.2.le⟩).differentiableAt (by simp)).hasDerivAt.hasDerivWithinAt
    · intro q hq
      rw [interior_Icc] at hq
      exact hderiv q ⟨hq.1.le,hq.2.le⟩
  obtain ⟨q,hq,hzero⟩ := intermediate_value_Icc hab.le hc ⟨ha.le,hb.le⟩
  have hqa : a < q := by
    rcases hq.1.eq_or_lt with he|hlt
    · subst q
      linarith
    · exact hlt
  have hqb : q < b := by
    rcases hq.2.eq_or_lt with he|hlt
    · subst q
      linarith
    · exact hlt
  refine ⟨q,⟨⟨hqa,hqb⟩,hzero⟩,?_⟩
  intro r hr
  exact hm.injOn ⟨hr.1.1.le,hr.1.2.le⟩ hq (hr.2.trans hzero.symm)

theorem intervalImplicitRoot_spec (G : E × ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (θ : E) (hreg : ∀ q ∈ Icc a b, ContDiffAt ℝ ∞ (fun q => G (θ,q)) q)
    (ha : G (θ,a) < 0) (hb : 0 < G (θ,b))
    (hderiv : ∀ q ∈ Icc a b, 0 < deriv (fun q => G (θ,q)) q) :
    intervalImplicitRoot G a b θ ∈ Ioo a b ∧ G (θ,intervalImplicitRoot G a b θ) = 0 := by
  classical
  obtain ⟨q,hq,_⟩ := existsUnique_interval_root (fun q => G (θ,q)) hab hreg ha hb hderiv
  have hex : ∃ q ∈ Ioo a b, G (θ,q) = 0 := ⟨q,hq⟩
  simp only [intervalImplicitRoot, dite_eq_left hex]
  exact hex.choose_spec

theorem intervalImplicitRoot_unique (G : E × ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (θ : E) (hreg : ∀ q ∈ Icc a b, ContDiffAt ℝ ∞ (fun q => G (θ,q)) q)
    (ha : G (θ,a) < 0) (hb : 0 < G (θ,b))
    (hderiv : ∀ q ∈ Icc a b, 0 < deriv (fun q => G (θ,q)) q)
    {q : ℝ} (hq : q ∈ Ioo a b) (hzero : G (θ,q) = 0) :
    intervalImplicitRoot G a b θ = q := by
  obtain ⟨r,hr,hunique⟩ := existsUnique_interval_root (fun q => G (θ,q)) hab hreg ha hb hderiv
  have hs := intervalImplicitRoot_spec G hab θ hreg ha hb hderiv
  exact (hunique _ hs).trans (hunique q ⟨hq,hzero⟩).symm

private theorem invertible_partial_of_positive (G : E × ℝ → ℝ) (θ : E) (q : ℝ)
    (hG : ContDiffAt ℝ ∞ G (θ,q)) (hpos : 0 < deriv (fun r => G (θ,r)) q) :
    (fderiv ℝ G (θ,q) ∘L ContinuousLinearMap.inr ℝ E ℝ).IsInvertible := by
  let L : ℝ →L[ℝ] ℝ := fderiv ℝ G (θ,q) ∘L ContinuousLinearMap.inr ℝ E ℝ
  have hd : HasDerivAt (fun r => G (θ,r)) (L 1) q := by
    convert (hG.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt q
      ((hasDerivAt_const q θ).prodMk (hasDerivAt_id q)) using 1
    · rfl
    · simp [L]
  have hL : L 1 ≠ 0 := by rw [hd.deriv] at hpos; exact hpos.ne'
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (L 1) hL)
  have he : L = (e : ℝ →L[ℝ] ℝ) := by
    apply ContinuousLinearMap.ext
    intro r
    calc
      L r = L (r • (1 : ℝ)) := by simp
      _ = r * L 1 := by rw [map_smul];rfl
      _ = e r := by simp [e]
  change L.IsInvertible
  rw [he]
  exact ContinuousLinearMap.isInvertible_equiv

theorem contDiffAt_intervalImplicitRoot (G : E × ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (U : Set (E × ℝ)) (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U)
    (O : Set E) (hO : IsOpen O)
    (hfiber : ∀ θ ∈ O, ∀ q ∈ Icc a b, (θ,q) ∈ U)
    (ha : ∀ θ ∈ O, G (θ,a) < 0) (hb : ∀ θ ∈ O, 0 < G (θ,b))
    (hderiv : ∀ θ ∈ O, ∀ q ∈ Icc a b, 0 < deriv (fun r => G (θ,r)) q)
    {θ : E} (hθ : θ ∈ O) :
    ContDiffAt ℝ ∞ (intervalImplicitRoot G a b) θ := by
  have hslice : ∀ u ∈ O, ∀ q ∈ Icc a b,
      ContDiffAt ℝ ∞ (fun r => G (u,r)) q := by
    intro u hu q hq
    exact (hG.contDiffAt (hU.mem_nhds (hfiber u hu q hq))).comp q
      (contDiffAt_const.prodMk contDiffAt_id)
  let q := intervalImplicitRoot G a b θ
  have hq := intervalImplicitRoot_spec G hab θ (hslice θ hθ) (ha θ hθ) (hb θ hθ)
    (hderiv θ hθ)
  have hGq : ContDiffAt ℝ ∞ G (θ,q) :=
    hG.contDiffAt (hU.mem_nhds (hfiber θ hθ q ⟨hq.1.1.le,hq.1.2.le⟩))
  have hinv := invertible_partial_of_positive G θ q hGq
    (hderiv θ hθ q ⟨hq.1.1.le,hq.1.2.le⟩)
  let w : E → ℝ := hGq.implicitFunction (by simp) hinv
  have hws : ContDiffAt ℝ ∞ w θ := hGq.contDiffAt_implicitFunction (by simp) hinv
  have hw0 : w θ = q := hGq.implicitFunction_apply_self (by simp) hinv
  have hwzero : ∀ᶠ u in 𝓝 θ, G (u,w u) = 0 := by
    filter_upwards [hGq.eventually_apply_implicitFunction (by simp) hinv] with u hu
    exact hu.trans hq.2
  have hwmem : ∀ᶠ u in 𝓝 θ, w u ∈ Ioo a b := by
    have hqnhds : Ioo a b ∈ 𝓝 (w θ) := by rw [hw0];exact Ioo_mem_nhds hq.1.1 hq.1.2
    exact hws.continuousAt.tendsto.eventually hqnhds
  have heq : intervalImplicitRoot G a b =ᶠ[𝓝 θ] w := by
    filter_upwards [hO.mem_nhds hθ,hwmem,hwzero] with u hu hwu hwz
    exact intervalImplicitRoot_unique G hab u (hslice u hu) (ha u hu) (hb u hu)
      (hderiv u hu) hwu hwz
  exact hws.congr_of_eventuallyEq heq

theorem contDiffOn_intervalImplicitRoot (G : E × ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (U : Set (E × ℝ)) (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U)
    (O : Set E) (hO : IsOpen O)
    (hfiber : ∀ θ ∈ O, ∀ q ∈ Icc a b, (θ,q) ∈ U)
    (ha : ∀ θ ∈ O, G (θ,a) < 0) (hb : ∀ θ ∈ O, 0 < G (θ,b))
    (hderiv : ∀ θ ∈ O, ∀ q ∈ Icc a b, 0 < deriv (fun r => G (θ,r)) q) :
    ContDiffOn ℝ ∞ (intervalImplicitRoot G a b) O :=
  fun _ hθ => (contDiffAt_intervalImplicitRoot G hab U hU hG O hO hfiber ha hb hderiv hθ).contDiffWithinAt

end GeneralDepthPaper
