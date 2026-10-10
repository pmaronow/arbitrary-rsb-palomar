module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

@[expose] public section


/-! Regularity into a closed linear subspace is detected by the ambient map.
Derivative values belong to the subspace by actual limits of difference
quotients; finite-order induction then lifts the derivative map as well. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000
universe u
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def linearMapsInto (S : Submodule ℝ F) : Submodule ℝ (E→L[ℝ]F) where
  carrier := {A | ∀v,A v∈S}
  zero_mem' := fun _=>S.zero_mem
  add_mem' := fun hA hB v=>S.add_mem (hA v) (hB v)
  smul_mem' := fun c _ hA v=>S.smul_mem c (hA v)

theorem isClosed_linearMapsInto (S : Submodule ℝ F) (hS : IsClosed (S:Set F)) :
    IsClosed (linearMapsInto (E:=E) S : Set (E→L[ℝ]F)) := by
  have he : (linearMapsInto (E:=E) S : Set (E→L[ℝ]F))=
      ⋂v:E,(fun A:E→L[ℝ]F=>A v)⁻¹'(S:Set F) := by ext A; simp [linearMapsInto]
  rw [he]
  exact isClosed_iInter fun v=>hS.preimage (ContinuousLinearMap.apply ℝ F v).continuous

def restrictLinearMaps (S : Submodule ℝ F) : linearMapsInto (E:=E) S→L[ℝ](E→L[ℝ]S) :=
  LinearMap.mkContinuous
    {toFun:=fun A=>A.1.codRestrict S A.2
     map_add':=fun A B=>by ext v; rfl
     map_smul':=fun c A=>by ext v; rfl}
    1 (fun A=>by
      simp only [one_mul]
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro v
      exact A.1.le_opNorm v)

theorem hasFDerivAt_range_closed (S : Submodule ℝ F) (hS : IsClosed (S:Set F))
    (f : E→S) {A : E→L[ℝ]F} {x:E}
    (h : HasFDerivAt (fun y:E=>(f y : F)) A x) : ∀v,A v∈S := by
  intro v
  have hc : Tendsto (fun n:ℕ=>‖(n:ℝ)‖) atTop atTop := by
    simpa only [Real.norm_natCast] using (tendsto_natCast_atTop_atTop : Tendsto (fun n:ℕ=>(n:ℝ)) atTop atTop)
  exact hS.mem_of_tendsto (h.lim v hc)
    (.of_forall fun n=>S.smul_mem (n:ℝ) (S.sub_mem (f _).2 (f x).2))

theorem hasFDerivAt_codomainRestriction (S : Submodule ℝ F) (f : E→S)
    {A : E→L[ℝ]F} {x:E} (hA : ∀v,A v∈S)
    (h : HasFDerivAt (fun y:E=>(f y : F)) A x) :
    HasFDerivAt f (A.codRestrict S hA) x := by
  rw [hasFDerivAt_iff_tendsto] at h ⊢
  exact h

theorem contDiffAt_submodule_of_coe_nat (n : ℕ) (S : Submodule ℝ F)
    (hS : IsClosed (S:Set F)) (f : E→S) (x:E)
    (h : ContDiffAt ℝ n (fun y:E=>(f y:F)) x) : ContDiffAt ℝ n f x := by
  classical
  induction n generalizing F with
  | zero =>
    simp only [Nat.cast_zero,contDiffAt_zero] at h ⊢
    obtain ⟨U,hU,hf⟩ := h
    exact ⟨U,hU,fun y hy=>tendsto_subtype_rng.mpr (hf y hy)⟩
  | succ n ih =>
    obtain ⟨A,⟨U,hU,hA⟩,hreg⟩ := contDiffAt_succ_iff_hasFDerivAt.mp h
    let D := linearMapsInto (E:=E) S
    let B (y:E) : D := if hy: A y∈D then ⟨A y,hy⟩ else 0
    have hB (y:E) (hy:y∈U) : (B y : E→L[ℝ]F)=A y := by
      have hmem : A y∈D := hasFDerivAt_range_closed S hS f (hA y hy)
      simp only [B,dif_pos hmem]
    have he : (fun y:E=>(B y:E→L[ℝ]F))=ᶠ[𝓝 x]A :=
      Filter.eventuallyEq_of_mem hU hB
    have hregB : ContDiffAt ℝ n B x := ih D (isClosed_linearMapsInto S hS) B
      (hreg.congr_of_eventuallyEq he)
    refine contDiffAt_succ_iff_hasFDerivAt.mpr
      ⟨fun y=>restrictLinearMaps S (B y),⟨U,hU,?_⟩,
        (restrictLinearMaps S).contDiff.contDiffAt.comp x hregB⟩
    intro y hy
    have hb := (B y).2
    have ha := hasFDerivAt_codomainRestriction S f hb ((hB y hy).symm ▸ hA y hy)
    exact ha

theorem contDiffAt_submodule_of_coe (S : Submodule ℝ F) (hS : IsClosed (S:Set F))
    (f : E→S) (x:E) (h : ContDiffAt ℝ ∞ (fun y:E=>(f y:F)) x) :
    ContDiffAt ℝ ∞ f x := by
  rw [contDiffAt_infty] at h ⊢
  exact fun n=>contDiffAt_submodule_of_coe_nat n S hS f x (h n)

end GeneralDepthPaper
