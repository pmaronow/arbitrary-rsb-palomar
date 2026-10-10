module

public import DepthPaper.PointwiseDerivativeBounds
public import DepthPaper.AnalyticDerivativeBound
public import Mathlib.Analysis.Analytic.Linear
public import DepthPaper.InverseDerivativeBounds
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section


/-! Closure rules for bounds on all actual Fréchet derivatives over arbitrary
sets. No finite-dimensional compactness is imposed on terminal-function balls. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
set_option maxSynthPendingDepth 64

structure BoundedSmoothOn (f : E→F) (s : Set E) : Prop where
  smooth : ∀x∈s,ContDiffAt ℝ ∞ f x
  bound : ∀n:ℕ,∃C:ℝ,0≤C ∧ ∀x∈s,‖iteratedFDeriv ℝ n f x‖≤C

theorem BoundedSmoothOn.congr_of_eventuallyEq {f g : E→F} {s : Set E}
    (hf : BoundedSmoothOn f s) (he : ∀x∈s,f=ᶠ[𝓝 x]g) : BoundedSmoothOn g s := by
  refine ⟨fun x hx=>(hf.smooth x hx).congr_of_eventuallyEq (he x hx).symm,fun n=>?_⟩
  obtain ⟨C,hC,hb⟩:=hf.bound n
  exact ⟨C,hC,fun x hx=>by
    rw [←((he x hx).iteratedFDeriv (𝕜:=ℝ) n).eq_of_nhds]
    exact hb x hx⟩

theorem BoundedSmoothOn.mono {f : E→F} {s t : Set E}
    (hf : BoundedSmoothOn f s) (ht : t⊆s) : BoundedSmoothOn f t :=
  ⟨fun x hx=>hf.smooth x (ht hx),fun n=>by
    obtain ⟨C,hC,hb⟩:=hf.bound n
    exact ⟨C,hC,fun x hx=>hb x (ht hx)⟩⟩

theorem BoundedSmoothOn.const (c : F) (s : Set E) : BoundedSmoothOn (fun _:E=>c) s := by
  refine ⟨fun _ _=>contDiffAt_const,fun n=>⟨‖c‖,norm_nonneg _,?_⟩⟩
  intro x _
  cases n with
  | zero => simp only [norm_iteratedFDeriv_zero]; exact le_rfl
  | succ n => simpa only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero] using norm_nonneg c

theorem BoundedSmoothOn.compCLM {f : E→F} {s : Set E}
    (hf : BoundedSmoothOn f s) (L : F→L[ℝ] G) : BoundedSmoothOn (L∘f) s := by
  refine ⟨fun x hx=>L.contDiff.contDiffAt.comp x (hf.smooth x hx),fun n=>?_⟩
  obtain ⟨C,hC,hb⟩:=hf.bound n
  refine ⟨‖L‖*C,mul_nonneg (norm_nonneg _) hC,fun x hx=>?_⟩
  exact (L.norm_iteratedFDeriv_comp_left (hf.smooth x hx) (show (n:ℕ∞ω)≤∞ from by simp)).trans
    (mul_le_mul_of_nonneg_left (hb x hx) (norm_nonneg _))

theorem BoundedSmoothOn.add {f g : E→F} {s : Set E}
    (hf : BoundedSmoothOn f s) (hg : BoundedSmoothOn g s) :
    BoundedSmoothOn (fun x=>f x+g x) s := by
  refine ⟨fun x hx=>(hf.smooth x hx).add (hg.smooth x hx),fun n=>?_⟩
  obtain ⟨C,hC,hb⟩:=hf.bound n
  obtain ⟨D,hD,hd⟩:=hg.bound n
  refine ⟨C+D,add_nonneg hC hD,fun x hx=>?_⟩
  rw [fun_iteratedFDeriv_add_apply ((hf.smooth x hx).of_le (by simp))
    ((hg.smooth x hx).of_le (by simp))]
  exact (norm_add_le _ _).trans (add_le_add (hb x hx) (hd x hx))

theorem BoundedSmoothOn.neg {f : E→F} {s : Set E}
    (hf : BoundedSmoothOn f s) : BoundedSmoothOn (fun x=>-f x) s := by
  refine ⟨fun x hx=>(hf.smooth x hx).neg,fun n=>?_⟩
  obtain ⟨C,hC,hb⟩:=hf.bound n
  refine ⟨C,hC,fun x hx=>?_⟩
  change ‖iteratedFDeriv ℝ n (-f) x‖≤C
  simpa only [iteratedFDeriv_neg_apply,norm_neg] using hb x hx

theorem BoundedSmoothOn.sub {f g : E→F} {s : Set E}
    (hf : BoundedSmoothOn f s) (hg : BoundedSmoothOn g s) :
    BoundedSmoothOn (fun x=>f x-g x) s := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem BoundedSmoothOn.bilinear {f : E→F} {g : E→G} {s : Set E}
    (hf : BoundedSmoothOn f s) (hg : BoundedSmoothOn g s)
    (B : F→L[ℝ] G→L[ℝ] H) : BoundedSmoothOn (fun x=>B (f x) (g x)) s := by
  classical
  refine ⟨fun x hx=>B.isBoundedBilinearMap.contDiff.contDiffAt.comp₂
    (hf.smooth x hx) (hg.smooth x hx),fun n=>?_⟩
  choose C hC hb using hf.bound
  choose D hD hd using hg.bound
  refine ⟨‖B‖*∑i∈Finset.range (n+1),(n.choose i:ℝ)*C i*D (n-i),
    mul_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun i _=>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC i)) (hD (n-i)))),fun x hx=>?_⟩
  refine (norm_iteratedFDeriv_bilinear_le_at B (hf.smooth x hx) (hg.smooth x hx) n).trans ?_
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hb i x hx) (Nat.cast_nonneg _))
    (hd (n-i) x hx) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hC i))

theorem BoundedSmoothOn.prodMk {f : E→F} {g : E→G} {s : Set E}
    (hf : BoundedSmoothOn f s) (hg : BoundedSmoothOn g s) :
    BoundedSmoothOn (fun x=>(f x,g x)) s := by
  have h := (hf.compCLM (ContinuousLinearMap.inl ℝ F G)).add
    (hg.compCLM (ContinuousLinearMap.inr ℝ F G))
  convert h using 1
  ext x <;> simp

theorem BoundedSmoothOn.comp {f : E→F} {g : F→G} {s : Set E} {t : Set F}
    (hg : BoundedSmoothOn g t) (hf : BoundedSmoothOn f s) (hmap : MapsTo f s t) :
    BoundedSmoothOn (g∘f) s := by
  classical
  refine ⟨fun x hx=>(hg.smooth (f x) (hmap hx)).comp x (hf.smooth x hx),fun n=>?_⟩
  choose C hC hb using hg.bound
  choose D hD hd using hf.bound
  let Cn := ∑i∈Finset.range (n+1),C i
  let Dn := 1+∑i∈Finset.range (n+1),D i
  have hCn : 0≤Cn := Finset.sum_nonneg (fun i _=>hC i)
  have hDn : 1≤Dn := by
    have hs := Finset.sum_nonneg (fun i (_:i∈Finset.range (n+1))=>hD i)
    dsimp [Dn]
    linarith
  refine ⟨(n.factorial:ℝ)*Cn*Dn^n,by positivity,fun x hx=>?_⟩
  apply norm_iteratedFDeriv_comp_le_at (hg.smooth (f x) (hmap hx)) (hf.smooth x hx) n Cn Dn
  · intro i hi
    exact (hb i (f x) (hmap hx)).trans
      (Finset.single_le_sum (fun j _=>hC j) (Finset.mem_range.mpr (by omega)))
  · intro i hi hin
    have hdi : D i≤∑j∈Finset.range (n+1),D j :=
      Finset.single_le_sum (fun j _=>hD j) (Finset.mem_range.mpr (by omega))
    exact (hd i x hx).trans ((hdi.trans (by dsimp [Dn]; linarith)).trans
      (le_self_pow₀ hDn (by omega)))

theorem BoundedSmoothOn.linear [CompleteSpace F] (L : E→L[ℝ] F) (s : Set E)
    (B : ℝ) (hB : 0≤B) (hb : ∀x∈s,‖x‖≤B) : BoundedSmoothOn L s := by
  refine ⟨fun _ _=>L.contDiff.contDiffAt,fun n=>⟨(n.factorial:ℝ)*max (‖L‖*B) ‖L‖,
    by positivity,fun x hx=>?_⟩⟩
  apply (norm_iteratedFDeriv_le_factorial_coefficient (L.hasFPowerSeriesOnBall x) n).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  cases n with
  | zero =>
    change ‖(continuousMultilinearCurryFin0 ℝ E F).symm (L x)‖≤_
    rw [LinearIsometryEquiv.norm_map]
    exact (L.le_opNorm x).trans ((mul_le_mul_of_nonneg_left (hb x hx) (norm_nonneg _)).trans
      (le_max_left _ _))
  | succ n =>
    cases n with
    | zero =>
      change ‖(continuousMultilinearCurryFin1 ℝ E F).symm L‖≤_
      rw [LinearIsometryEquiv.norm_map]
      exact le_max_right _ _
    | succ n =>
      change ‖(0: E [×(n+2)]→L[ℝ] F)‖≤_
      rw [norm_zero]
      positivity

theorem BoundedSmoothOn.of_compact {f : E→F} {s : Set E} (hs : IsCompact s)
    (hf : ∀x∈s,ContDiffAt ℝ ∞ f x) : BoundedSmoothOn f s := by
  refine ⟨hf,fun n=>?_⟩
  obtain ⟨C,hC⟩:=hs.exists_bound_of_continuousOn
    (fun x hx=>(hf x hx).continuousAt_iteratedFDeriv (show (n:ℕ∞ω)≤∞ from by simp)
      |>.continuousWithinAt)
  exact ⟨max C 0,le_max_right _ _,fun x hx=>(hC x hx).trans (le_max_left _ _)⟩

theorem BoundedSmoothOn.fderiv {f : E→F} {s : Set E}
    (hf : BoundedSmoothOn f s) : BoundedSmoothOn (fderiv ℝ f) s := by
  refine ⟨fun x hx=>(hf.smooth x hx).fderiv_right (m:=∞) (by simp),fun n=>?_⟩
  obtain ⟨C,hC,hb⟩:=hf.bound (n+1)
  exact ⟨C,hC,fun x hx=>by simpa only [norm_iteratedFDeriv_fderiv] using hb x hx⟩

theorem BoundedSmoothOn.inverse {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] [NormOneClass A] [Nontrivial A]
    {f : E→A} {s : Set E} (hf : BoundedSmoothOn f s)
    (hu : ∀x∈s,IsUnit (f x)) (R : ℝ) (hR : 0≤R)
    (hb : ∀x∈s,‖Ring.inverse (f x)‖≤R) :
    BoundedSmoothOn (fun x=>Ring.inverse (f x)) s := by
  have hg : BoundedSmoothOn Ring.inverse (f '' s) := by
    refine ⟨?_,fun n=>⟨(n.factorial:ℝ)*R^(n+1),by positivity,?_⟩⟩
    · rintro z ⟨x,hx,rfl⟩
      simpa only [IsUnit.unit_spec] using
        (analyticAt_inverse (𝕜:=ℝ) (hu x hx).unit).contDiffAt (n:=∞)
    · rintro z ⟨x,hx,rfl⟩
      have h := norm_iteratedFDeriv_inverse_le (hu x hx).unit n
      have he : (((hu x hx).unit⁻¹:Aˣ):A)=Ring.inverse (f x) := by
        simpa only [IsUnit.unit_spec] using (Ring.inverse_unit (hu x hx).unit).symm
      simp only [IsUnit.unit_spec,he] at h
      exact h.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hb x hx) (n+1)) (Nat.cast_nonneg _))
  exact hg.comp hf (fun x hx=>⟨x,hx,rfl⟩)

end DepthPaper
