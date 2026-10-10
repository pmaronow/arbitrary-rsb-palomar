module

public import GeneralDepthPaper.ColeHopfRecursionBounds
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section


/-! Quantitative mean-value bounds for the actual recursion and all its
Fréchet jets on a convex terminal-data ball. The terminal space is Banach;
no compactness of its norm ball is used. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GeneralDepthPaper
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000

 theorem BoundedSmoothOn.jet_lipschitz {f : E→F} {s : Set E}
    (hf : BoundedSmoothOn f s) (hs : Convex ℝ s) (j : ℕ) :
    ∃C:ℝ,0 ≤ C ∧ ∀x∈s,∀y∈s,
      ‖iteratedFDeriv ℝ j f y-iteratedFDeriv ℝ j f x‖ ≤ C*‖y-x‖ := by
  obtain ⟨C,hC,hb⟩ := hf.bound (j+1)
  refine ⟨C,hC,fun x hx y hy => ?_⟩
  apply hs.norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) ?_ ?_ hx hy
  · intro z hz
    exact ((hf.smooth z hz).iteratedFDeriv_right (m:=∞) (by simp)).differentiableAt (by simp)
  · intro z hz
    rw [norm_fderiv_iteratedFDeriv]
    exact hb z hz

 theorem BoundedSmoothOn.value_lipschitz {f : E→F} {s : Set E}
    (hf : BoundedSmoothOn f s) (hs : Convex ℝ s) :
    ∃C:ℝ,0 ≤ C ∧ ∀x∈s,∀y∈s,‖f y-f x‖ ≤ C*‖y-x‖ := by
  obtain ⟨C,hC,hb⟩ := hf.fderiv.bound 0
  refine ⟨C,hC,fun x hx y hy => ?_⟩
  apply hs.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hf.smooth z hz).differentiableAt (by simp)) ?_ hx hy
  intro z hz
  simpa only [norm_iteratedFDeriv_zero] using hb z hz

 theorem convex_coleHopfRecursionBall (L : ℕ) (A Vlo Vhi B : ℝ) :
    Convex ℝ (coleHopfRecursionBall L A Vlo Vhi B) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    have hf : (a • x+b • y).1 i = a • x.1 i+b • y.1 i := rfl
    rw [hf]
    constructor
    · change ‖a*(x.1 i).1+b*(y.1 i).1‖ ≤ A
      calc
        _ ≤ ‖a*(x.1 i).1‖+‖b*(y.1 i).1‖ := norm_add_le _ _
        _ = a*‖(x.1 i).1‖+b*‖(y.1 i).1‖ := by
          rw [norm_mul,norm_mul,Real.norm_of_nonneg ha,Real.norm_of_nonneg hb]
        _ ≤ a*A+b*A := add_le_add (mul_le_mul_of_nonneg_left (hx.1 i).1 ha)
          (mul_le_mul_of_nonneg_left (hy.1 i).1 hb)
        _ = A := by rw [←add_mul,hab,one_mul]
    · change Vlo ≤ a*(x.1 i).2+b*(y.1 i).2 ∧ a*(x.1 i).2+b*(y.1 i).2 ≤ Vhi
      constructor
      · calc
          _ = a*Vlo+b*Vlo := by rw [←add_mul,hab,one_mul]
          _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hx.1 i).2.1 ha)
            (mul_le_mul_of_nonneg_left (hy.1 i).2.1 hb)
      · calc
          _ ≤ a*Vhi+b*Vhi := add_le_add (mul_le_mul_of_nonneg_left (hx.1 i).2.2 ha)
            (mul_le_mul_of_nonneg_left (hy.1 i).2.2 hb)
          _ = _ := by rw [←add_mul,hab,one_mul]
  · change ‖a • x.2+b • y.2‖ ≤ B
    calc
      _ ≤ ‖a • x.2‖+‖b • y.2‖ := norm_add_le _ _
      _ = a*‖x.2‖+b*‖y.2‖ := by rw [norm_smul,norm_smul,Real.norm_of_nonneg ha,Real.norm_of_nonneg hb]
      _ ≤ a*B+b*B := add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
        (mul_le_mul_of_nonneg_left hy.2 hb)
      _ = B := by rw [←add_mul,hab,one_mul]

 theorem coleHopfRecursion_jet_lipschitz (L : ℕ) (A Vlo Vhi B : ℝ)
    (hA : 0 ≤ A) (hVlo : 0 < Vlo) (hV : Vlo ≤ Vhi) (hB : 0 ≤ B) (j : ℕ) :
    ∃C:ℝ,0 ≤ C ∧ ∀x∈coleHopfRecursionBall L A Vlo Vhi B,
      ∀y∈coleHopfRecursionBall L A Vlo Vhi B,
      ‖iteratedFDeriv ℝ j (coleHopfRecursion L) y-
        iteratedFDeriv ℝ j (coleHopfRecursion L) x‖ ≤ C*‖y-x‖ :=
  (boundedSmoothOn_coleHopfRecursion L A Vlo Vhi B hA hVlo hV hB).jet_lipschitz
    (convex_coleHopfRecursionBall L A Vlo Vhi B) j

end GeneralDepthPaper
