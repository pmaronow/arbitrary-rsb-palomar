module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public section


/-! Local versions of quantitative derivative inequalities. This avoids
requiring a positive-variance kernel to be smooth at nonpositive variance. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
set_option maxSynthPendingDepth 64

theorem norm_iteratedFDeriv_bilinear_le_at (B : F→L[ℝ] G→L[ℝ] H)
    {f : E→F} {g : E→G} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (hg : ContDiffAt ℝ ∞ g x) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y=>B (f y) (g y)) x‖ ≤
      ‖B‖*∑i∈Finset.range (n+1),(n.choose i:ℝ)*
        ‖iteratedFDeriv ℝ i f x‖*‖iteratedFDeriv ℝ (n-i) g x‖ := by
  obtain ⟨u,hu,hxu,hfu⟩ := (hf.contDiffWithinAt (s:=univ)).contDiffOn' (m:=(n:ℕ∞ω)) (by simp) (by simp)
  obtain ⟨v,hv,hxv,hgv⟩ := (hg.contDiffWithinAt (s:=univ)).contDiffOn' (m:=(n:ℕ∞ω)) (by simp) (by simp)
  have hfu' : ContDiffOn ℝ n f u := by simpa using hfu
  have hgv' : ContDiffOn ℝ n g v := by simpa using hgv
  have hs : IsOpen (u∩v) := hu.inter hv
  have hx : x∈u∩v := ⟨hxu,hxv⟩
  have h := B.norm_iteratedFDerivWithin_le_of_bilinear
    (hfu'.mono inter_subset_left) (hgv'.mono inter_subset_right) hs.uniqueDiffOn hx le_rfl
  have heq (j:ℕ) : iteratedFDerivWithin ℝ j f (u∩v) x=iteratedFDeriv ℝ j f x :=
    iteratedFDerivWithin_eq_iteratedFDeriv hs.uniqueDiffOn (hf.of_le (by simp)) hx
  have geq (j:ℕ) : iteratedFDerivWithin ℝ j g (u∩v) x=iteratedFDeriv ℝ j g x :=
    iteratedFDerivWithin_eq_iteratedFDeriv hs.uniqueDiffOn (hg.of_le (by simp)) hx
  have beq : iteratedFDerivWithin ℝ n (fun y=>B (f y) (g y)) (u∩v) x=
      iteratedFDeriv ℝ n (fun y=>B (f y) (g y)) x :=
    iteratedFDerivWithin_eq_iteratedFDeriv hs.uniqueDiffOn
      ((B.isBoundedBilinearMap.contDiff.contDiffAt.comp₂ hf hg).of_le (by simp)) hx
  simpa only [heq,geq,beq] using h

theorem norm_iteratedFDeriv_comp_le_at {g : F→G} {f : E→F} {x : E}
    (hg : ContDiffAt ℝ ∞ g (f x)) (hf : ContDiffAt ℝ ∞ f x)
    (n : ℕ) (C D : ℝ)
    (hC : ∀ i : ℕ, i ≤ n → ‖iteratedFDeriv ℝ i g (f x)‖≤C)
    (hD : ∀ i : ℕ, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖≤D^i) :
    ‖iteratedFDeriv ℝ n (g∘f) x‖≤(n.factorial:ℝ)*C*D^n := by
  obtain ⟨u,hu,hxu,hfu⟩ := (hf.contDiffWithinAt (s:=univ)).contDiffOn' (m:=(n:ℕ∞ω)) (by simp) (by simp)
  obtain ⟨v,hv,hxv,hgv⟩ := (hg.contDiffWithinAt (s:=univ)).contDiffOn' (m:=(n:ℕ∞ω)) (by simp) (by simp)
  have hfu' : ContDiffOn ℝ n f u := by simpa using hfu
  have hgv' : ContDiffOn ℝ n g v := by simpa using hgv
  have hpre : f ⁻¹' v∩u∈𝓝 x :=
    inter_mem (hf.continuousAt.preimage_mem_nhds (hv.mem_nhds hxv)) (hu.mem_nhds hxu)
  obtain ⟨w,hwsub,hw,hxw⟩ := mem_nhds_iff.mp hpre
  have hfW : ContDiffOn ℝ n f w := hfu'.mono (hwsub.trans inter_subset_right)
  have hmaps : MapsTo f w v := fun y hy=> (hwsub hy).1
  have h := norm_iteratedFDerivWithin_comp_le hgv' hfW le_rfl
    hv.uniqueDiffOn hw.uniqueDiffOn hmaps hxw (C:=C) (D:=D)
  have feq (j:ℕ) : iteratedFDerivWithin ℝ j f w x=iteratedFDeriv ℝ j f x :=
    iteratedFDerivWithin_eq_iteratedFDeriv hw.uniqueDiffOn (hf.of_le (by simp)) hxw
  have geq (j:ℕ) : iteratedFDerivWithin ℝ j g v (f x)=iteratedFDeriv ℝ j g (f x) :=
    iteratedFDerivWithin_eq_iteratedFDeriv hv.uniqueDiffOn (hg.of_le (by simp)) hxv
  have ceq : iteratedFDerivWithin ℝ n (g∘f) w x=iteratedFDeriv ℝ n (g∘f) x :=
    iteratedFDerivWithin_eq_iteratedFDeriv hw.uniqueDiffOn
      ((hg.comp x hf).of_le (by simp)) hxw
  simpa only [feq,geq,ceq] using h (by simpa only [geq] using hC)
    (by simpa only [feq] using hD)

end DepthPaper
