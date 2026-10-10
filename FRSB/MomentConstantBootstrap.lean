module

public import FRSB.MomentBootstrap

@[expose] public section


/-! Simultaneous smoothness bootstrap for a constant-coefficient polynomial
moment hierarchy on an arbitrary open interval. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace FRSB

 theorem moments_contDiffOn_constant_hierarchy {ι:Type*}
    (e:ι→ℝ→ℝ) (f₀ f₁:ι→ι) (β m a b:ℝ)
    (he:∀i,ContinuousOn (e i) (Ioo a b))
    (hd:∀i t,t∈Ioo a b→HasDerivAt (e i) (β^2*(e (f₀ i) t+m*e (f₁ i) t)) t) :
    ∀i,ContDiffOn ℝ ∞ (e i) (Ioo a b) := by
  have hu:UniqueDiffOn ℝ (Ioo a b):=isOpen_Ioo.uniqueDiffOn
  have hn:∀n:ℕ,∀i,ContDiffOn ℝ n (e i) (Ioo a b) := by
    intro n
    induction n with
    | zero => intro i;exact contDiffOn_zero.mpr (he i)
    | succ n ih =>
      intro i
      rw [Nat.cast_add,Nat.cast_one,contDiffOn_succ_iff_derivWithin hu]
      refine ⟨fun t ht=>(hd i t ht).hasDerivWithinAt.differentiableWithinAt,by simp,?_⟩
      have hc:ContDiffOn ℝ (n:ℕ∞ω)
          (fun t=>β^2*(e (f₀ i) t+m*e (f₁ i) t)) (Ioo a b) :=
        contDiffOn_const.mul ((ih (f₀ i)).add (contDiffOn_const.mul (ih (f₁ i))))
      exact hc.congr (fun t ht=>(hd i t ht).hasDerivWithinAt.derivWithin (hu t ht))
  intro i
  exact contDiffOn_infty.mpr (fun n=>hn n i)

end FRSB
