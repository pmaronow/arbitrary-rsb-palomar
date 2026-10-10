module

public import GeneralDepthPaper.UniformDerivativeCalculus
public import GeneralDepthPaper.ClosedSubmoduleRegularity

@[expose] public section


/-! Finite jet assembly and closed-subspace restriction retain quantitative
all-order bounds. The inherited max norm is handled by actual isometries. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GeneralDepthPaper
universe u
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem BoundedSmoothOn.sum {ι : Type u} (u : Finset ι) (f : ι→E→F) (s : Set E)
    (hf : ∀i∈u,BoundedSmoothOn (f i) s) :
    BoundedSmoothOn (fun x=>∑i∈u,f i x) s := by
  classical
  induction u using Finset.induction with
  | empty => simpa only [Finset.sum_empty] using BoundedSmoothOn.const (0:F) s
  | insert i u hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self i u)).add
        (ih (fun j hj=>hf j (Finset.mem_insert_of_mem hj)))

theorem BoundedSmoothOn.pi {ι : Type u} [Fintype ι] (f : E→ι→F) (s : Set E)
    (hf : ∀i,BoundedSmoothOn (fun x=>f x i) s) : BoundedSmoothOn f s := by
  classical
  have h := BoundedSmoothOn.sum Finset.univ
    (fun i=>(ContinuousLinearMap.single ℝ (fun _:ι=>F) i)∘(fun x=>f x i)) s
    (fun i _=>(hf i).compCLM (ContinuousLinearMap.single ℝ (fun _:ι=>F) i))
  have he : (fun x=>∑i:ι,(ContinuousLinearMap.single ℝ (fun _:ι=>F) i) (f x i))=f := by
    funext x
    exact Finset.univ_sum_single (f x)
  simpa only [Function.comp_def,he] using h

theorem BoundedSmoothOn.submodule (S : Submodule ℝ F) (hS : IsClosed (S:Set F))
    (f : E→S) (s : Set E) (hf : BoundedSmoothOn (fun x=>(f x:F)) s) :
    BoundedSmoothOn f s := by
  have hc : ∀x∈s,ContDiffAt ℝ ∞ f x := fun x hx=>
    contDiffAt_submodule_of_coe S hS f x (hf.smooth x hx)
  refine ⟨hc,fun n=>?_⟩
  obtain ⟨C,hC,hb⟩:=hf.bound n
  refine ⟨C,hC,fun x hx=>?_⟩
  have he := S.subtypeₗᵢ.norm_iteratedFDeriv_comp_left (hc x hx)
    (show (n:ℕ∞ω)≤∞ from by simp)
  exact he ▸ hb x hx

end GeneralDepthPaper
