module

public import DepthPaper.ImplicitRootJetBounds
public import DepthPaper.StationaryGraphBounds

@[expose] public section


/-! A small smooth scalar residual gives genuine C² bounds for a root
relative to a varying smooth baseline. The local equation is differentiated
through the already proved implicit-correction estimate. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 1700000

def rootShiftMap (ell:ℝ→ℝ) (w:ℝ×ℝ):ℝ×ℝ:=(w.2-1+ell w.1,w.1)

theorem scalar_root_C2_perturbation {ell q:ℝ→ℝ} {G:ℝ×ℝ→ℝ} {m ε D:ℝ}
    (hell:ContDiffAt ℝ ∞ ell m) (hq:ContDiffAt ℝ ∞ q m)
    (hG:ContDiffAt ℝ ∞ G (q m,m)) (hε:0 ≤ ε) (hD:1 ≤ D)
    (hsmall:2*ε*D^2 ≤ 1/2)
    (heq:∀ᶠu in 𝓝 m,q u=ell u-G (q u,u))
    (hGj:∀j:ℕ,j ≤ 2→‖iteratedFDeriv ℝ j G (q m,m)‖ ≤ ε)
    (hTj:∀j:ℕ,j ≤ 2→‖iteratedFDeriv ℝ j (rootShiftMap ell) (m,1+q m-ell m)‖ ≤ D) :
    ‖iteratedFDeriv ℝ 1 (fun u=>q u-ell u) m‖ ≤ 2*ε*D^2 ∧
    ‖iteratedFDeriv ℝ 2 (fun u=>q u-ell u) m‖ ≤ 4*ε*D^2 := by
  let k:ℝ→ℝ:=fun u=>1+q u-ell u
  let A:ℝ×ℝ→ℝ:=G∘rootShiftMap ell
  have hk:ContDiffAt ℝ ∞ k m:=(contDiffAt_const.add hq).sub hell
  have hT:ContDiffAt ℝ ∞ (rootShiftMap ell) (m,k m) :=
    ((contDiffAt_snd.sub contDiffAt_const).add (hell.comp (m,k m) contDiffAt_fst)).prodMk
      contDiffAt_fst
  have hmap:rootShiftMap ell (m,k m)=(q m,m) := by dsimp [rootShiftMap,k];congr 1;ring
  have hGs:ContDiffAt ℝ ∞ G (rootShiftMap ell (m,k m)) := hmap.symm ▸ hG
  have hA:ContDiffAt ℝ ∞ A (m,k m):=hGs.comp (m,k m) hT
  have hAj (j:ℕ) (hj:j ≤ 2):‖iteratedFDeriv ℝ j A (m,k m)‖ ≤ 2*ε*D^2 := by
    have hh:=norm_iteratedFDeriv_composition_uniform_low_order hGs hT 2 hε hD
      (fun i hi=>by rw [hmap];exact hGj i hi) hTj j hj
    simpa [A] using hh
  have hloc:∀ᶠu in 𝓝 m,k u=1-A (u,k u) := by
    filter_upwards [heq] with u hu
    dsimp [k,A,rootShiftMap,Function.comp_def]
    have hi:1+q u-ell u-1+ell u=q u := by ring
    rw [hi]
    linarith
  have hb:=implicit_correction_first_second_jet_bound (by positivity) hsmall hA hk hloc
    (hAj 1 (by norm_num)) (hAj 2 (by norm_num))
  have hn (j:ℕ) (hj:0 < j):‖iteratedFDeriv ℝ j k m‖=
      ‖iteratedFDeriv ℝ j (fun u=>q u-ell u) m‖ := by
    have he:k=(fun u=> (1:ℝ)+(q u-ell u)) := by ext u;dsimp [k];ring
    have hc:ContDiffAt ℝ ∞ (fun _:ℝ=>(1:ℝ)) m:=contDiffAt_const
    rw [he,fun_iteratedFDeriv_add_apply (hc.of_le (by simp))
      ((hq.sub hell).of_le (by simp))]
    have hconst:iteratedFDeriv ℝ j (fun _:ℝ=>(1:ℝ)) m=0 := by
      obtain ⟨i,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : j≠0)
      simp only [iteratedFDeriv_succ_const,Pi.zero_apply]
    rw [hconst,zero_add]
  exact ⟨by rw [←hn 1 (by norm_num)];exact hb.1,
    by rw [←hn 2 (by norm_num)];convert hb.2 using 1 <;> ring⟩

end DepthPaper
