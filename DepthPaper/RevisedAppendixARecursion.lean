module

public import DepthPaper.RevisedAppendixARecursionOutputs
public import DepthPaper.RevisedAppendixAJetBounds

@[expose] public section

/-! The finite differentiability and stability assertion of Appendix A.2.
The input needs only C^ell derivatives in the interior and continuous
extensions to the closed parameter domain. Bounds use the printed sum
norm and all ordered coordinate derivatives. Constants precede the
parameter domain and both data families. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
namespace DepthPaper
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 64

def revisedRecursionDatumSumNorm {L : ℕ} (p : ColeHopfRecursionParameter L)
    (i : Fin L) : ℝ := |(p.1 i).1|+|(p.1 i).2|+terminalSumNorm p.2

theorem revised_norm_le_recursionDatumSumNorm {L : ℕ} (hL : 0<L)
    (p : ColeHopfRecursionParameter L) (C : ℝ) (hC : 0≤C)
    (hp : ∀i,revisedRecursionDatumSumNorm p i≤C) : ‖p‖≤C := by
  have ht := norm_le_terminalSumNorm p.2
  have hs := (norm_nonneg p.2).trans ht
  rw [Prod.norm_def]
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg hC).mpr
    intro i
    rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
    have hi := hp i
    dsimp only [revisedRecursionDatumSumNorm] at hi
    exact max_le (by linarith [abs_nonneg (p.1 i).2])
      (by linarith [abs_nonneg (p.1 i).1])
  · have hi := hp ⟨0,hL⟩
    dsimp only [revisedRecursionDatumSumNorm] at hi
    linarith [abs_nonneg (p.1 ⟨0,hL⟩).1,abs_nonneg (p.1 ⟨0,hL⟩).2]

theorem revised_norm_coordinate_jet_bound (d ell L : ℕ) (hL : 0<L)
    (M : (Fin d→ℝ)[×ell]→L[ℝ] ColeHopfRecursionParameter L)
    (C : ℝ) (hC : 0≤C)
    (hb : ∀w:Fin ell→Fin d,∀i,
      revisedRecursionDatumSumNorm (M (fun k=>revisedParameterAxis d (w k))) i≤C) :
    ‖M‖≤(d:ℝ)^ell*C :=
  revised_norm_coordinate_multilinear_le d ell M C hC
    (fun w=>revised_norm_le_recursionDatumSumNorm hL _ C hC (hb w))

theorem revised_norm_coordinate_evaluation_le {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (d j : ℕ)
    (M : (Fin d→ℝ)[×j]→L[ℝ] F) (w : Fin j→Fin d) :
    ‖M (fun k=>revisedParameterAxis d (w k))‖≤‖M‖ := by
  apply (M.le_opNorm _).trans
  apply mul_le_of_le_one_right (norm_nonneg _)
  apply Finset.prod_le_one₀ (fun _ _=>norm_nonneg _)
  intro k _
  simp [revisedParameterAxis,Pi.norm_single]

theorem revised_recursion_data_mem_ball {d ell L : ℕ} (hL : 0<L)
    {D : Set (Fin d→ℝ)} {f : (Fin d→ℝ)→ ColeHopfRecursionParameter L}
    (hf : RevisedClosedCData ell D f) (ahi Vlo Vhi C0 : ℝ) (hC0 : 0≤C0)
    (ha : ∀x∈D,∀i,‖((f x).1 i).1‖≤ahi)
    (hV : ∀x∈D,∀i,((f x).1 i).2∈Icc Vlo Vhi)
    (hb : ∀j≤ell,∀x∈D,∀w:Fin j→Fin d,∀i,
      revisedRecursionDatumSumNorm (hf.jets x j (fun k=>revisedParameterAxis d (w k))) i≤C0) :
    MapsTo f D (coleHopfRecursionBall L ahi Vlo Vhi C0) := by
  intro x hx
  refine ⟨fun i=>⟨ha x hx i,(hV x hx i).1,(hV x hx i).2⟩,?_⟩
  have hi := hb 0 (by omega) x hx (fun k=>Fin.elim0 k) ⟨0,hL⟩
  rw [hf.zero x hx] at hi
  simp only [iteratedFDeriv_zero_apply] at hi
  have hn := norm_le_terminalSumNorm (f x).2
  dsimp only [revisedRecursionDatumSumNorm] at hi
  linarith [abs_nonneg ((f x).1 ⟨0,hL⟩).1,abs_nonneg ((f x).1 ⟨0,hL⟩).2]

/-- Actual all-intermediate recursion jets, including uniform sum-norm
bounds and perturbation estimates on an arbitrary closed data domain.
This stronger form does not need compactness or convexity of that domain. -/
theorem revised_finite_recursion (L ell d : ℕ) (hL : 0<L)
    (ahi Vlo Vhi C0 : ℝ) (hA : 0≤ahi) (hVlo : 0<Vlo)
    (hVrange : Vlo≤Vhi) (hC0 : 0≤C0) :
    ∃C:ℝ,0≤C ∧ ∀(D:Set (Fin d→ℝ))
      (f g:(Fin d→ℝ)→ ColeHopfRecursionParameter L)
      (hf:RevisedClosedCData ell D f) (hg:RevisedClosedCData ell D g),
      (∀x∈D,∀i,‖((f x).1 i).1‖≤ahi) →
      (∀x∈D,∀i,‖((g x).1 i).1‖≤ahi) →
      (∀x∈D,∀i,((f x).1 i).2∈Icc Vlo Vhi) →
      (∀x∈D,∀i,((g x).1 i).2∈Icc Vlo Vhi) →
      (∀x∈D,‖terminalJet (f x).2 0‖≤1) →
      (∀x∈D,‖terminalJet (g x).2 0‖≤1) →
      (∀j≤ell,∀x∈D,∀w:Fin j→Fin d,∀i,
        revisedRecursionDatumSumNorm (hf.jets x j (fun k=>revisedParameterAxis d (w k))) i≤C0) →
      (∀j≤ell,∀x∈D,∀w:Fin j→Fin d,∀i,
        revisedRecursionDatumSumNorm (hg.jets x j (fun k=>revisedParameterAxis d (w k))) i≤C0) →
      ∀ε:ℝ,0≤ε →
      (∀j≤ell,∀x∈D,∀w:Fin j→Fin d,∀i,
        revisedRecursionDatumSumNorm ((hf.jets x j-hg.jets x j)
          (fun k=>revisedParameterAxis d (w k))) i≤ε) →
      ∃(uf:RevisedClosedCData ell D (revisedColeHopfOutputs L∘f))
        (ug:RevisedClosedCData ell D (revisedColeHopfOutputs L∘g)),
        Nonempty (RevisedClosedCData ell D (fun x=>terminalValue (coleHopfRecursion L (f x)) 0)) ∧
        (∀x∈D,∀i,LipschitzWith 1 (terminalValue (revisedColeHopfOutputs L (f x) i))) ∧
        (∀x∈D,∀i,LipschitzWith 1 (terminalValue (revisedColeHopfOutputs L (g x) i))) ∧
        ∀j≤ell,∀x∈D,∀w:Fin j→Fin d,∀i,
          terminalSumNorm ((uf.jets x j (fun k=>revisedParameterAxis d (w k))) i)≤C ∧
          terminalSumNorm (((uf.jets x j-ug.jets x j)
            (fun k=>revisedParameterAxis d (w k))) i)≤C*ε := by
  let A : ℝ := (max 1 (d:ℝ))^ell
  have hA1 : 1≤A := one_le_pow₀ (le_max_left _ _)
  have hA0 : 0≤A := zero_le_one.trans hA1
  have hdj (j:ℕ) (hj:j≤ell) : (d:ℝ)^j≤A := by
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) (le_max_right _ _) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) hj)
  let R := 1+A*C0
  have hR : 1≤R := by dsimp only [R]; nlinarith
  let H := revisedColeHopfOutputs L
  let s := coleHopfRecursionBall L ahi Vlo Vhi C0
  have hH : BoundedSmoothOn H s :=
    revised_boundedSmoothOn_coleHopfOutputs L ahi Vlo Vhi C0 hA hVlo hVrange hC0
  obtain ⟨B,hB,hest⟩ := revised_closed_composition_jet_estimates
    (E:=Fin d→ℝ) ell hH (convex_coleHopfRecursionBall ..) R hR
  refine ⟨4*B*A,by positivity,?_⟩
  intro D f g hf hg haf hag hVf hVg hLf hLg hbf hbg ε hε hdiff
  have hfm := revised_recursion_data_mem_ball hL hf ahi Vlo Vhi C0 hC0 haf hVf hbf
  have hgm := revised_recursion_data_mem_ball hL hg ahi Vlo Vhi C0 hC0 hag hVg hbg
  have hfj (j:ℕ) (hj:j≤ell) (x:Fin d→ℝ) (hx:x∈D) : ‖hf.jets x j‖≤R := by
    apply (revised_norm_coordinate_jet_bound d j L hL _ C0 hC0 (hbf j hj x hx)).trans
    exact (mul_le_mul_of_nonneg_right (hdj j hj) hC0).trans (by dsimp only [R]; linarith)
  have hgj (j:ℕ) (hj:j≤ell) (x:Fin d→ℝ) (hx:x∈D) : ‖hg.jets x j‖≤R := by
    apply (revised_norm_coordinate_jet_bound d j L hL _ C0 hC0 (hbg j hj x hx)).trans
    exact (mul_le_mul_of_nonneg_right (hdj j hj) hC0).trans (by dsimp only [R]; linarith)
  have hd (j:ℕ) (hj:j≤ell) (x:Fin d→ℝ) (hx:x∈D) : ‖hf.jets x j-hg.jets x j‖≤A*ε :=
    (revised_norm_coordinate_jet_bound d j L hL _ ε hε (hdiff j hj x hx)).trans
      (mul_le_mul_of_nonneg_right (hdj j hj) hε)
  let uf := hf.comp H (fun x hx=>hH.smooth _ (hfm hx))
  let ug := hg.comp H (fun x hx=>hH.smooth _ (hgm hx))
  refine ⟨uf,ug,?_,?_,?_,?_⟩
  · let ev : (Fin (L+1)→TerminalSpace)→L[ℝ] ℝ :=
      (terminalEvalCLM 0).comp (ContinuousLinearMap.proj 0)
    have hc := uf.comp ev (fun _ _=>ev.contDiff.contDiffAt)
    have he : (ev∘(H∘f))=(fun x=>terminalValue (coleHopfRecursion L (f x)) 0) := by
      funext x
      simp [ev,H,Function.comp_def]
    rw [he] at hc
    exact ⟨hc⟩
  · intro x hx
    exact revisedColeHopfOutputs_one_lipschitz L (f x)
      (fun i=>hVlo.le.trans (hVf x hx i).1) (hLf x hx)
  · intro x hx
    exact revisedColeHopfOutputs_one_lipschitz L (g x)
      (fun i=>hVlo.le.trans (hVg x hx i).1) (hLg x hx)
  · intro j hj x hx w i
    have he := hest D f g hf hg hfm hgm hfj hgj (A*ε) (mul_nonneg hA0 hε) hd j hj x hx
    have hv : ‖uf.jets x j (fun k=>revisedParameterAxis d (w k)) i‖≤B :=
      (norm_le_pi_norm _ i).trans ((revised_norm_coordinate_evaluation_le d j _ w).trans he.1)
    have hdv : ‖(uf.jets x j-ug.jets x j) (fun k=>revisedParameterAxis d (w k)) i‖≤B*(A*ε) :=
      (norm_le_pi_norm _ i).trans ((revised_norm_coordinate_evaluation_le d j _ w).trans he.2)
    constructor
    · exact (terminalSumNorm_le_four_norm _).trans
        ((mul_le_mul_of_nonneg_left hv (by norm_num)).trans (by nlinarith))
    · exact (terminalSumNorm_le_four_norm _).trans
        ((mul_le_mul_of_nonneg_left hdv (by norm_num)).trans_eq (by ring))

/-- The printed positive parameter ranges of A.2. Each of the three input
differences may be bounded by epsilon separately; the constant absorbs
the finite sum and is independent of the closed parameter domain. -/
theorem revised_appendix_a_2 (L ell d : ℕ) (hL : 1≤L)
    (alo ahi Vlo Vhi C0 : ℝ) (halo : 0<alo) (ha : alo≤ahi)
    (hVlo : 0<Vlo) (hVrange : Vlo≤Vhi) :
    ∃C:ℝ,0≤C ∧ ∀(D:Set (Fin d→ℝ))
      (f g:(Fin d→ℝ)→ ColeHopfRecursionParameter L)
      (hf:RevisedClosedCData ell D f) (hg:RevisedClosedCData ell D g),
      (∀x∈D,∀i,((f x).1 i).1∈Icc alo ahi) →
      (∀x∈D,∀i,((g x).1 i).1∈Icc alo ahi) →
      (∀x∈D,∀i,((f x).1 i).2∈Icc Vlo Vhi) →
      (∀x∈D,∀i,((g x).1 i).2∈Icc Vlo Vhi) →
      (∀x∈D,‖terminalJet (f x).2 0‖≤1) →
      (∀x∈D,‖terminalJet (g x).2 0‖≤1) →
      (∀j≤ell,∀x∈D,∀w:Fin j→Fin d,∀i,
        |((hf.jets x j (fun k=>revisedParameterAxis d (w k))).1 i).1|+
        |((hf.jets x j (fun k=>revisedParameterAxis d (w k))).1 i).2|+
        terminalSumNorm (hf.jets x j (fun k=>revisedParameterAxis d (w k))).2≤C0) →
      (∀j≤ell,∀x∈D,∀w:Fin j→Fin d,∀i,
        |((hg.jets x j (fun k=>revisedParameterAxis d (w k))).1 i).1|+
        |((hg.jets x j (fun k=>revisedParameterAxis d (w k))).1 i).2|+
        terminalSumNorm (hg.jets x j (fun k=>revisedParameterAxis d (w k))).2≤C0) →
      ∀ε:ℝ,0≤ε →
      (∀j≤ell,∀x∈D,∀w:Fin j→Fin d,∀i,
        |(((hf.jets x j-hg.jets x j) (fun k=>revisedParameterAxis d (w k))).1 i).1|≤ε ∧
        |(((hf.jets x j-hg.jets x j) (fun k=>revisedParameterAxis d (w k))).1 i).2|≤ε ∧
        terminalSumNorm ((hf.jets x j-hg.jets x j) (fun k=>revisedParameterAxis d (w k))).2≤ε) →
      ∃(uf:RevisedClosedCData ell D (revisedColeHopfOutputs L∘f))
        (ug:RevisedClosedCData ell D (revisedColeHopfOutputs L∘g)),
        Nonempty (RevisedClosedCData ell D (fun x=>terminalValue (coleHopfRecursion L (f x)) 0)) ∧
        (∀x∈D,∀i,LipschitzWith 1 (terminalValue (revisedColeHopfOutputs L (f x) i))) ∧
        (∀x∈D,∀i,LipschitzWith 1 (terminalValue (revisedColeHopfOutputs L (g x) i))) ∧
        ∀j≤ell,∀x∈D,∀w:Fin j→Fin d,∀i,
          terminalSumNorm ((uf.jets x j (fun k=>revisedParameterAxis d (w k))) i)≤C ∧
          terminalSumNorm (((uf.jets x j-ug.jets x j)
            (fun k=>revisedParameterAxis d (w k))) i)≤C*ε := by
  obtain ⟨C,hC,h⟩ := revised_finite_recursion L ell d (by omega) ahi Vlo Vhi
    (max C0 0) (halo.le.trans ha) hVlo hVrange (le_max_right _ _)
  refine ⟨3*C,by positivity,?_⟩
  intro D f g hf hg haf hag hVf hVg hLf hLg hbf hbg ε hε hdiff
  have habs (f:(Fin d→ℝ)→ ColeHopfRecursionParameter L)
      (hh:∀x∈D,∀i,((f x).1 i).1∈Icc alo ahi) :
      ∀x∈D,∀i,‖((f x).1 i).1‖≤ahi := by
    intro x hx i
    rw [Real.norm_of_nonneg (halo.le.trans (hh x hx i).1)]
    exact (hh x hx i).2
  obtain ⟨uf,ug,he,huf,hug,hb⟩ := h D f g hf hg (habs f haf) (habs g hag)
    hVf hVg hLf hLg
    (fun j hj x hx w i=>(hbf j hj x hx w i).trans (le_max_left _ _))
    (fun j hj x hx w i=>(hbg j hj x hx w i).trans (le_max_left _ _))
    (3*ε) (by positivity) (fun j hj x hx w i=>by
      have hi := hdiff j hj x hx w i
      change _+_+_≤3*ε
      linarith [hi.1,hi.2.1,hi.2.2])
  refine ⟨uf,ug,he,huf,hug,?_⟩
  intro j hj x hx w i
  have hi := hb j hj x hx w i
  exact ⟨hi.1.trans (by nlinarith),hi.2.trans_eq (by ring)⟩

end DepthPaper
