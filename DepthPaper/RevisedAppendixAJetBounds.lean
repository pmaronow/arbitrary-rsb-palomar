module

public import DepthPaper.RevisedAppendixAClosedJets

@[expose] public section

/-! Uniform bounds and Lipschitz stability for finite-order closed-domain
composition jets. The constants are chosen before the parameter domain and
before either finite-differentiability data family. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
namespace DepthPaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64
universe u
variable {E F G : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem revised_closed_composition_jet_estimates (ell : ℕ)
    {H : F → G} {s : Set F} (hH : BoundedSmoothOn H s) (hs : Convex ℝ s)
    (Djet : ℝ) (hD : 1 ≤ Djet) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : Set E) (f g : E → F)
      (hf : RevisedClosedCData ell D f) (hg : RevisedClosedCData ell D g)
      (hfm : MapsTo f D s) (hgm : MapsTo g D s),
      (∀j≤ell,∀x∈D,‖hf.jets x j‖≤Djet) →
      (∀j≤ell,∀x∈D,‖hg.jets x j‖≤Djet) →
      ∀δ:ℝ,0≤δ → (∀j≤ell,∀x∈D,‖hf.jets x j-hg.jets x j‖≤δ) →
      ∀j≤ell,∀x∈D,
        ‖(hf.comp H (fun x hx => hH.smooth _ (hfm hx))).jets x j‖≤C ∧
        ‖(hf.comp H (fun x hx => hH.smooth _ (hfm hx))).jets x j-
          (hg.comp H (fun x hx => hH.smooth _ (hgm hx))).jets x j‖≤C*δ := by
  classical
  choose b hb hbound using hH.bound
  choose a ha hlip using fun j => hH.jet_lipschitz hs j
  let R := ∑j∈Finset.range (ell+1),b j
  let A := ∑j∈Finset.range (ell+1),a j
  let P := ∑j : Fin (ell+1),(Fintype.card (OrderedFinpartition j):ℝ)
  have hR : 0 ≤ R := Finset.sum_nonneg (fun _ _ => hb _)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => ha _)
  have hP : 0 ≤ P := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hRb (j : ℕ) (hj : j≤ell) (y : F) (hy : y∈s) :
      ‖iteratedFDeriv ℝ j H y‖≤R :=
    (hbound j y hy).trans (Finset.single_le_sum (fun k _ => hb k) (Finset.mem_range.mpr (by omega)))
  have hAb (j : ℕ) (hj : j≤ell) (y z : F) (hy : y∈s) (hz : z∈s) :
      ‖iteratedFDeriv ℝ j H y-iteratedFDeriv ℝ j H z‖≤A*‖y-z‖ := by
    exact (hlip j z hz y hy).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun k _ => ha k) (Finset.mem_range.mpr (by omega))) (norm_nonneg _))
  have hPc (j : ℕ) (hj : j≤ell) : (Fintype.card (OrderedFinpartition j):ℝ)≤P := by
    exact Finset.single_le_sum (fun k (_:k∈(Finset.univ:Finset (Fin (ell+1)))) => (show (0:ℝ) ≤ (Fintype.card (OrderedFinpartition k):ℝ) by positivity))
      (Finset.mem_univ (⟨j,by omega⟩:Fin (ell+1)))
  let C := P*(R+(R*ell+A))*Djet^ell
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro D f g hf hg hfm hgm hfj hgj δ hδ hdj j hj x hx
  have hfx := hfm hx
  have hgx := hgm hx
  have hz : ‖f x-g x‖≤δ := by
    have H0 := hdj 0 (by omega) x hx
    rw [hf.zero x hx,hg.zero x hx] at H0
    change ‖(continuousMultilinearCurryFin0 ℝ E F).symm (f x)-
      (continuousMultilinearCurryFin0 ℝ E F).symm (g x)‖≤δ at H0
    simpa only [←map_sub,LinearIsometryEquiv.norm_map] using H0
  have hv (c : OrderedFinpartition j) :
      ‖(ftaylorSeries ℝ H (f x)).compAlongOrderedFinpartition (hf.jets x) c‖ ≤ R*Djet^ell := by
    apply (c.norm_compAlongOrderedFinpartition_le _ _).trans
    have hp : (∏ i:Fin c.length,‖hf.jets x (c.partSize i)‖)≤Djet^c.length := by
      simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
        Finset.prod_le_prod₀ (s := Finset.univ) (fun _ _ => norm_nonneg _) (fun i _ => hfj _ ((c.partSize_le i).trans hj) x hx)
    exact (mul_le_mul (hRb _ (c.length_le.trans hj) _ hfx) hp (by positivity) hR).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (c.length_le.trans hj)) hR)
  have hd (c : OrderedFinpartition j) :
      ‖(ftaylorSeries ℝ H (f x)).compAlongOrderedFinpartition (hf.jets x) c-
        (ftaylorSeries ℝ H (g x)).compAlongOrderedFinpartition (hg.jets x) c‖ ≤
      (R*ell+A)*Djet^ell*δ := by
    let p := fun i:Fin c.length => hf.jets x (c.partSize i)
    let q := fun i:Fin c.length => hg.jets x (c.partSize i)
    have hp : ‖p‖≤Djet := (pi_norm_le_iff_of_nonneg (zero_le_one.trans hD)).mpr
      (fun i => hfj _ ((c.partSize_le i).trans hj) x hx)
    have hq : ‖q‖≤Djet := (pi_norm_le_iff_of_nonneg (zero_le_one.trans hD)).mpr
      (fun i => hgj _ ((c.partSize_le i).trans hj) x hx)
    have hpq : ‖p-q‖≤δ := (pi_norm_le_iff_of_nonneg hδ).mpr
      (fun i => hdj _ ((c.partSize_le i).trans hj) x hx)
    have hqprod : (∏ i:Fin c.length,‖q i‖)≤Djet^ell := by
      apply (show (∏ i:Fin c.length,‖q i‖)≤Djet^c.length from by
        simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
          Finset.prod_le_prod₀ (s := Finset.univ) (fun _ _ => norm_nonneg _) (fun i _ => hgj _ ((c.partSize_le i).trans hj) x hx)).trans
      exact pow_le_pow_right₀ hD (c.length_le.trans hj)
    have houter := (hAb _ (c.length_le.trans hj) (f x) (g x) hfx hgx).trans
      (mul_le_mul_of_nonneg_left hz hA)
    have hpow : max ‖p‖ ‖q‖ ^ (c.length-1)≤Djet^ell := by
      exact (pow_le_pow_left₀ (by positivity) (max_le hp hq) _).trans
        (pow_le_pow_right₀ hD (by have hc := c.length_le; omega : c.length-1≤ell))
    apply (c.norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le
      (iteratedFDeriv ℝ c.length H (f x)) (iteratedFDeriv ℝ c.length H (g x)) p q).trans
    have he :
        ‖iteratedFDeriv ℝ c.length H (f x)‖*c.length*max ‖p‖ ‖q‖^(c.length-1)*‖p-q‖+
          ‖iteratedFDeriv ℝ c.length H (f x)-iteratedFDeriv ℝ c.length H (g x)‖*
            (∏ i:Fin c.length,‖q i‖) ≤ R*ell*Djet^ell*δ+(A*δ)*Djet^ell := by
      gcongr
      · exact hRb _ (c.length_le.trans hj) _ hfx
      · exact_mod_cast c.length_le.trans hj
    exact he.trans_eq (by ring)
  constructor
  · change ‖(ftaylorSeries ℝ H (f x)).taylorComp (hf.jets x) j‖≤C
    unfold FormalMultilinearSeries.taylorComp
    apply (norm_sum_le _ _).trans
    have Hs := Finset.sum_le_sum (fun c (_:c∈(Finset.univ:Finset (OrderedFinpartition j))) => hv c)
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at Hs
    apply Hs.trans
    dsimp only [C]
    have hh : R≤R+(R*ell+A) := by linarith [mul_nonneg hR (Nat.cast_nonneg ell)]
    calc
      (Fintype.card (OrderedFinpartition j):ℝ)*(R*Djet^ell) =
          (Fintype.card (OrderedFinpartition j):ℝ)*R*Djet^ell := by ring
      _ ≤ P*(R+(R*ell+A))*Djet^ell :=
        mul_le_mul_of_nonneg_right (mul_le_mul (hPc j hj) hh hR hP) (by positivity)
  · change ‖(ftaylorSeries ℝ H (f x)).taylorComp (hf.jets x) j-
      (ftaylorSeries ℝ H (g x)).taylorComp (hg.jets x) j‖≤C*δ
    unfold FormalMultilinearSeries.taylorComp
    rw [←Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    have Hs := Finset.sum_le_sum (fun c (_:c∈(Finset.univ:Finset (OrderedFinpartition j))) => hd c)
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at Hs
    apply Hs.trans
    dsimp only [C]
    have hh : R*ell+A≤R+(R*ell+A) := by linarith
    calc
      (Fintype.card (OrderedFinpartition j):ℝ)*((R*ell+A)*Djet^ell*δ) =
          (Fintype.card (OrderedFinpartition j):ℝ)*(R*ell+A)*Djet^ell*δ := by ring
      _ ≤ P*(R+(R*ell+A))*Djet^ell*δ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul (hPc j hj) hh (by positivity) hP) (by positivity)) hδ

end DepthPaper
