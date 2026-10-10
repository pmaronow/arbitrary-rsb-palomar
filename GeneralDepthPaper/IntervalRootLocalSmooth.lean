module

public import GeneralDepthPaper.IntervalRootDomain

@[expose] public section


/-! A compact fiber needs a common finite-order tube for uniqueness;
all-order smoothness of its actual root comes from the pointwise IFT. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 1700000
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem intervalRoot_eventually_positive_partial (G:E×ℝ→ℝ) {a b:ℝ} {θ:E}
    (hG:∀q∈Icc a b,ContDiffAt ℝ ∞ G (θ,q))
    (hpos:∀q∈Icc a b,0 < fderiv ℝ G (θ,q) (0,1)) :
    ∀ᶠu in 𝓝 θ,∀q∈Icc a b,DifferentiableAt ℝ G (u,q) ∧
      0 < fderiv ℝ G (u,q) (0,1) := by
  let S:Set (E×ℝ):={w|DifferentiableAt ℝ G w ∧ 0 < fderiv ℝ G w (0,1)}
  have hpoint (q:ℝ) (hq:q∈Icc a b):S∈𝓝 (θ,q) := by
    have hd:∀ᶠw in 𝓝 (θ,q),DifferentiableAt ℝ G w := by
      have hh:=((hG q hq).of_le (show (1:ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)
      exact hh.mono (fun _ hw=>hw.differentiableAt (by simp))
    have hc:ContinuousAt (fun w:E×ℝ=>fderiv ℝ G w (0,1)) (θ,q) :=
      ((hG q hq).fderiv_right (m:=∞) (by simp)).continuousAt.clm_apply continuousAt_const
    filter_upwards [hd,hc.eventually (isOpen_Ioi.mem_nhds (hpos q hq))] with w hw hp
    exact ⟨hw,hp⟩
  have htube:S∈𝓝 θ ×ˢnhdsSet (Icc a b):=
    isCompact_Icc.mem_prod_nhdsSet_of_forall
      (fun q hq=>by simpa only [←nhds_prod_eq] using hpoint q hq)
  obtain ⟨U,hU,V,hV,hUV⟩:=Filter.mem_prod_iff.mp htube
  filter_upwards [hU] with u hu q hq
  exact hUV ⟨hu,subset_of_mem_nhdsSet hV hq⟩

theorem intervalImplicitRoot_local_smooth_spec (G:E×ℝ→ℝ) {a b:ℝ}
    (hab:a < b) (θ:E)
    (hG:∀q∈Icc a b,ContDiffAt ℝ ∞ G (θ,q))
    (hpos:∀q∈Icc a b,0 < fderiv ℝ G (θ,q) (0,1))
    (hq:intervalImplicitRoot G a b θ∈Ioo a b)
    (hz:G (θ,intervalImplicitRoot G a b θ)=0) :
    ContDiffAt ℝ ∞ (intervalImplicitRoot G a b) θ ∧
      ∀ᶠu in 𝓝 θ,intervalImplicitRoot G a b u∈Ioo a b ∧
        G (u,intervalImplicitRoot G a b u)=0 := by
  classical
  let q:=intervalImplicitRoot G a b θ
  have hqc:q∈Icc a b:=⟨hq.1.le,hq.2.le⟩
  have hg:=hG q hqc
  let L:ℝ→L[ℝ]ℝ:=fderiv ℝ G (θ,q) ∘L ContinuousLinearMap.inr ℝ E ℝ
  have hL:L 1≠0 := (hpos q hqc).ne'
  let e:ℝ≃L[ℝ]ℝ:=ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (L 1) hL)
  have he:L=(e:ℝ→L[ℝ]ℝ) := by
    apply ContinuousLinearMap.ext
    intro r
    calc
      L r=L (r • (1:ℝ)) := by simp
      _=r*L 1 := by rw [map_smul];rfl
      _=e r := by simp [e]
  have hinv:L.IsInvertible := by rw [he];exact ContinuousLinearMap.isInvertible_equiv
  let w:=hg.implicitFunction (by simp) hinv
  have hws:ContDiffAt ℝ ∞ w θ:=hg.contDiffAt_implicitFunction (by simp) hinv
  have hw0:w θ=q:=hg.implicitFunction_apply_self (by simp) hinv
  have hwz:∀ᶠu in 𝓝 θ,G (u,w u)=0 := by
    filter_upwards [hg.eventually_apply_implicitFunction (by simp) hinv] with u hu
    exact hu.trans hz
  have hwb:∀ᶠu in 𝓝 θ,w u∈Ioo a b :=
    hws.continuousAt.eventually (isOpen_Ioo.mem_nhds (hw0.symm ▸ hq))
  have H:∀ᶠu in 𝓝 θ,intervalImplicitRoot G a b u=w u ∧
      intervalImplicitRoot G a b u∈Ioo a b ∧ G (u,intervalImplicitRoot G a b u)=0 := by
    filter_upwards [intervalRoot_eventually_positive_partial G hG hpos,hwz,hwb]
      with u hpartial hwzu hwbu
    have hslice (q:ℝ) (hq:q∈Icc a b):
        HasDerivAt (fun r=>G (u,r)) (fderiv ℝ G (u,q) (0,1)) q := by
      convert (hpartial q hq).1.hasFDerivAt.comp_hasDerivAt q
        ((hasDerivAt_const q u).prodMk (hasDerivAt_id q)) using 1 <;> rfl
    have hmono:StrictMonoOn (fun r=>G (u,r)) (Icc a b) := by
      apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
        (fun q hq=>(hslice q hq).continuousAt.continuousWithinAt)
      · intro q hq
        rw [interior_Icc] at hq
        exact (hslice q ⟨hq.1.le,hq.2.le⟩).hasDerivWithinAt
      · intro q hq
        rw [interior_Icc] at hq
        exact (hpartial q ⟨hq.1.le,hq.2.le⟩).2
    have hex:∃r∈Ioo a b,G (u,r)=0:=⟨w u,hwbu,hwzu⟩
    have hsel:intervalImplicitRoot G a b u∈Ioo a b ∧ G (u,intervalImplicitRoot G a b u)=0 := by
      simpa only [intervalImplicitRoot,dite_eq_left hex] using hex.choose_spec
    have heq:=hmono.injOn ⟨hsel.1.1.le,hsel.1.2.le⟩ ⟨hwbu.1.le,hwbu.2.le⟩
      (hsel.2.trans hwzu.symm)
    exact ⟨heq,hsel⟩
  exact ⟨hws.congr_of_eventuallyEq (H.mono fun _ hu=>hu.1),H.mono (fun _ hu=>hu.2)⟩

end GeneralDepthPaper
