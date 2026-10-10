module

public import GeneralDepthPaper.IntervalImplicitRoot
public import GeneralDepthPaper.IntervalFiberDomain

@[expose] public section


/-! A concrete open domain of monotone interval roots. Compact fibers give
the neighborhood uniformly in the endpoint coordinate, and the positive
partial derivative and endpoint signs are genuine open conditions. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GeneralDepthPaper
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
set_option maxHeartbeats 900000

theorem interval_partial_derivative_eq (G : E × ℝ → ℝ) (θ : E) (q : ℝ)
    (hG : ContDiffAt ℝ ∞ G (θ,q)) :
    deriv (fun r => G (θ,r)) q = fderiv ℝ G (θ,q) (0,1) := by
  have hd : HasDerivAt (fun r => G (θ,r)) (fderiv ℝ G (θ,q) (0,1)) q := by
    convert (hG.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt q
      ((hasDerivAt_const q θ).prodMk (hasDerivAt_id q)) using 1 <;> rfl
  exact hd.deriv

def intervalRootDomain (G : E × ℝ → ℝ) (U : Set (E × ℝ)) (a b : ℝ) : Set E :=
  compactFiberDomain (U ∩ {p | 0 < fderiv ℝ G p (0,1)}) (Icc a b) ∩
    {θ | G (θ,a) < 0 ∧ 0 < G (θ,b)}

theorem isOpen_intervalRootDomain (G : E × ℝ → ℝ) (U : Set (E × ℝ))
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) {a b : ℝ} (hab : a < b) :
    IsOpen (intervalRootDomain G U a b) := by
  let V : Set (E × ℝ) := U ∩ {p | 0 < fderiv ℝ G p (0,1)}
  have hd : ContinuousOn (fun p => fderiv ℝ G p (0,1)) U :=
    (hG.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const
  have hV : IsOpen V := hd.isOpen_inter_preimage hU isOpen_Ioi
  let O : Set E := compactFiberDomain V (Icc a b)
  have hO : IsOpen O := isOpen_compactFiberDomain V hV (Icc a b) isCompact_Icc
  have hca : ContinuousOn (fun θ => G (θ,a)) O := by
    apply hG.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
    intro θ hθ
    exact (hθ a (left_mem_Icc.mpr hab.le)).1
  have hcb : ContinuousOn (fun θ => G (θ,b)) O := by
    apply hG.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
    intro θ hθ
    exact (hθ b (right_mem_Icc.mpr hab.le)).1
  exact (hca.prodMk hcb).isOpen_inter_preimage hO (isOpen_Iio.prod isOpen_Ioi)

theorem intervalRootDomain_partial_pos (G : E × ℝ → ℝ) (U : Set (E × ℝ))
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) {a b : ℝ}
    {θ : E} (hθ : θ ∈ intervalRootDomain G U a b) {q : ℝ} (hq : q ∈ Icc a b) :
    0 < deriv (fun r => G (θ,r)) q := by
  have hp := hθ.1 q hq
  rw [interval_partial_derivative_eq G θ q (hG.contDiffAt (hU.mem_nhds hp.1))]
  exact hp.2

theorem intervalImplicitRoot_smooth_domain (G : E × ℝ → ℝ) (U : Set (E × ℝ))
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) {a b : ℝ} (hab : a < b) :
    ContDiffOn ℝ ∞ (intervalImplicitRoot G a b) (intervalRootDomain G U a b) := by
  apply contDiffOn_intervalImplicitRoot G hab U hU hG _
    (isOpen_intervalRootDomain G U hU hG hab)
  · intro θ hθ q hq
    exact (hθ.1 q hq).1
  · intro θ hθ
    exact hθ.2.1
  · intro θ hθ
    exact hθ.2.2
  · intro θ hθ q hq
    exact intervalRootDomain_partial_pos G U hU hG hθ hq

theorem intervalImplicitRoot_spec_domain (G : E × ℝ → ℝ) (U : Set (E × ℝ))
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) {a b : ℝ} (hab : a < b)
    {θ : E} (hθ : θ ∈ intervalRootDomain G U a b) :
    intervalImplicitRoot G a b θ ∈ Ioo a b ∧
      G (θ,intervalImplicitRoot G a b θ) = 0 := by
  have hslice : ∀ q ∈ Icc a b, ContDiffAt ℝ ∞ (fun r => G (θ,r)) q := by
    intro q hq
    exact (hG.contDiffAt (hU.mem_nhds (hθ.1 q hq).1)).comp q
      (contDiffAt_const.prodMk contDiffAt_id)
  have hd : ∀ q ∈ Icc a b, 0 < deriv (fun r => G (θ,r)) q := by
    intro q hq
    exact intervalRootDomain_partial_pos G U hU hG hθ hq
  exact intervalImplicitRoot_spec G hab θ hslice hθ.2.1 hθ.2.2 hd

end GeneralDepthPaper
