module

public import DepthPaper.TwoLevelAtomicCoordinates

@[expose] public section


/-! The actual coordinate differential is a continuous linear equivalence,
proved by differentiating the explicit smooth inverse in both directions. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 1400000

theorem twoLevelAtomicCoordinates_fderiv_bijective {r : ℕ} (v : TwoLevelAtomicPoint r)
    (hm : v.2.1≠0) : Function.Bijective (fderiv ℝ (twoLevelAtomicCoordinates (r:=r)) v) := by
  let T:=twoLevelAtomicCoordinates (r:=r)
  let I:=twoLevelAtomicInverse (r:=r)
  let L:=fderiv ℝ T v
  let J:=fderiv ℝ I (T v)
  have hTv : HasFDerivAt T L v:=(contDiff_twoLevelAtomicCoordinates r).differentiable (by simp) v |>.hasFDerivAt
  have hIv : HasFDerivAt I J (T v):=
    (contDiffAt_twoLevelAtomicInverse (T v) (by simpa only [T,twoLevelAtomicCoordinates_mass_sum] using hm)).differentiableAt (by simp) |>.hasFDerivAt
  have heL : (I∘T)=ᶠ[𝓝 v]id := by
    filter_upwards [((continuous_snd.fst : Continuous (fun v : TwoLevelAtomicPoint r=>v.2.1)).continuousAt).eventually_ne hm] with w hw
    exact twoLevelAtomicInverse_coordinates w hw
  have hL : J.comp L=ContinuousLinearMap.id ℝ (TwoLevelAtomicPoint r) := by
    exact (hIv.comp v hTv |>.congr_of_eventuallyEq heL.symm).unique (hasFDerivAt_id v)
  have hsum : Continuous (fun y : AtomicPoint (r+1)=>∑j,y.2 j):=
    continuous_finsetSum _ fun j _=>(continuous_apply j).comp continuous_snd
  have hmass : (∑j,(T v).2 j)≠0:=by simpa only [T,twoLevelAtomicCoordinates_mass_sum] using hm
  have heR : (T∘I)=ᶠ[𝓝 (T v)]id := by
    filter_upwards [hsum.continuousAt.eventually_ne hmass] with y hy
    exact twoLevelAtomicCoordinates_inverse y hy
  have hTiv : HasFDerivAt T L (I (T v)) := by
    change HasFDerivAt T L (twoLevelAtomicInverse (twoLevelAtomicCoordinates v))
    rw [twoLevelAtomicInverse_coordinates v hm]
    exact hTv
  have hR : L.comp J=ContinuousLinearMap.id ℝ (AtomicPoint (r+1)) := by
    exact (hTiv.comp (T v) hIv |>.congr_of_eventuallyEq heR.symm).unique (hasFDerivAt_id (T v))
  constructor
  · intro x y hxy
    have he:=congrArg J hxy
    change (J.comp L) x=(J.comp L) y at he
    simpa only [hL,ContinuousLinearMap.id_apply] using he
  · intro y
    refine ⟨J y,?_⟩
    change (L.comp J) y=y
    rw [hR]
    rfl

def twoLevelAtomicDerivativeEquivalence {r : ℕ} (v : TwoLevelAtomicPoint r)
    (hm : v.2.1≠0) : TwoLevelAtomicPoint r≃L[ℝ]AtomicPoint (r+1) :=
  ContinuousLinearEquiv.ofBijective (fderiv ℝ (twoLevelAtomicCoordinates (r:=r)) v)
    (LinearMap.ker_eq_bot.mpr (twoLevelAtomicCoordinates_fderiv_bijective v hm).1)
    (LinearMap.range_eq_top.mpr (twoLevelAtomicCoordinates_fderiv_bijective v hm).2)

@[simp] theorem twoLevelAtomicDerivativeEquivalence_apply {r : ℕ} (v : TwoLevelAtomicPoint r)
    (hm : v.2.1≠0) (w : TwoLevelAtomicPoint r) :
    twoLevelAtomicDerivativeEquivalence v hm w=fderiv ℝ twoLevelAtomicCoordinates v w := rfl

end DepthPaper
