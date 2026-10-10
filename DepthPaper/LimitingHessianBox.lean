module

public import DepthPaper.LimitingCorner
public import DepthPaper.HessianCoercivityNeighborhood
public import DepthPaper.NondegenerateChartContinuation

@[expose] public section


/-! The actual limiting atomic Hessian has a uniform quadratic margin
on a genuine common coordinate/mass box near every nondegenerate seed. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 64

def limitingHessianField (Ξ:AdmissibleCovariance) (r:ℕ) (w:AtomicPoint r×ℝ) :
    AtomicPoint r→L[ℝ] AtomicPoint r→L[ℝ] ℝ :=
  w.2⁻¹ • atomicHessianFamily (temperatureCovarianceFamily Ξ) r (w.2,w.1)

theorem limitingAtomicPhi_hessian_eq (Ξ:AdmissibleCovariance) {r:ℕ}
    (z:AtomicPoint r) (hz:IsAtomicPoint z) (m:ℝ) (hm:0 < m) :
    fderiv ℝ (fun y=>fderiv ℝ (fun w=>limitingAtomicPhi Ξ r (w,m)) y) z=
      limitingHessianField Ξ r (z,m) := by
  have he:(fun y=>fderiv ℝ (fun w=>limitingAtomicPhi Ξ r (w,m)) y)=ᶠ[𝓝 z]
      (fun y=>m⁻¹ • fderiv ℝ (atomicFunctionalExtension
        ((temperatureCovarianceFamily Ξ).covariance m) r) y) := by
    filter_upwards [(isOpen_atomic_domain r).mem_nhds hz] with y hy
    exact fderiv_limitingAtomicPhi_locations Ξ y hy m hm
  have hd:=((contDiffAt_atomicFunctionalExtension
    ((temperatureCovarianceFamily Ξ).covariance m) z hz).fderiv_right (m:=∞) (by simp)).differentiableAt
    (by norm_num)
  rw [he.fderiv_eq.trans (hd.hasFDerivAt.const_smul m⁻¹).fderiv]
  unfold limitingHessianField atomicHessianFamily
  rw [(temperatureCovarianceFamily Ξ).atomicGradientFamily_partial_hessian
    (by exact hm) z hz]

theorem continuousAt_limitingHessianField (Ξ:AdmissibleCovariance) {r:ℕ}
    (z:AtomicPoint r) (hz:IsAtomicPoint z) (m:ℝ) (hm:0 < m) :
    ContinuousAt (limitingHessianField Ξ r) (z,m) := by
  have hc : ContinuousAt (atomicHessianFamily (temperatureCovarianceFamily Ξ) r) (m,z) :=
    (temperatureCovarianceFamily Ξ).continuousAt_atomicHessianFamily hm z hz
  have hi : ContinuousAt (fun w:AtomicPoint r×ℝ=>(w.2,w.1)) (z,m) :=
    continuousAt_snd.prodMk continuousAt_fst
  have hs : ContinuousAt (fun w:AtomicPoint r×ℝ=>
      atomicHessianFamily (temperatureCovarianceFamily Ξ) r (w.2,w.1)) (z,m) :=
    ContinuousAt.comp (g:=atomicHessianFamily (temperatureCovarianceFamily Ξ) r)
      (f:=fun w:AtomicPoint r×ℝ=>(w.2,w.1)) hc hi
  exact (continuousAt_snd.inv₀ hm.ne').smul hs

theorem exists_limiting_hessian_box (Ξ:AdmissibleCovariance) {r:ℕ}
    (z:AtomicPoint r) (hz:IsAtomicPoint z) (hnd:Nondegenerate Ξ z hz)
    {qc:ℝ} (hcut:atomicLocation z (Fin.last r) < qc) :
    ∃ρ:ℝ,0 < ρ ∧ ∃δ:ℝ,δ∈Ioo (0:ℝ) 1 ∧ ∃κ:ℝ,0 < κ ∧
      ∀y∈closedBall z ρ,∀m∈Icc (1-δ) (1+δ),
        IsAtomicPoint y ∧ atomicLocation y (Fin.last r) < qc ∧ 0 < m ∧
          ∀v:AtomicPoint r,κ*‖v‖^2 ≤
            (fderiv ℝ (fun a=>fderiv ℝ (fun b=>limitingAtomicPhi Ξ r (b,m)) a) y v) v := by
  have hpos:∀v:AtomicPoint r,v≠0→0 < limitingHessianField Ξ r (z,1) v v := by
    rw [←limitingAtomicPhi_hessian_eq Ξ z hz 1 zero_lt_one]
    have hH:positiveAtomicHessian ((temperatureCovarianceFamily Ξ).covariance 1) z := by
      simpa only [temperatureCovarianceFamily_one] using hnd.2.2.2
    exact positive_limitingAtomicPhi_hessian Ξ z hz 1 zero_lt_one hH
  obtain ⟨κ,hκ,U,hU,hbase,hmargin⟩ := exists_bilinear_coercive_neighborhood
    (limitingHessianField Ξ r) (z,1) (continuousAt_limitingHessianField Ξ z hz 1 zero_lt_one) hpos
  let V:Set (AtomicPoint r×ℝ) := U∩
    (({y:AtomicPoint r|IsAtomicPoint y}∩{y|atomicLocation y (Fin.last r) < qc})×ˢIoo (0:ℝ) 2)
  have hV:IsOpen V := hU.inter (((isOpen_atomic_domain r).inter
    ((contDiff_atomicLocation (Fin.last r)).continuous.isOpen_preimage _ isOpen_Iio)).prod isOpen_Ioo)
  have hpV:(z,1)∈V := ⟨hbase,⟨hz,hcut⟩,by norm_num⟩
  obtain ⟨ε,hε,hεV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hpV)
  let ρ:ℝ := min (ε/4) (1/4)
  have hρ:0 < ρ := lt_min (by positivity) (by norm_num)
  have hρ1:ρ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hρε:ρ < ε := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨ρ,hρ,ρ,⟨hρ,hρ1⟩,κ,hκ,?_⟩
  intro y hy m hm
  have hdist:dist (y,m) (z,(1:ℝ)) < ε := by
    rw [Prod.dist_eq]
    apply max_lt
    · exact hy.trans_lt hρε
    · rw [Real.dist_eq]
      apply (abs_le.mpr (show -ρ ≤ m-1 ∧ m-1 ≤ ρ by
        constructor <;> linarith [hm.1,hm.2])).trans_lt hρε
  have hv: (y,m)∈V := hεV hdist
  refine ⟨hv.2.1.1,hv.2.1.2,hv.2.2.1,?_⟩
  intro v
  rw [limitingAtomicPhi_hessian_eq Ξ y hv.2.1.1 m hv.2.2.1]
  exact hmargin (y,m) hv.1 v

end DepthPaper
