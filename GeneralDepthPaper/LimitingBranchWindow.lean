module

public import GeneralDepthPaper.LimitingHessianBox

@[expose] public section


/-! A genuine common mass window, coordinate ball, and smooth stationary
branch selected from the actual nondegenerate Parisi minimizer. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 64

theorem exists_limiting_branch_window (Ξ:AdmissibleCovariance) {r:ℕ}
    (z:AtomicPoint r) (hz:IsAtomicPoint z) (hnd:Nondegenerate Ξ z hz) :
    ∃a:ℝ,a∈Ioo (0:ℝ) 1 ∧ ∃ρ:ℝ,0 < ρ ∧ ∃κ:ℝ,0 < κ ∧
    ∃m0:ℝ,m0∈Ioo (0:ℝ) 1 ∧ ∃c:ℝ,0 < c ∧
    ∃V:Set ℝ,IsOpen V ∧ Icc m0 1⊆V ∧ ∃zF:ℝ→AtomicPoint r,
      zF 1=z ∧ ContDiffOn ℝ ∞ zF V ∧
      (∀m∈V,∃hmz:IsAtomicPoint (zF m),
        Nondegenerate ((temperatureCovarianceFamily Ξ).covariance m) (zF m) hmz) ∧
      (∀m∈Icc m0 1,dist (zF m) z < ρ/2 ∧
        ∃hmz:IsAtomicPoint (zF m),
          Nondegenerate ((temperatureCovarianceFamily Ξ).covariance m) (zF m) hmz ∧
          fderiv ℝ (fun y=>limitingAtomicPhi Ξ r (y,m)) (zF m)=0 ∧
          ContDiffAt ℝ ∞ (scaledThermodynamicPressure Ξ.toEvenMixture) m ∧
          ContDiffAt ℝ ∞ (pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture)) m ∧
          deriv (pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture)) m ≤ -2*c) ∧
      (∀y∈closedBall z ρ,∀m∈Icc m0 1,
        IsAtomicPoint y ∧ atomicLocation y (Fin.last r) < a ∧
        ∀v:AtomicPoint r,κ*‖v‖^2 ≤
          (fderiv ℝ (fun u=>fderiv ℝ (fun w=>limitingAtomicPhi Ξ r (w,m)) u) y v) v) := by
  let a:ℝ := (max 0 (atomicLocation z (Fin.last r))+1)/2
  have ha:Ioo (0:ℝ) 1 a := by
    have hlast:=hz.2.1
    constructor <;> dsimp only [a] <;> nlinarith [le_max_left (0:ℝ) (atomicLocation z (Fin.last r)),
      le_max_right (0:ℝ) (atomicLocation z (Fin.last r)),
      max_lt (show (0:ℝ)<1 by norm_num) hlast]
  have hcut:atomicLocation z (Fin.last r) < a := by
    dsimp only [a]
    have hlast:=hz.2.1
    have hmax:max 0 (atomicLocation z (Fin.last r)) < 1 := max_lt (by norm_num) hlast
    nlinarith [le_max_right (0:ℝ) (atomicLocation z (Fin.last r))]
  obtain ⟨ρ,hρ,δ,hδ,κ,hκ,hbox⟩:=exists_limiting_hessian_box Ξ z hz hnd hcut
  let F:=temperatureCovarianceFamily Ξ
  have hbase:Nondegenerate (F.covariance 1) z hz := by
    simpa only [F,temperatureCovarianceFamily_one] using hnd
  obtain ⟨V,hV,h1V,hVD,zF,hvalue,hsm,hdata⟩:=F.nondegenerate_stability
    (θ:=1) (by norm_num [F,temperatureCovarianceFamily]) z hz hbase
  obtain ⟨Vp,hVp,h1Vp,hVpD,hP⟩:=exists_smooth_temperature_pressure Ξ z hz hnd
  obtain ⟨mc,hmc,c,hc,zc,_,_,hcorner,_,_⟩:=limiting_corner Ξ z hz hnd
  have hclose:∀ᶠm in 𝓝 (1:ℝ),dist (zF m) z < ρ/2 := by
    have hcont:ContinuousAt zF 1 := (hsm.contDiffAt (hV.mem_nhds h1V)).continuousAt
    have hdist:ContinuousAt (fun m=>dist (zF m) z) 1 := hcont.dist continuousAt_const
    have hlt:dist (zF 1) z < ρ/2 := by rw [hvalue,dist_self];positivity
    exact hdist.eventually (eventually_lt_nhds hlt)
  have hnear:∀ᶠm in 𝓝 (1:ℝ),m∈V ∧ m∈Vp ∧ dist (zF m) z < ρ/2 ∧
      m∈Ioo (1-δ) (1+δ) ∧ mc < m := by
    filter_upwards [hV.mem_nhds h1V,hVp.mem_nhds h1Vp,hclose,
      isOpen_Ioo.mem_nhds (show (1:ℝ)∈Ioo (1-δ) (1+δ) by constructor <;> linarith [hδ.1]),
      isOpen_Ioi.mem_nhds (show mc < (1:ℝ) from hmc.2)] with m hm hmP hmclose hmδ hmcore
    exact ⟨hm,hmP,hmclose,hmδ,hmcore⟩
  obtain ⟨d,hd,hball⟩:=Metric.mem_nhds_iff.mp hnear
  let τ:ℝ:=min (d/2) (1/2)
  have hτ:0 < τ := lt_min (by positivity) (by norm_num)
  have hτ1:τ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hτd:τ < d := (min_le_left _ _).trans_lt (by linarith)
  let m0:ℝ:=1-τ
  have hm0:m0∈Ioo (0:ℝ) 1 := by constructor <;> dsimp only [m0] <;> linarith
  have hwindow (m:ℝ) (hm:m∈Icc m0 1) :
      m∈V ∧ m∈Vp ∧ dist (zF m) z < ρ/2 ∧ m∈Ioo (1-δ) (1+δ) ∧ mc < m := by
    apply hball
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    dsimp only [m0] at hm
    constructor <;> linarith [hm.1,hm.2]
  refine ⟨a,ha,ρ,hρ,κ,hκ,m0,hm0,c,hc,V,hV,?_,zF,hvalue,hsm,hdata,?_,?_⟩
  · intro m hm
    exact (hwindow m hm).1
  · intro m hm
    have hw:=hwindow m hm
    obtain ⟨hmz,hndm⟩:=hdata m hw.1
    have hmp:0 < m := hVD hw.1
    have hzero:fderiv ℝ (fun y=>limitingAtomicPhi Ξ r (y,m)) (zF m)=0 := by
      rw [fderiv_limitingAtomicPhi_locations Ξ (zF m) hmz m hmp,
        fderiv_atomicFunctional_eq_zero_of_minimizer _ (zF m) hmz hndm.1,smul_zero]
    have hp:=hP.contDiffAt (hVp.mem_nhds hw.2.1)
    obtain ⟨_,_,hcd⟩:=hcorner m ⟨hw.2.2.2.2.le,hm.2⟩
    exact ⟨hw.2.2.1,hmz,hndm,hzero,hp,contDiffAt_pressureEll _ m hmp.ne' hp,(hcd 0).2.2.2.2⟩
  · intro y hy m hm
    have hw:=hwindow m hm
    have hb:=hbox y hy m ⟨hw.2.2.2.1.1.le,hw.2.2.2.1.2.le⟩
    exact ⟨hb.1,hb.2.1,hb.2.2.2⟩

end GeneralDepthPaper
