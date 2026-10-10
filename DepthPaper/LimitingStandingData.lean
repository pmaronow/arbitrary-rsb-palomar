module

public import DepthPaper.LimitingCouplingWindow

@[expose] public section


/-! The standing choices are constructed from an actual nondegenerate
finite-depth seed. They are not additional hypotheses on the model. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 64

structure LimitingStandingData (Ξ:AdmissibleCovariance) {r:ℕ} (seed:AtomicPoint r) where
  radius:ℝ
  radius_pos:0 < radius
  margin:ℝ
  margin_pos:0 < margin
  massLower:ℝ
  massLower_mem:massLower∈Ioo (0:ℝ) 1
  slope:ℝ
  slope_pos:0 < slope
  couplingMargin:ℝ
  couplingMargin_pos:0 < couplingMargin
  couplingMargin_small:couplingMargin < pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) 1/4
  couplingMargin_gap:couplingMargin < (pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) massLower-
    pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) 1)/4
  couplingLower_pos:0 < pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) 1-2*couplingMargin
  cutoff:ℝ
  cutoff_mem:cutoff∈Ioo (0:ℝ) 1
  branch:ℝ→AtomicPoint r
  massDomain:Set ℝ
  massDomain_open:IsOpen massDomain
  massWindow_subset:Icc massLower 1⊆massDomain
  branch_seed:branch 1=seed
  branch_smooth:ContDiffOn ℝ ∞ branch massDomain
  branch_nondegenerate_domain:∀m∈massDomain,∃hm:IsAtomicPoint (branch m),
    Nondegenerate ((temperatureCovarianceFamily Ξ).covariance m) (branch m) hm
  branch_close:∀m∈Icc massLower 1,dist (branch m) seed < radius/2
  branch_nondegenerate:∀m∈Icc massLower 1,∃hm:IsAtomicPoint (branch m),
    Nondegenerate ((temperatureCovarianceFamily Ξ).covariance m) (branch m) hm
  branch_stationary:∀m∈Icc massLower 1,
    fderiv ℝ (fun z=>limitingAtomicPhi Ξ r (z,m)) (branch m)=0
  pressure_smooth:∀m∈Icc massLower 1,
    ContDiffAt ℝ ∞ (scaledThermodynamicPressure Ξ.toEvenMixture) m
  ell_smooth:∀m∈Icc massLower 1,
    ContDiffAt ℝ ∞ (pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture)) m
  ell_slope:∀m∈Icc massLower 1,
    deriv (pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture)) m ≤ -2*slope
  ell_strictAnti:StrictAntiOn (pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture)) (Icc massLower 1)
  ball_valid:∀z∈closedBall seed radius,IsAtomicPoint z
  ball_below_cutoff:∀z∈closedBall seed radius,atomicLocation z (Fin.last r) < cutoff
  hessian_margin:∀z∈closedBall seed radius,∀m∈Icc massLower 1,∀v:AtomicPoint r,
    margin*‖v‖^2 ≤ (fderiv ℝ (fun u=>fderiv ℝ (fun w=>limitingAtomicPhi Ξ r (w,m)) u) z v) v

theorem exists_limitingStandingData (Ξ:AdmissibleCovariance) {r:ℕ}
    (seed:AtomicPoint r) (hz:IsAtomicPoint seed) (hnd:Nondegenerate Ξ seed hz) :
    Nonempty (LimitingStandingData Ξ seed) := by
  obtain ⟨a,ha,R,hR,κ,hκ,e,he,c,hc,V,hV,hwin,zF,hzF,hsm,hdataV,hdata,hbox⟩:=
    exists_limiting_branch_window Ξ seed hz hnd
  have hreg:=fun m hm=>(hdata m hm).2.choose_spec.2.2.2.1
  have hslope:=fun m hm=>(hdata m hm).2.choose_spec.2.2.2.2
  obtain ⟨eta,heta,he1,heg,hlo,hanti,_⟩:=limiting_coupling_window Ξ seed hz hnd
    e he c hc hreg hslope
  refine ⟨{
    radius:=R,radius_pos:=hR,margin:=κ,margin_pos:=hκ,
    massLower:=e,massLower_mem:=he,slope:=c,slope_pos:=hc,
    couplingMargin:=eta,couplingMargin_pos:=heta,couplingMargin_small:=he1,
    couplingMargin_gap:=heg,couplingLower_pos:=hlo,cutoff:=a,cutoff_mem:=ha,
    branch:=zF,massDomain:=V,massDomain_open:=hV,massWindow_subset:=hwin,
    branch_seed:=hzF,branch_smooth:=hsm,branch_nondegenerate_domain:=hdataV,
    branch_close:=fun m hm=>(hdata m hm).1,
    branch_nondegenerate:=fun m hm=>⟨(hdata m hm).2.choose,(hdata m hm).2.choose_spec.1⟩,
    branch_stationary:=fun m hm=>(hdata m hm).2.choose_spec.2.1,
    pressure_smooth:=fun m hm=>(hdata m hm).2.choose_spec.2.2.1,
    ell_smooth:=hreg,ell_slope:=hslope,ell_strictAnti:=hanti,
    ball_valid:=fun z hz=>(hbox z hz 1 ⟨he.2.le,le_rfl⟩).1,
    ball_below_cutoff:=fun z hz=>(hbox z hz 1 ⟨he.2.le,le_rfl⟩).2.1,
    hessian_margin:=fun z hz m hm=>(hbox z hz m hm).2.2
  }⟩

namespace LimitingStandingData
variable {Ξ:AdmissibleCovariance} {r:ℕ} {seed:AtomicPoint r}

def couplingLower (d:LimitingStandingData Ξ seed) : ℝ :=
  pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) 1-2*d.couplingMargin
def couplingUpper (d:LimitingStandingData Ξ seed) : ℝ :=
  pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) d.massLower+2*d.couplingMargin
def stripRateLower (d:LimitingStandingData Ξ seed) : ℝ := d.massLower^2*d.couplingLower/4
def stripRateUpper (d:LimitingStandingData Ξ seed) : ℝ := d.couplingUpper+1

theorem couplingLower_le_upper (d:LimitingStandingData Ξ seed) : d.couplingLower ≤ d.couplingUpper := by
  have hh:=d.ell_strictAnti ⟨le_rfl,d.massLower_mem.2.le⟩ ⟨d.massLower_mem.2.le,le_rfl⟩ d.massLower_mem.2
  dsimp only [couplingLower,couplingUpper]
  linarith [d.couplingMargin_pos]

theorem strip_rates (d:LimitingStandingData Ξ seed) :
    0 < d.stripRateLower ∧ d.stripRateLower < d.massLower^2*d.couplingLower/2 ∧
    d.couplingUpper/2 < d.stripRateUpper := by
  have hlo:0 < d.couplingLower := d.couplingLower_pos
  have he:0 < d.massLower := d.massLower_mem.1
  have hhi:0 < d.couplingUpper := hlo.trans_le d.couplingLower_le_upper
  dsimp only [stripRateLower,stripRateUpper]
  constructor
  · have hp:0 < d.massLower^2*d.couplingLower := by positivity
    linarith
  constructor
  · have hp:0 < d.massLower^2*d.couplingLower := by positivity
    linarith
  · linarith

end LimitingStandingData
end DepthPaper
