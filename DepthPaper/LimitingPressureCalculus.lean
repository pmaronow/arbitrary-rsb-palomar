module

public import DepthPaper.NondegeneratePressureSmooth
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section


/-! Actual scalar derivatives of the reduced limiting pressure. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 800000

def pressureEntropy (p : ℝ→ℝ) (m : ℝ) : ℝ := p m-m*deriv p m
def pressureEll (p : ℝ→ℝ) (m : ℝ) : ℝ := 2*pressureEntropy p m/m^2
def limitingPressureObjective (p : ℝ→ℝ) (lam m : ℝ) : ℝ := p m/m+lam*m/2
def pressureKappa (p : ℝ→ℝ) : ℝ := deriv (deriv p) 1+2*pressureEntropy p 1

theorem hasDerivAt_pressureEntropy (p : ℝ→ℝ) (m : ℝ)
    (hp : DifferentiableAt ℝ p m) (hpp : DifferentiableAt ℝ (deriv p) m) :
    HasDerivAt (pressureEntropy p) (-m*deriv (deriv p) m) m := by
  exact (hp.hasDerivAt.sub ((hasDerivAt_id m).mul hpp.hasDerivAt)).congr_deriv
    (by dsimp only [id_eq];ring)

theorem hasDerivAt_pressureEll (p : ℝ→ℝ) (m : ℝ) (hm : m≠0)
    (hp : DifferentiableAt ℝ p m) (hpp : DifferentiableAt ℝ (deriv p) m) :
    HasDerivAt (pressureEll p)
      (-2*deriv (deriv p) m/m-4*pressureEntropy p m/m^3) m := by
  apply ((hasDerivAt_pressureEntropy p m hp hpp).const_mul 2 |>.div
    ((hasDerivAt_id m).pow 2) (pow_ne_zero _ hm)).congr_deriv
  dsimp only [id_eq,Pi.pow_apply]
  field_simp [hm]
  ring

/-- The exact displayed derivative J′=(λ−ell)/2. -/
theorem hasDerivAt_limitingPressureObjective (p : ℝ→ℝ) (lam m : ℝ) (hm : m≠0)
    (hp : DifferentiableAt ℝ p m) :
    HasDerivAt (limitingPressureObjective p lam) ((lam-pressureEll p m)/2) m := by
  apply ((hp.hasDerivAt.div (hasDerivAt_id m) hm).add
    (((hasDerivAt_id m).const_mul lam).div_const 2)).congr_deriv
  dsimp only [pressureEll,pressureEntropy,id_eq]
  field_simp [hm]
  ring

theorem convex_secondDerivative_nonneg_at (p : ℝ→ℝ) (m : ℝ)
    (hc : ConvexOn ℝ univ p) (hp : ContDiffAt ℝ 2 p m) :
    0 ≤ deriv (deriv p) m := by
  have he : ∀ᶠx in 𝓝 m,DifferentiableAt ℝ p x :=
    (hp.eventually (by norm_num)).mono (fun x hx=>hx.differentiableAt (by norm_num))
  obtain ⟨ε,hε,hball⟩:=Metric.mem_nhds_iff.mp he
  have hm:= (hc.subset (subset_univ _) (convex_ball m ε)).monotoneOn_deriv hball
  simpa only [derivWithin_of_mem_nhds (Metric.ball_mem_nhds m hε)] using
    (hm.derivWithin_nonneg (x:=m))

theorem pressureKappa_pos (p : ℝ→ℝ) (hc : ConvexOn ℝ univ p)
    (hp : ContDiffAt ℝ 2 p 1) (he : 0 < pressureEntropy p 1) :
    0 < pressureKappa p := by
  have hn:=convex_secondDerivative_nonneg_at p 1 hc hp
  dsimp only [pressureKappa]
  linarith

theorem deriv_pressureEll_one (p : ℝ→ℝ) (hp : ContDiffAt ℝ 2 p 1) :
    deriv (pressureEll p) 1=-2*pressureKappa p := by
  rw [(hasDerivAt_pressureEll p 1 one_ne_zero
    (hp.differentiableAt (by norm_num))
    ((hp.derivWithin (m:=1) (by norm_num)).differentiableAt (by norm_num))).deriv]
  dsimp only [pressureKappa]
  norm_num
  ring

theorem contDiffAt_pressureEll (p : ℝ→ℝ) (m : ℝ) (hm : m≠0)
    (hp : ContDiffAt ℝ ∞ p m) : ContDiffAt ℝ ∞ (pressureEll p) m := by
  have hd:=hp.derivWithin (m:=∞) (by simp)
  exact ((contDiffAt_const.mul (hp.sub (contDiffAt_id.mul hd))).div
    (contDiffAt_id.pow 2) (pow_ne_zero _ hm))

theorem exists_limiting_mass_window (p : ℝ→ℝ) (V : Set ℝ) (hV : IsOpen V)
    (h1V : (1:ℝ)∈V) (hp : ContDiffOn ℝ ∞ p V) (hc : ConvexOn ℝ univ p)
    (he : 0 < pressureEntropy p 1) :
    ∃m1∈Ioo (0:ℝ) 1,∃c>0,Icc m1 1⊆V ∧
      (∀m∈Icc m1 1,deriv (pressureEll p) m≤-2*c) ∧
      deriv (pressureEll p) 1=-2*pressureKappa p := by
  have hps:=hp.contDiffAt (hV.mem_nhds h1V)
  have hkp:=pressureKappa_pos p hc (hps.of_le (by simp)) he
  have hd:=deriv_pressureEll_one p (hps.of_le (by simp))
  have hE:=contDiffAt_pressureEll p 1 one_ne_zero hps
  have hcont:ContinuousAt (deriv (pressureEll p)) 1 :=
    (hE.derivWithin (m:=0) (by simp)).continuousAt
  have hn : ∀ᶠm in 𝓝 (1:ℝ),m∈V ∧ deriv (pressureEll p) m < -pressureKappa p := by
    have hneg : deriv (pressureEll p) 1 < -pressureKappa p := by rw [hd];linarith
    exact (show ∀ᶠm in 𝓝 (1:ℝ),m∈V from hV.mem_nhds h1V).and
      (hcont.eventually (eventually_lt_nhds hneg))
  obtain ⟨d,hdp,hball⟩:=Metric.mem_nhds_iff.mp hn
  let δ:=min (d/2) (1/2:ℝ)
  have hδ:0<δ:=lt_min (by positivity) (by norm_num)
  have hδd:δ<d:=(min_le_left _ _).trans_lt (by linarith)
  have hδ1:δ<1:=(min_le_right _ _).trans_lt (by norm_num)
  have hb (m : ℝ) (hm : m∈Icc (1-δ) 1) : m∈Metric.ball (1:ℝ) d := by
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    constructor <;> linarith [hm.1,hm.2]
  refine ⟨1-δ,⟨by linarith,by linarith⟩,pressureKappa p/2,by positivity,?_,?_,hd⟩
  · intro m hm
    exact (hball (hb m hm)).1
  · intro m hm
    have hh:=(hball (hb m hm)).2
    linarith

end DepthPaper
