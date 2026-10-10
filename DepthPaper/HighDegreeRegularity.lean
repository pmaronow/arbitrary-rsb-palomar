module

public import DepthPaper.HighDegreeModel
public import DepthPaper.SmoothCovarianceFamily

@[expose] public section


/-! The genuine high-degree perturbation is a smooth finite covariance
family on positive coefficients. No fixed-SK replacement is made. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper

def highDegreeCovarianceFamily (Ξ : AdmissibleCovariance) (p : ℕ) (hp : 4≤p)
    (he : Even p) (hn : p∉Ξ.degrees) : SmoothCovarianceFamily ℝ where
  domain:=Ioi 0
  isOpen_domain:=isOpen_Ioi
  covariance lam:=if hlam:0 < lam then Ξ.addHighDegree p hp he hn lam hlam else Ξ
  degrees:=insert p Ξ.degrees
  degrees_eq lam hlam:=by
    rw [dite_eq_left (show 0 < lam from hlam)]
    rfl
  smooth_coefficient j hj:=by
    by_cases hje:j=p
    · subst j
      apply contDiffOn_id.congr
      intro lam hlam
      rw [dite_eq_left (show 0 < lam from hlam)]
      simp [AdmissibleCovariance.addHighDegree]
    · have hconst : ContDiffOn ℝ ∞ (fun _:ℝ=>Ξ.coefficient j) (Ioi (0:ℝ)):=contDiffOn_const
      apply hconst.congr
      intro lam hlam
      rw [dite_eq_left (show 0 < lam from hlam)]
      simp only [AdmissibleCovariance.addHighDegree,ite_eq_right hje]

theorem highDegreeCovarianceFamily_covariance (Ξ : AdmissibleCovariance)
    (p : ℕ) (hp : 4≤p) (he : Even p) (hn : p∉Ξ.degrees)
    (lam : ℝ) (hlam : 0 < lam) :
    (highDegreeCovarianceFamily Ξ p hp he hn).covariance lam=
      Ξ.addHighDegree p hp he hn lam hlam := by
  simp only [highDegreeCovarianceFamily,dite_eq_left hlam]

end DepthPaper
