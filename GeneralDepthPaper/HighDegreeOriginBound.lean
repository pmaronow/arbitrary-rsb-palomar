module

public import GeneralDepthPaper.Curvature
public import GeneralDepthPaper.EndpointStrip

@[expose] public section


/-! A single origin radius works for every actual added-degree candidate,
independently of its atomic measure and endpoint. -/
noncomputable section
open Set
namespace GeneralDepthPaper

def highDegreeOriginBound (Ξ : AdmissibleCovariance) (L : ℝ) : ℝ :=
  Ξ.first (1/2)+L*(Real.exp (-Real.log (1/2))/(-Real.log (1/2)))

theorem highDegreeOriginBound_pos (Ξ : AdmissibleCovariance) {L : ℝ} (hL : 0≤L) :
    0<highDegreeOriginBound Ξ L := by
  have hlog : 0< -Real.log (1/2:ℝ):=neg_pos.mpr (Real.log_neg (by norm_num) (by norm_num))
  have hc : 0≤L*(Real.exp (-Real.log (1/2))/(-Real.log (1/2))) := by positivity
  exact add_pos_of_pos_of_nonneg (Ξ.first_pos (by norm_num)) hc

theorem highDegree_first_half_le (Ξ : AdmissibleCovariance)
    (p : ℕ) (hp : 4≤p) (he : Even p) (hn : p∉Ξ.degrees)
    (lam : ℝ) (hlam : 0<lam) {L : ℝ} (hl : lam≤L) :
    (Ξ.addHighDegree p hp he hn lam hlam).first (1/2)≤highDegreeOriginBound Ξ L := by
  rw [Ξ.addHighDegree_first]
  have hb:=nat_mul_pow_sub_one_bound (by norm_num : (1/2:ℝ)∈Ioo (0:ℝ) 1)
    p (by omega)
  have hL : 0≤L:=hlam.le.trans hl
  have HH:=mul_le_mul hl hb (by positivity : 0≤(p:ℝ)*(1/2:ℝ)^(p-1)) hL
  dsimp only [highDegreeOriginBound]
  nlinarith

end GeneralDepthPaper
