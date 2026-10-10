module

public import DepthPaper.TemperatureMassPotential
public import FourPapersCommon.MixedScalarTransition

@[expose] public section


/-! Exact finite-cell Cole–Hopf recursion for the rescaled lower potential.
Both covariance variance and the lower cumulative mass are the literal
temperature–mass changes of variables. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace DepthPaper
open FourPapersCommon ColeHopfFoundation.ProbabilityTheory
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem temperatureMassPotential_hasLinearGrowth (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) (m : ℝ) (hm : 0 < m) (qc q : ℝ) (hq : q∈Icc (0:ℝ) 1) :
    HasLinearGrowth (temperatureMassPotential Ξ μ m qc q) := by
  exact HasLinearGrowth.of_bounded_deriv
    (fun x=>hasDerivAt_temperatureMassPotential_spatial Ξ μ m hm qc q x hq)
    (L:=1) (fun x=>by
      simpa only [temperatureMassGradient,gradient,Real.norm_eq_abs] using
        norm_mixedGradient_le_one ((temperatureCovarianceFamily Ξ).covariance m).toEvenMixture
          μ (q,m*x))

theorem measurable_temperatureMassPotential_section (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) (m qc q : ℝ) :
    Measurable (temperatureMassPotential Ξ μ m qc q) := by
  exact (((continuous_mixedPotential_section
    ((temperatureCovarianceFamily Ξ).covariance m).toEvenMixture μ q).comp
      (continuous_const.mul continuous_id)).const_mul m⁻¹).sub continuous_const |>.measurable

theorem temperatureMassPotential_coleHopf (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) (m : ℝ) (hm : 0 < m) (qc : ℝ) {a b mass : ℝ}
    (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1) (hab : a < b)
    (hc : ∀s∈Ico a b,Paper.parisiCDF μ s=mass) (x : ℝ) :
    temperatureMassPotential Ξ μ m qc a x=
      coleHopf (m*mass) (Ξ.first b-Ξ.first a).toNNReal
        (temperatureMassPotential Ξ μ m qc b) x := by
  let Ψ:AdmissibleCovariance:=(temperatureCovarianceFamily Ξ).covariance m
  let k:ℝ:=m/2*(Ξ.first 1-Ξ.first qc)
  let A:ℝ→ℝ:=fun y=>m⁻¹*potential Ψ μ b (m*y)
  have hAg : HasLinearGrowth A := by
    exact HasLinearGrowth.of_bounded_deriv
      (fun y=>by
        have hd:=hasDerivAt_temperatureMassPotential_spatial Ξ μ m hm qc b y hb
        convert! hd.add_const k using 1
        funext w
        dsimp only [temperatureMassPotential,A,k,Ψ]
        ring)
      (L:=1) (fun y=>by
        simpa only [temperatureMassGradient,gradient,Real.norm_eq_abs] using
          norm_mixedGradient_le_one Ψ.toEvenMixture μ (b,m*y))
  have hAm : Measurable A := by
    exact (((continuous_mixedPotential_section Ψ.toEvenMixture μ b).comp
      (continuous_const.mul continuous_id)).const_mul m⁻¹).measurable
  have hvar : NNReal.mk (m^2) (sq_nonneg m)*(Ξ.first b-Ξ.first a).toNNReal=
      (Ψ.first b-Ψ.first a).toNNReal := by
    apply NNReal.coe_injective
    rw [NNReal.coe_mul,NNReal.coe_mk,Real.coe_toNNReal _
      (sub_nonneg.mpr (Ξ.first_strictMonoOn.monotoneOn ha.1 hb.1 hab.le))]
    have he : Ψ.first b-Ψ.first a=m^2*(Ξ.first b-Ξ.first a) := by
      dsimp only [Ψ]
      rw [temperatureCovarianceFamily_covariance Ξ m hm.ne',Ξ.temperatureScale_first,
        Ξ.temperatureScale_first]
      ring
    rw [he,Real.coe_toNNReal _ (mul_nonneg (sq_nonneg m)
      (sub_nonneg.mpr (Ξ.first_strictMonoOn.monotoneOn ha.1 hb.1 hab.le)))]
  have hs:=coleHopf_temperature_mass_scaling m hm.ne' mass
    (Ξ.first b-Ξ.first a).toNNReal (fun y=>potential Ψ μ b y)
    (continuous_mixedPotential_section Ψ.toEvenMixture μ b).measurable x
  rw [hvar] at hs
  have hch:=mixedPotential_coleHopf_on_constantCDF Ψ.toEvenMixture μ ha hb hab hc (m*x)
  simp only [AdmissibleCovariance.toEvenMixture_first] at hch
  change potential Ψ μ a (m*x)=
    coleHopf mass (Ψ.first b-Ψ.first a).toNNReal (fun y=>potential Ψ μ b y) (m*x) at hch
  have hshift:=coleHopf_add_const hAg hAm (-k) (m*mass)
    (Ξ.first b-Ξ.first a).toNNReal x
  change m⁻¹*potential Ψ μ a (m*x)-k=
    coleHopf (m*mass) (Ξ.first b-Ξ.first a).toNNReal (fun y=>A y-k) x
  rw [show (fun y=>A y-k)=(fun y=>A y+(-k)) by rfl,hshift]
  rw [hs,←hch]
  rfl

end DepthPaper
