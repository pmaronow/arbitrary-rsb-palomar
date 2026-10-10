module

public import DepthPaper.TemperatureMassColeHopf
public import DepthPaper.TemperatureFamily
public import FourPapersCommon.MixedClassicalCell
public import FourPapersCommon.MixedSupport

@[expose] public section


/-! The literal rescaled lower potential and its actual spatial and temporal
derivatives. The construction is valid for every positive m, and even for
non-atomic probability measures on constant-CDF intervals. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace DepthPaper
open FourPapersCommon ColeHopfFoundation.ProbabilityTheory
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 64

def temperatureMassPotential (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (m qc q x : ℝ) : ℝ :=
  m⁻¹*potential ((temperatureCovarianceFamily Ξ).covariance m) μ q (m*x)-
    m/2*(Ξ.first 1-Ξ.first qc)

def temperatureMassGradient (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (m q x : ℝ) : ℝ :=
  gradient ((temperatureCovarianceFamily Ξ).covariance m) μ q (m*x)

def temperatureMassHessian (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (m q x : ℝ) : ℝ :=
  m*hessian ((temperatureCovarianceFamily Ξ).covariance m) μ q (m*x)

theorem hasDerivAt_temperatureMassPotential_spatial (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) (m : ℝ) (hm : 0 < m) (qc q x : ℝ) (hq : q∈Icc (0:ℝ) 1) :
    HasDerivAt (temperatureMassPotential Ξ μ m qc q)
      (temperatureMassGradient Ξ μ m q x) x := by
  have hd:=((hasDerivAt_mixedPotential_spatial
    ((temperatureCovarianceFamily Ξ).covariance m).toEvenMixture μ q (m*x) hq).comp x
    ((hasDerivAt_id x).const_mul m)).const_mul m⁻¹
  convert! hd.sub_const (m/2*(Ξ.first 1-Ξ.first qc)) using 1
  dsimp only [temperatureMassGradient,gradient]
  field_simp

theorem hasDerivAt_temperatureMassGradient_spatial (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) (m q x : ℝ) :
    HasDerivAt (temperatureMassGradient Ξ μ m q)
      (temperatureMassHessian Ξ μ m q x) x := by
  have hd:=(hasDerivAt_mixedGradient_spatial
    ((temperatureCovarianceFamily Ξ).covariance m).toEvenMixture μ q (m*x)).comp x
    ((hasDerivAt_id x).const_mul m)
  convert! hd using 1
  dsimp only [temperatureMassHessian,hessian]
  ring

theorem temperatureMassPotential_terminal (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (m : ℝ) (hm : 0 < m) {qc : ℝ} (hc : qc∈Icc (0:ℝ) 1)
    (hs : ∀x∈FRSB.parisiSupport μ,x≤qc) (x : ℝ) :
    temperatureMassPotential Ξ μ m qc qc x=terminalValue (scaledLogCoshTerminal m) x := by
  rw [temperatureMassPotential,temperatureCovarianceFamily_covariance Ξ m hm.ne']
  have H:=mixedPotential_terminal_region (Ξ.temperatureScale m hm.ne').toEvenMixture μ hc hs
    ⟨le_rfl,hc.2⟩ (m*x)
  change potential (Ξ.temperatureScale m hm.ne') μ qc (m*x)=_ at H
  rw [H,AdmissibleCovariance.toEvenMixture_first,AdmissibleCovariance.toEvenMixture_first,
    Ξ.temperatureScale_first,Ξ.temperatureScale_first,terminalValue_scaledLogCoshTerminal m hm.ne']
  field_simp
  ring

theorem hasDerivAt_temperatureMassPotential_time (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) (m : ℝ) (hm : 0 < m) (qc : ℝ) {a b mass : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀s∈Ico a b,Paper.parisiCDF μ s=mass) {q : ℝ} (hq : q∈Ioo a b) (x : ℝ) :
    HasDerivAt (fun t=>temperatureMassPotential Ξ μ m qc t x)
      (-Ξ.second q/2*(temperatureMassHessian Ξ μ m q x+
        m*mass*temperatureMassGradient Ξ μ m q x^2)) q := by
  have hd:=(hasDerivAt_mixedPotential_constantCDF_time
    ((temperatureCovarianceFamily Ξ).covariance m).toEvenMixture μ ha hab hb hc hq (m*x)).const_mul m⁻¹
  convert! hd.sub_const (m/2*(Ξ.first 1-Ξ.first qc)) using 1
  dsimp only [temperatureMassHessian,temperatureMassGradient,hessian,gradient]
  rw [AdmissibleCovariance.toEvenMixture_second,
    temperatureCovarianceFamily_covariance Ξ m hm.ne',Ξ.temperatureScale_second]
  field_simp

end DepthPaper
