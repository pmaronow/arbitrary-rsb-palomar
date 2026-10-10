module

public import GeneralDepthPaper.RevisedCovarianceInverse
public import GeneralDepthPaper.RevisedTransition

@[expose] public section

/-! The universal revised Gardner results on the finite-support
common-mixture interface. The finite coefficient presentation is an exact
inverse bridge: its covariance, probability measures, physical pressure,
first variation, and actual atomic functional agree with this interface. -/
noncomputable section
namespace DepthPaper.RevisedCovariance

/-- Transfer of the paper's seed condition to its exact finite coefficient
presentation. No positive-Hessian or subcriticality assumption is included. -/
theorem paperNondegenerate_toGeneralCovariance (Ξ : RevisedCovariance) {r : ℕ}
    (seed : AtomicPoint r) (hz : IsAtomicPoint seed) (hND : Nondegenerate Ξ seed hz) :
    GeneralDepthPaper.PaperNondegenerate Ξ.toGeneralCovariance seed hz := by
  apply (GeneralDepthPaper.paperNondegenerate_iff_revised Ξ.toGeneralCovariance seed hz).mp
  simpa only [toGeneralCovariance_toRevisedCovariance] using hND

theorem isSubcritical_toGeneralCovariance (Ξ : RevisedCovariance)
    (hsub : Ξ.IsSubcritical) : Ξ.toGeneralCovariance.IsSubcritical := by
  apply (GeneralDepthPaper.AdmissibleCovariance.toRevisedCovariance_isSubcritical_iff
    Ξ.toGeneralCovariance).mp
  simpa only [toGeneralCovariance_toRevisedCovariance] using hsub

/-- Revised support geometry and phase transition for every positive finite
even covariance with Ξ''(0)<1 and a nondegenerate finite-step Parisi measure.
The target uses the exact finite presentation of the same physical model. -/
theorem revised_gardner_geometry (Ξ : RevisedCovariance) {r : ℕ}
    (seed : AtomicPoint r) (hz : IsAtomicPoint seed) (hsub : Ξ.IsSubcritical)
    (hND : Nondegenerate Ξ seed hz) :
    GeneralDepthPaper.RevisedGardnerGeometryTarget Ξ.toGeneralCovariance seed :=
  GeneralDepthPaper.revised_gardner_geometry_of_paper_nondegenerate
    Ξ.toGeneralCovariance seed hz (isSubcritical_toGeneralCovariance Ξ hsub)
    (paperNondegenerate_toGeneralCovariance Ξ seed hz hND)

/-- Revised mass and logarithmic-location asymptotics, including the
actual derivative-ratio normalization and diagonal small-o mass law. -/
theorem revised_gardner_asymptotics (Ξ : RevisedCovariance) {r : ℕ}
    (seed : AtomicPoint r) (hz : IsAtomicPoint seed) (hsub : Ξ.IsSubcritical)
    (hND : Nondegenerate Ξ seed hz) :
    GeneralDepthPaper.RevisedGardnerAsymptoticsTarget Ξ.toGeneralCovariance seed :=
  GeneralDepthPaper.revised_gardner_asymptotics_of_paper_nondegenerate
    Ξ.toGeneralCovariance seed hz (isSubcritical_toGeneralCovariance Ξ hsub)
    (paperNondegenerate_toGeneralCovariance Ξ seed hz hND)

/-- Universal high-degree Gardner transition and its finite-degree
asymptotics. Quadratic interactions are permitted, and positive
atomic-Hessian definiteness is a proved dependency. -/
theorem universal_gardner_transition (Ξ : RevisedCovariance) {r : ℕ}
    (seed : AtomicPoint r) (hz : IsAtomicPoint seed) (hsub : Ξ.IsSubcritical)
    (hND : Nondegenerate Ξ seed hz) :
    GeneralDepthPaper.RevisedGardnerGeometryTarget Ξ.toGeneralCovariance seed ∧
      GeneralDepthPaper.RevisedGardnerAsymptoticsTarget Ξ.toGeneralCovariance seed :=
  ⟨revised_gardner_geometry Ξ seed hz hsub hND,
    revised_gardner_asymptotics Ξ seed hz hsub hND⟩

end DepthPaper.RevisedCovariance
