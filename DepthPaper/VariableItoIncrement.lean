module

public import FourPapersCommon.VariableItoExpectation
public import FRSB.ItoExpectationSource

@[expose] public section


/-! Genuine expectation increments for deterministic variable volatility.
The stochastic term is centered by the already proved Itô construction, and
the time/sample exchange is actual bounded-source Fubini. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus
open scoped Topology NNReal
namespace DepthPaper
open FourPapersCommon Paper
set_option maxHeartbeats 1000000

def variableItoGenerator {Ω : Type*} (X d : ℝ≥0 → Ω → ℝ) (σ : ℝ≥0 → ℝ)
    (f : ℝ → ℝ → ℝ) (s : ℝ) (ω : Ω) : ℝ :=
  itoTimeDerivative f s (X s.toNNReal ω)+itoSpaceDerivative f s (X s.toNNReal ω)*d s.toNNReal ω+
    (1/2:ℝ)*itoSpaceSecondDerivative f s (X s.toNNReal ω)*(σ s.toNNReal)^2

theorem variable_ito_expectation_increment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [SigmaFiniteFiltration P V]
    {X d J : ℝ≥0 → Ω → ℝ} {σ : ℝ≥0 → ℝ}
    (hc : BoundedDriftVariableItoCharacteristics P V X d J σ)
    (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ×ℝ => f p.1 p.2))
    (ht : ∀x,Differentiable ℝ (fun s => f s x)) (hxx : ∀s,ContDiff ℝ 2 (f s))
    (hdt : Continuous (fun p : ℝ×ℝ => itoTimeDerivative f p.1 p.2))
    (hdx : Continuous (fun p : ℝ×ℝ => itoSpaceDerivative f p.1 p.2))
    (hdxx : Continuous (fun p : ℝ×ℝ => itoSpaceSecondDerivative f p.1 p.2))
    (a b : ℝ≥0) (hab : a ≤ b) (K : ℝ≥0)
    (hK : ∀s∈Icc (0:ℝ) (b:ℝ),∀x,‖itoSpaceDerivative f s x‖ ≤ K)
    (source : ℝ → Ω → ℝ) (hsource : Measurable (Function.uncurry source))
    (B : ℝ) (hB : ∀s ω,‖source s ω‖ ≤ B)
    (hgen : ∀ω,∀s∈Icc (0:ℝ) (b:ℝ),variableItoGenerator X d σ f s ω = source s ω)
    (hi : ∀t∈Icc (0:ℝ≥0) b,Integrable (fun ω => f t (X t ω)) P) :
    (∫ω,f b (X b ω) ∂P)-(∫ω,f a (X a ω) ∂P) =
      ∫s in (a:ℝ)..(b:ℝ),∫ω,source s ω ∂P := by
  have he (t : ℝ≥0) (htb : t ≤ b) :
      (∫ω,f t (X t ω) ∂P)-(∫ω,f 0 (X 0 ω) ∂P) =
        ∫s in (0:ℝ)..(t:ℝ),∫ω,source s ω ∂P := by
    obtain ⟨N,hN,_,hzero,hformula⟩ := ito_centered_weighted_of_variableDrift hc f hf ht hxx
      hdt hdx hdxx t K (fun s hs x => hK s ⟨hs.1,hs.2.trans (NNReal.coe_le_coe.mpr htb)⟩ x)
      (fun _ => 1) stronglyMeasurable_const 1 (by simp)
    simp only [one_mul] at hzero
    have hI (ω : Ω) : generalItoTimeIntegral f X t ω+variableItoDriftIntegral X d f t ω+
        generalItoQuadraticIntegral f X (fun s _ => σ s) t ω = ∫s in (0:ℝ)..(t:ℝ),source s ω := by
      have hp : Continuous (fun s : ℝ => (s,X s.toNNReal ω)) :=
        continuous_id.prodMk ((hc.continuous_state ω).comp continuous_real_toNNReal)
      have hti := (hdt.comp hp).integrableOn_Icc (μ := volume) (a := (0:ℝ)) (b := (t:ℝ))
      have hxi := (hdx.comp hp).integrableOn_Icc (μ := volume) (a := (0:ℝ)) (b := (t:ℝ))
      obtain ⟨D,hD⟩ := hc.bounded_drift
      have hdi := hxi.mul_bdd ((hc.measurable_drift.comp
        (measurable_real_toNNReal.prodMk measurable_const)).aestronglyMeasurable)
        (.of_forall fun s => hD s.toNNReal ω)
      have hqi := (((hdxx.comp hp).const_mul (1/2:ℝ)).mul
        ((hc.continuous_volatility.comp continuous_real_toNNReal).pow 2)).integrableOn_Icc
        (μ := volume) (a := (0:ℝ)) (b := (t:ℝ))
      change Integrable (fun s => itoTimeDerivative f s (X s.toNNReal ω))
        (volume.restrict (Icc (0:ℝ) (t:ℝ))) at hti
      change Integrable (fun s => itoSpaceDerivative f s (X s.toNNReal ω)*d s.toNNReal ω)
        (volume.restrict (Icc (0:ℝ) (t:ℝ))) at hdi
      have hqi' : Integrable (fun s => (1/2:ℝ)*
          (itoSpaceSecondDerivative f s (X s.toNNReal ω)*(σ s.toNNReal)^2))
          (volume.restrict (Icc (0:ℝ) (t:ℝ))) := by
        change Integrable (fun s => ((1/2:ℝ)*itoSpaceSecondDerivative f s (X s.toNNReal ω))*(σ s.toNNReal)^2)
          (volume.restrict (Icc (0:ℝ) (t:ℝ))) at hqi
        convert! hqi using 1
        funext s
        ring
      unfold generalItoTimeIntegral variableItoDriftIntegral generalItoQuadraticIntegral
      rw [←integral_const_mul]
      rw [←integral_add hti hdi,←integral_add
        (f := fun s => itoTimeDerivative f s (X s.toNNReal ω)+itoSpaceDerivative f s (X s.toNNReal ω)*d s.toNNReal ω)
        (g := fun s => (1/2:ℝ)*(itoSpaceSecondDerivative f s (X s.toNNReal ω)*(σ s.toNNReal)^2))
        (hti.add hdi) hqi',
        intervalIntegral.integral_of_le t.coe_nonneg,integral_Icc_eq_integral_Ioc]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      simpa only [variableItoGenerator,mul_assoc] using
        hgen ω s ⟨hs.1.le,hs.2.trans (NNReal.coe_le_coe.mpr htb)⟩
    have hf' : ∀ᵐ ω ∂P,f t (X t ω) = f 0 (X 0 ω)+N ω+∫s in (0:ℝ)..(t:ℝ),source s ω := by
      filter_upwards [hformula] with ω hω
      have hIω := hI ω
      linarith
    obtain ⟨hRi,hR⟩ := FRSB.bounded_source_fubini P source hsource B hB 0 t t.coe_nonneg
    have hi0 := hi 0 ⟨le_rfl,bot_le⟩
    change Integrable (fun ω => f 0 (X 0 ω)) P at hi0
    have hit := hi t ⟨bot_le,htb⟩
    have h := integral_congr_ae hf'
    have hsum : (∫ω,(f 0 (X 0 ω)+N ω+(∫s in (0:ℝ)..(t:ℝ),source s ω)) ∂P) =
        (∫ω,f 0 (X 0 ω) ∂P)+(∫ω,N ω ∂P)+∫ω,(∫s in (0:ℝ)..(t:ℝ),source s ω) ∂P := by
      rw [integral_add (f := fun ω => f 0 (X 0 ω)+N ω)
        (g := fun ω => ∫s in (0:ℝ)..(t:ℝ),source s ω) (hi0.add hN) hRi,
        integral_add hi0 hN]
    rw [hsum,hzero,hR] at h
    linarith
  have hSb : IntervalIntegrable (fun s => ∫ω,source s ω ∂P) volume 0 b := by
    apply (intervalIntegrable_const (c := B)).mono_fun'
      (hsource.stronglyMeasurable.integral_prod_right (ν := P)).aestronglyMeasurable
    exact .of_forall fun s => by
      simpa only [probReal_univ,mul_one] using
        norm_integral_le_of_norm_le_const (μ := P) (.of_forall (hB s))
  have hSa : IntervalIntegrable (fun s => ∫ω,source s ω ∂P) volume 0 a :=
    hSb.mono_set (by simpa only [uIcc_of_le a.coe_nonneg,uIcc_of_le b.coe_nonneg] using
      Icc_subset_Icc_right (NNReal.coe_le_coe.mpr hab))
  have hs := intervalIntegral.integral_interval_sub_left hSa hSb
  rw [intervalIntegral.integral_symm (a := (a:ℝ)) (b := (b:ℝ))] at hs
  have ha := he a hab
  have hb := he b le_rfl
  linarith

end DepthPaper
