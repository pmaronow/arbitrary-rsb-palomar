module

public import DepthPaper.AtomMoveOperations
public import DepthPaper.SupportingPlane
public import DepthPaper.SmallRemainderDirect

@[expose] public section


/-! Literal mass transfers between two atoms of an arbitrary probability
measure. Convex mixing with the donor-atom relocation constructs the measure
without subtracting measures. Positive transfer moves mass from `b` to `a`;
negative transfer reverses it. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace DepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

def atomTransferTarget (μ : ParisiMeasure) (a b : Overlap) : ParisiMeasure :=
  moveAtom μ b ((a:ℝ)-(b:ℝ))

theorem movedOverlap_sub (a b : Overlap) : movedOverlap b ((a:ℝ)-(b:ℝ))=a := by
  apply Subtype.ext
  simp only [movedOverlap,add_sub_cancel,projIcc_of_mem (by norm_num : (0:ℝ)≤1) a.property]

theorem integral_atomTransferTarget_sub (μ : ParisiMeasure) (a b : Overlap)
    (f : Overlap→ᵇℝ) :
    (∫q,f q ∂(atomTransferTarget μ a b : Measure Overlap))-
      (∫q,f q ∂(μ : Measure Overlap))=atomWeight μ b*(f a-f b) := by
  simpa only [atomTransferTarget,movedOverlap_sub] using
    integral_moveAtom_sub μ b ((a:ℝ)-(b:ℝ)) f

def transferAtomMass (μ : ParisiMeasure) (a b : Overlap) (t : ℝ) : ParisiMeasure :=
  if 0≤t then Paper.parisiMix μ (atomTransferTarget μ a b) (t/atomWeight μ b)
  else Paper.parisiMix μ (atomTransferTarget μ b a) (-t/atomWeight μ a)

@[simp] theorem transferAtomMass_zero (μ : ParisiMeasure) (a b : Overlap) :
    transferAtomMass μ a b 0=μ := by
  simp [transferAtomMass]

theorem integral_transferAtomMass_sub (μ : ParisiMeasure) (a b : Overlap)
    (ha : 0<atomWeight μ a) (hb : 0<atomWeight μ b) (t : ℝ)
    (ht : -atomWeight μ a≤t ∧ t≤atomWeight μ b) (f : Overlap→ᵇℝ) :
    (∫q,f q ∂(transferAtomMass μ a b t : Measure Overlap))-
      (∫q,f q ∂(μ : Measure Overlap))=t*(f a-f b) := by
  classical
  unfold transferAtomMass
  split_ifs with hs
  · have hε : t/atomWeight μ b∈Icc (0:ℝ) 1 :=
      ⟨div_nonneg hs hb.le,(div_le_one hb).mpr ht.2⟩
    rw [Paper.integral_parisiMix f.continuous _ _ _ hε]
    have he:=integral_atomTransferTarget_sub μ a b f
    have hw:=hb.ne'
    field_simp
    nlinarith [he]
  · have hε : -t/atomWeight μ a∈Icc (0:ℝ) 1 :=
      ⟨div_nonneg (by linarith) ha.le,(div_le_one ha).mpr (by linarith [ht.1])⟩
    rw [Paper.integral_parisiMix f.continuous _ _ _ hε]
    have he:=integral_atomTransferTarget_sub μ b a f
    have hw:=ha.ne'
    field_simp
    nlinarith [he]

theorem transferAtomMass_mem_interval (μ : ParisiMeasure) (a b : Overlap)
    (ha : 0<atomWeight μ a) (hb : 0<atomWeight μ b) :
    ∀ᶠt in 𝓝 (0:ℝ),-atomWeight μ a≤t ∧ t≤atomWeight μ b :=
  Icc_mem_nhds (by linarith) hb

theorem tendsto_transferAtomMass_zero (μ : ParisiMeasure) (a b : Overlap)
    (ha : 0<atomWeight μ a) (hb : 0<atomWeight μ b) :
    Tendsto (transferAtomMass μ a b) (𝓝 (0:ℝ)) (𝓝 μ) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have hh := ((continuous_id.mul_const (f a-f b)).add_const
    (∫q,f q ∂(μ : Measure Overlap))).continuousAt.tendsto (x:=0)
  have he : (fun t=>∫q,f q ∂(transferAtomMass μ a b t : Measure Overlap))=ᶠ[𝓝 0]
      (fun t=>t*(f a-f b)+(∫q,f q ∂(μ : Measure Overlap))) := by
    filter_upwards [transferAtomMass_mem_interval μ a b ha hb] with t ht
    linarith [integral_transferAtomMass_sub μ a b ha hb t ht f]
  simpa only [id_eq,zero_mul,zero_add] using hh.congr' he.symm

theorem atomMassTransfer_functional_remainder (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (a b : Overlap) (ha : 0<atomWeight μ a) (hb : 0<atomWeight μ b)
    (t : ℝ) (ht : -atomWeight μ a≤t ∧ t≤atomWeight μ b) :
    ‖parisiFunctional Ξ (transferAtomMass μ a b t)-parisiFunctional Ξ μ+
      t*(firstVariation Ξ μ a-firstVariation Ξ μ b)‖ ≤
      (2*‖firstVariationValueMap Ξ (transferAtomMass μ a b t)-
        firstVariationValueMap Ξ μ‖)*|t| := by
  let ν:=transferAtomMass μ a b t
  let A:=firstVariation Ξ μ a-firstVariation Ξ μ b
  let B:=firstVariation Ξ ν a-firstVariation Ξ ν b
  let Δ:=parisiFunctional Ξ ν-parisiFunctional Ξ μ
  have hmove (ρ : ParisiMeasure) :
      (∫q : Overlap,firstVariation Ξ ρ q ∂(ν : Measure Overlap))-
        (∫q : Overlap,firstVariation Ξ ρ q ∂(μ : Measure Overlap))=
        t*(firstVariation Ξ ρ a-firstVariation Ξ ρ b) := by
    simpa only [BoundedContinuousFunction.mkOfCompact_apply,firstVariationValueMap_apply] using
      integral_transferAtomMass_sub μ a b ha hb t ht
        (BoundedContinuousFunction.mkOfCompact (firstVariationValueMap Ξ ρ))
  have hp:=firstVariation_supporting_planes Ξ μ ν
  rw [hmove μ,hmove ν] at hp
  change -(t*A)≤Δ ∧ Δ≤-(t*B) at hp
  have hnonneg : 0≤Δ+t*A := by linarith [hp.1]
  have hupper : Δ+t*A≤t*(A-B) := by linarith [hp.2]
  have hi:=firstVariation_two_values_sub_norm_le Ξ μ ν a b
  change ‖B-A‖≤2*‖firstVariationValueMap Ξ ν-firstVariationValueMap Ξ μ‖ at hi
  change ‖Δ+t*A‖≤(2*‖firstVariationValueMap Ξ ν-firstVariationValueMap Ξ μ‖)*|t|
  rw [Real.norm_of_nonneg hnonneg]
  calc
    Δ+t*A≤t*(A-B) := hupper
    _≤‖t*(A-B)‖ := le_abs_self _
    _=|t| * ‖A-B‖ := by rw [norm_mul,Real.norm_eq_abs]
    _≤|t| * (2*‖firstVariationValueMap Ξ ν-firstVariationValueMap Ξ μ‖) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg t)
      simpa only [norm_sub_rev] using hi
    _=(2*‖firstVariationValueMap Ξ ν-firstVariationValueMap Ξ μ‖)*|t| := by ring

/-- Literal derivative with respect to the amount moved from `b` to `a`.
The other mass of the order parameter may be nonatomic. -/
theorem hasDerivAt_parisiFunctional_transferAtomMass (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) (a b : Overlap)
    (ha : 0<atomWeight μ a) (hb : 0<atomWeight μ b) :
    HasDerivAt (fun t=>parisiFunctional Ξ (transferAtomMass μ a b t))
      (firstVariation Ξ μ b-firstVariation Ξ μ a) 0 := by
  let φ:ℝ→ℝ:=fun t=>parisiFunctional Ξ (transferAtomMass μ a b t)
  let A:=firstVariation Ξ μ a-firstVariation Ξ μ b
  have hpart : HasDerivAt (fun t:ℝ=>t*A) A 0 := by
    simpa only [one_mul,id_eq] using (hasDerivAt_id (0:ℝ)).mul_const A
  let ψ:ℝ→ℝ:=fun t=>φ t+t*A
  let E:ℝ→ℝ:=fun t=>2*‖firstVariationValueMap Ξ (transferAtomMass μ a b t)-
    firstVariationValueMap Ξ μ‖
  have hE : Tendsto E (𝓝 (0:ℝ)) (𝓝 0) := by
    have hp:=tendsto_firstVariationValueMap_of_weak Ξ _ μ
      (tendsto_transferAtomMass_zero μ a b ha hb)
    simpa only [E,sub_self,norm_zero,mul_zero] using
      (hp.sub_const (firstVariationValueMap Ξ μ)).norm.const_mul 2
  have hψ : HasDerivAt ψ 0 0 := by
    apply hasDerivAt_of_small_remainder ψ 0 E hE
    filter_upwards [transferAtomMass_mem_interval μ a b ha hb] with t ht
    simpa only [ψ,φ,A,E,transferAtomMass_zero,zero_mul,add_zero,sub_zero,
      add_sub_right_comm] using atomMassTransfer_functional_remainder Ξ μ a b ha hb t ht
  have hout:=hψ.sub hpart
  convert hout using 1
  · funext t
    dsimp only [ψ,φ,A,Pi.sub_apply]
    ring
  · dsimp only [A]
    ring

end DepthPaper
