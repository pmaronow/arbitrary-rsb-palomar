module

public import FRSB.BackwardsConstantTime
public import FRSB.InteriorTimeCap
public import FRSB.ItoStochasticTools
public import FRSB.OptimalCurvatureMoment
public import Paper.ParisiStateShift

@[expose] public section

/-! Genuine Hessian stochastic-integral representation on each constant-CDF
cell of the actual selected diffusion. Both the integrand and the stochastic
increment are concrete; no martingale representation is supplied. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus Paper
open scoped ContDiff Topology NNReal
namespace GeneralDepthPaper
open FRSB
set_option maxHeartbeats 1000000

/-- The actual optimal gradient increment is the limit in probability of
Brownian left sums with its actual Hessian integrand on an interior cell. -/
theorem actualGradient_stochastic_cell_interior
    (β h : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    {a b m : ℝ} (ha : 0≤a) (hab : a<b) (hb : b≤1)
    (hc : ∀s∈Ico a b,Paper.parisiCDF μ s=m) (l r : ℝ≥0)
    (hl : a<(l:ℝ)) (hlr : l≤r) (hr : (r:ℝ)<b) :
    TendstoInMeasure Paper.canonicalBrownianMeasure
      (fun n=>uniformAdaptedMartingaleLeftSumProcess (canonicalDiracShiftMartingale β l)
        (fun t sample=>Paper.parisiHessian β μ
          ((l:ℝ)+t,Paper.selectedParisiItoState β h hβ μ (l+t) sample))
        (r-l) (n+1) (r-l)) atTop
      (fun sample=>Paper.parisiGradient β μ ((r:ℝ),Paper.selectedParisiItoState β h hβ μ r sample)-
        Paper.parisiGradient β μ ((l:ℝ),Paper.selectedParisiItoState β h hβ μ l sample)) := by
  let u : ℝ→ℝ→ℝ:=fun t x=>Paper.parisiGradient β μ (t,x)
  let ut : ℝ→ℝ→ℝ:=cellTimeForcing β μ m 1
  let ux : ℝ→ℝ→ℝ:=fun t x=>Paper.parisiHessian β μ (t,x)
  let uxx : ℝ→ℝ→ℝ:=parisiSpatialJet β μ 3
  let f:=interiorCappedTest u a l r b
  let fR:=timeShiftTest f l
  let v : ℝ→ℝ→ℝ:=fun t x=>Paper.parisiGradient β μ (t,x)
  let hv : Continuous (Function.uncurry v):=continuous_parisiGradient β μ
  let hvb:=fun t x=>norm_parisiGradient_le_one β μ (t,x)
  let hvl:=lipschitzWith_parisiGradient β hβ μ
  let X:=canonicalParisiShiftState β h μ v hv hvb hvl l
  let d:=canonicalParisiShiftDrift β h μ v hv hvb hvl l
  let T:=r-l
  have hU : Continuous (fun p:ℝ×ℝ=>u p.1 p.2):=continuous_parisiGradient β μ
  have hUt : Continuous (fun p:ℝ×ℝ=>ut p.1 p.2):=continuous_cellTimeForcing β μ m 1
  have hUx : Continuous (fun p:ℝ×ℝ=>ux p.1 p.2):=continuous_parisiHessian_all β μ
  have hUxx : Continuous (fun p:ℝ×ℝ=>uxx p.1 p.2):=continuous_parisiSpatialJet_succ β μ 2
  have hut : ∀t∈Ioo a b,∀x,HasDerivAt (fun s=>u s x) (ut t x) t:=by
    intro t ht x
    simpa only [parisiSpatialJet_one] using
      hasDerivAt_constantCDF_spatialJet_time β hβ μ ha hab hb hc 1 ht x
  have hux : ∀t x,HasDerivAt (u t) (ux t x) x:=
    fun t x=>hasDerivAt_parisiGradient_spatial_all β μ t x
  have huxx : ∀t x,HasDerivAt (ux t) (uxx t x) x:=by
    intro t x
    simpa only [show 1+1=2 by norm_num,show 1+2=3 by norm_num,parisiSpatialJet_two] using hasDerivAt_parisiSpatialJet_succ β μ 1 t x
  have hC2 (t:ℝ):ContDiff ℝ 2 (u t):=(contDiff_parisiGradient_spatial β μ t).of_le (by simp)
  obtain ⟨hfc,hft,hfs,hfdt,hfx,hfxx⟩:=interiorCappedTest_regular u ut ux uxx a l r b
    hl (NNReal.coe_le_coe.mpr hlr) hr hU hUt hUx hUxx hut hux huxx hC2
  obtain ⟨hRc,hRt,hRs,hRdt,hRx,hRxx⟩:=timeShiftTest_regular f l hfc hft hfs hfdt hfx hfxx
  have hwindow {t:ℝ} (ht:t∈Icc (0:ℝ) (T:ℝ)):
      (l:ℝ)+t∈Icc (l:ℝ) (r:ℝ):=by
    have hT:(T:ℝ)=(r:ℝ)-l:=NNReal.coe_sub hlr
    constructor <;> linarith [ht.1,ht.2]
  have hgen : ∀ sample,∀t∈Icc (0:ℝ) (T:ℝ),hjbGenerator X d β fR t sample=0:=by
    intro sample t ht
    have htw:=hwindow ht
    have htc : (l:ℝ)+t∈Ico a b:=⟨hl.le.trans htw.1,htw.2.trans_lt hr⟩
    have ht1 : (l:ℝ)+t≤1:=htc.2.le.trans hb
    have htime:((l+t.toNNReal:ℝ≥0):ℝ)=(l:ℝ)+t:=by
      rw [NNReal.coe_add,Real.coe_toNNReal _ ht.1]
    have hd:d t.toNNReal sample=β^2*m*u ((l:ℝ)+t) (X t.toNNReal sample):=by
      change (if ((l+t.toNNReal:ℝ≥0):ℝ)≤1 then
        β^2*Paper.parisiCDF μ ((l+t.toNNReal:ℝ≥0):ℝ)*
          Paper.parisiGradient β μ (((l+t.toNNReal:ℝ≥0):ℝ),X t.toNNReal sample) else 0)=_
      rw [htime,ite_eq_left ht1,hc _ htc]
    unfold hjbGenerator
    rw [timeShiftTest_timeDerivative f l t _ hft,timeShiftTest_spaceDerivative,
      timeShiftTest_spaceSecondDerivative,
      interiorCappedTest_timeDerivative u ut a l r b hl (NNReal.coe_le_coe.mpr hlr) hr hut,
      interiorCappedTest_spaceDerivative u ux hux,
      interiorCappedTest_spaceSecondDerivative u ux uxx hux huxx,
      interiorTimeCap_eq _ _ _ _ _ htw,interiorTimeCapD_eq _ _ _ _ _ htw,hd]
    dsimp only [ut,ux,uxx,u]
    rw [cellTimeForcing_eq]
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.choose_zero_right,
      Nat.choose_self,Nat.cast_one,one_mul]
    norm_num
    ring
  have hconv:=ito_stochastic_leftSums_source
    (boundedDriftItoCharacteristics_canonicalParisiShift β h μ v hv hvb hvl l)
    fR hRc hRt hRs hRdt hRx hRxx T (fun _ _=>0) hgen
  have hleft (n:ℕ) (sample:Paper.BrownianSample):
      uniformAdaptedMartingaleLeftSumProcess (canonicalDiracShiftMartingale β l)
        (fun t sample=>itoSpaceDerivative fR t (X t sample)) T (n+1) T sample=
      uniformAdaptedMartingaleLeftSumProcess (canonicalDiracShiftMartingale β l)
        (fun t sample=>Paper.parisiHessian β μ
          ((l:ℝ)+t,Paper.selectedParisiItoState β h hβ μ (l+t) sample)) T (n+1) T sample:=by
    rw [uniformAdaptedMartingaleLeftSumProcess_terminal,uniformAdaptedMartingaleLeftSumProcess_terminal]
    apply Finset.sum_congr rfl
    intro i hi
    have hiT:(uniformPartitionTime T (n+1) i:ℝ)∈Icc (0:ℝ) (T:ℝ):=
      uniformPartitionTime_mem_Icc_of_le T (Nat.succ_pos n) (Nat.le_of_lt (Finset.mem_range.mp hi))
    rw [timeShiftTest_spaceDerivative,interiorCappedTest_spaceDerivative u ux hux,
      interiorTimeCap_eq _ _ _ _ _ (hwindow hiT)]
    rfl
  have heval (t:ℝ≥0) (ht:t∈Icc 0 T) (sample:Paper.BrownianSample):
      fR t (X t sample)=Paper.parisiGradient β μ
        ((l:ℝ)+t,Paper.selectedParisiItoState β h hβ μ (l+t) sample):=by
    have htR:(t:ℝ)∈Icc (0:ℝ) (T:ℝ):=⟨by exact_mod_cast ht.1,by exact_mod_cast ht.2⟩
    dsimp only [fR,timeShiftTest,f,interiorCappedTest,u]
    rw [interiorTimeCap_eq _ _ _ _ _ (hwindow htR)]
    rfl
  have hconv':=hconv.congr_left (fun n=>.of_forall (hleft n))
  apply TendstoInMeasure.congr_right _ hconv'
  exact .of_forall fun sample=>by
    have hTe:=heval T ⟨by positivity,le_rfl⟩ sample
    have h0e:=heval 0 ⟨by positivity,by positivity⟩ sample
    simp only [NNReal.coe_zero] at h0e
    change fR T (X T sample)-fR 0 (X 0 sample)-(∫s in (0:ℝ)..(T:ℝ),(0:ℝ))=_
    rw [hTe,h0e,intervalIntegral.integral_zero,sub_zero]
    simp only [add_zero,T,NNReal.coe_sub hlr,add_tsub_cancel_of_le hlr]
    rw [show (l:ℝ)+((r:ℝ)-l)=(r:ℝ) by ring]

end GeneralDepthPaper
