module

public import GeneralDepthPaper.TruncatedAtomicCoefficient
public import GeneralDepthPaper.TemperatureMassRecursion
public import GeneralDepthPaper.ScaledLogCoshTerminal
public import FRSB.FiniteSchemeRepresentation

@[expose] public section

/-! Independent lower Cole–Hopf recursion for the revised Lemma 3.1.
Its terminal value is `m⁻¹ log cosh(m x)`, its physical covariance is `Ξ`,
and each cell level is `m` times the actual lower measure's CDF.
The recursion is constructed before its temperature scaling identity is proved. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff NNReal
namespace GeneralDepthPaper
open ColeHopfFoundation.ProbabilityTheory
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

def sectionTwoCovarianceJet (Ξ : AdmissibleCovariance) (qc : ℝ) (j : Fin 4) :
    C(TruncatedClockDomain qc,ℝ) :=
  ⟨fun q=>iteratedDeriv j Ξ.value q,
    (Ξ.contDiff_value.continuous_iteratedDeriv j (by simp)).comp continuous_subtype_val⟩

theorem sectionTwoCovarianceJet_derivative (Ξ : AdmissibleCovariance)
    (qc : ℝ) (hc : 0 < qc) (j : Fin 3) (q : TruncatedClockDomain qc) :
    HasDerivWithinAt
      (fun t=>sectionTwoCovarianceJet Ξ qc j.castSucc (projIcc 0 qc hc.le t))
      (sectionTwoCovarianceJet Ξ qc j.succ q) (Icc (0:ℝ) qc) q := by
  have hd:=(Ξ.contDiff_value.differentiable_iteratedDeriv j
    (by exact_mod_cast ENat.natCast_lt_top (j:ℕ)) q).hasDerivAt
  rw [←iteratedDeriv_succ] at hd
  apply hd.hasDerivWithinAt.congr
  · intro t ht
    simp only [sectionTwoCovarianceJet,ContinuousMap.coe_mk,projIcc_of_mem hc.le ht]
    rfl
  · simp only [sectionTwoCovarianceJet,ContinuousMap.coe_mk,projIcc_of_mem hc.le q.property,
      Fin.val_castSucc]

@[simp] theorem sectionTwoCovarianceJet_one (Ξ : AdmissibleCovariance)
    (qc : ℝ) (q : TruncatedClockDomain qc) : sectionTwoCovarianceJet Ξ qc 1 q=Ξ.first q := by
  change iteratedDeriv 1 Ξ.value q=Ξ.first q
  rw [iteratedDeriv_covariance_one]

@[simp] theorem sectionTwoCovarianceJet_two (Ξ : AdmissibleCovariance)
    (qc : ℝ) (q : TruncatedClockDomain qc) : sectionTwoCovarianceJet Ξ qc 2 q=Ξ.second q := by
  change iteratedDeriv 2 Ξ.value q=Ξ.second q
  rw [iteratedDeriv_covariance_two]

def sectionTwoLowerData (Ξ : AdmissibleCovariance) (ν : ParisiMeasure)
    (m : ℝ) (hm : m∈Ioc (0:ℝ) 1) (qc : ℝ) (hc : qc∈Ioc (0:ℝ) 1)
    {r : ℕ} (node : Fin (r+2)→TruncatedClockDomain qc)
    (hn : StrictMono node) (h0 : (node 0:ℝ)=0)
    (hlast : (node (Fin.last (r+1)):ℝ)=qc) : TruncatedParisiData r qc where
  qc_pos := hc.1
  covarianceJet := sectionTwoCovarianceJet Ξ qc
  covariance_derivative := sectionTwoCovarianceJet_derivative Ξ qc hc.1
  covariance_second_nonneg := fun q=>by
    rw [sectionTwoCovarianceJet_two]
    exact Ξ.second_nonneg q.property.1
  node := node
  node_strictMono := hn
  node_zero := h0
  node_last := hlast
  level := fun i=>m*Paper.parisiCDF ν (node i.castSucc)
  level_mem := fun i=>⟨mul_nonneg hm.1.le (Paper.parisiCDF_nonneg ν _),
    (mul_le_mul_of_nonneg_left (Paper.parisiCDF_le_one ν _) hm.1.le).trans (by simpa using hm.2)⟩
  terminal := scaledLogCoshTerminal m
  terminal_first_bound := norm_terminalJet_scaledLogCoshTerminal_le_one m

theorem sectionTwoLowerData_covarianceField_one (Ξ : AdmissibleCovariance) (ν : ParisiMeasure)
    (m : ℝ) (hm : m∈Ioc (0:ℝ) 1) (qc : ℝ) (hc : qc∈Ioc (0:ℝ) 1)
    {r : ℕ} (node : Fin (r+2)→TruncatedClockDomain qc)
    (hn : StrictMono node) (h0 : (node 0:ℝ)=0)
    (hlast : (node (Fin.last (r+1)):ℝ)=qc) (q : ℝ) (hq : q∈Icc (0:ℝ) qc) :
    (sectionTwoLowerData Ξ ν m hm qc hc node hn h0 hlast).covarianceField 1 q=Ξ.first q := by
  simp only [TruncatedParisiData.covarianceField,sectionTwoLowerData,
    sectionTwoCovarianceJet_one,projIcc_of_mem hc.1.le hq]

theorem sectionTwoLowerData_covarianceField_two (Ξ : AdmissibleCovariance) (ν : ParisiMeasure)
    (m : ℝ) (hm : m∈Ioc (0:ℝ) 1) (qc : ℝ) (hc : qc∈Ioc (0:ℝ) 1)
    {r : ℕ} (node : Fin (r+2)→TruncatedClockDomain qc)
    (hn : StrictMono node) (h0 : (node 0:ℝ)=0)
    (hlast : (node (Fin.last (r+1)):ℝ)=qc) (q : ℝ) (hq : q∈Icc (0:ℝ) qc) :
    (sectionTwoLowerData Ξ ν m hm qc hc node hn h0 hlast).covarianceField 2 q=Ξ.second q := by
  simp only [TruncatedParisiData.covarianceField,sectionTwoLowerData,
    sectionTwoCovarianceJet_two,projIcc_of_mem hc.1.le hq]

theorem exists_sectionTwo_right_cell {r : ℕ} {qc : ℝ}
    (node : Fin (r+2)→TruncatedClockDomain qc)
    (h0 : (node 0:ℝ)=0) (hlast : (node (Fin.last (r+1)):ℝ)=qc)
    (q : ℝ) (hq : q∈Ico (0:ℝ) qc) :
    ∃i:Fin (r+1),q∈Ico (node i.castSucc:ℝ) (node i.succ:ℝ) := by
  classical
  have hex : ∃i:Fin (r+2),q<(node i:ℝ) :=
    ⟨Fin.last (r+1),by simpa only [hlast] using hq.2⟩
  let j:=Fin.find (fun i:Fin (r+2)=>q<(node i:ℝ)) hex
  have hj:=Fin.find_spec hex
  have hj0 : j≠0 := by
    intro he
    change q<(node j:ℝ) at hj
    rw [he,h0] at hj
    exact (not_lt_of_ge hq.1) hj
  obtain ⟨i,hi⟩:=Fin.exists_succ_eq_of_ne_zero hj0
  refine ⟨i,?_,?_⟩
  · exact le_of_not_gt (Fin.find_min hex (show i.castSucc<j by rw [←hi]; exact i.castSucc_lt_succ))
  · change q<(node j:ℝ) at hj
    simpa only [←hi] using hj

theorem sectionTwoLowerData_coefficient (Ξ : AdmissibleCovariance) (ν : ParisiMeasure)
    (m : ℝ) (hm : m∈Ioc (0:ℝ) 1) (qc : ℝ) (hc : qc∈Ioc (0:ℝ) 1)
    {r : ℕ} (node : Fin (r+2)→TruncatedClockDomain qc)
    (hn : StrictMono node) (h0 : (node 0:ℝ)=0)
    (hlast : (node (Fin.last (r+1)):ℝ)=qc)
    (hCDF : ∀i:Fin (r+1),∀s∈Ico (node i.castSucc:ℝ) (node i.succ:ℝ),
      Paper.parisiCDF ν s=Paper.parisiCDF ν (node i.castSucc))
    (q : ℝ) (hq : q∈Ico (0:ℝ) qc) :
    (sectionTwoLowerData Ξ ν m hm qc hc node hn h0 hlast).coefficient q=m*Paper.parisiCDF ν q := by
  obtain ⟨i,hi⟩:=exists_sectionTwo_right_cell node h0 hlast q hq
  rw [hCDF i q hi]
  exact truncatedCoefficient_eq_level
    (sectionTwoLowerData Ξ ν m hm qc hc node hn h0 hlast).parameter hn.monotone q i hi

theorem sectionTwoLowerData_potential (Ξ : AdmissibleCovariance) (ν : ParisiMeasure)
    (m : ℝ) (hm : m∈Ioc (0:ℝ) 1) (qc : ℝ) (hc : qc∈Ioc (0:ℝ) 1)
    {r : ℕ} (node : Fin (r+2)→TruncatedClockDomain qc)
    (hn : StrictMono node) (h0 : (node 0:ℝ)=0)
    (hlast : (node (Fin.last (r+1)):ℝ)=qc)
    (hCDF : ∀i:Fin (r+1),∀s∈Ico (node i.castSucc:ℝ) (node i.succ:ℝ),
      Paper.parisiCDF ν s=Paper.parisiCDF ν (node i.castSucc))
    (hs : ∀s∈FRSB.parisiSupport ν,s≤qc)
    (q : ℝ) (hq : q∈Icc (0:ℝ) qc) (x : ℝ) :
    (sectionTwoLowerData Ξ ν m hm qc hc node hn h0 hlast).potential q x=
      temperatureMassPotential Ξ ν m qc q x := by
  let d:=sectionTwoLowerData Ξ ν m hm qc hc node hn h0 hlast
  let p:=d.parameter
  let qI:TruncatedClockDomain qc:=⟨q,hq⟩
  let u:Fin (r+2)→ℝ→ℝ:=fun i y=>temperatureMassPotential Ξ ν m qc (max q (node i:ℝ)) y
  have hfirst : ∀a:TruncatedClockDomain qc,p.1 a=Ξ.first a := fun a=>sectionTwoCovarianceJet_one Ξ qc a
  have hnode : ∀i:Fin (r+2),p.2.1 i=node i := fun _=>rfl
  have hlevel : ∀i:Fin (r+1),p.2.2.1 i=m*Paper.parisiCDF ν (node i.castSucc) := fun _=>rfl
  have hstep (i : Fin (r+1)) (y : ℝ) :
      u i.castSucc y=coleHopf (truncatedStepData p qI i).1
        (truncatedStepData p qI i).2.toNNReal (u i.succ) y := by
    by_cases hqi : (node i.succ:ℝ)≤q
    · have hlow : (node i.castSucc:ℝ)≤q :=
        (show (node i.castSucc:ℝ)≤node i.succ from hn.monotone i.castSucc_lt_succ.le).trans hqi
      have hcl : truncatedClamp p.2.1 i qI=p.2.1 i.succ :=
        truncatedClamp_eq_upper_of_le _ _ _ hqi
      simp only [u,max_eq_left hlow,max_eq_left hqi,truncatedStepData,hcl,sub_self,
        Real.toNNReal_zero,coleHopf_zero_var]
    · have hqu : q<(node i.succ:ℝ) := lt_of_not_ge hqi
      have hnodes : (node i.castSucc:ℝ)<node i.succ := hn i.castSucc_lt_succ
      have hlt : max q (node i.castSucc:ℝ)<node i.succ := max_lt hqu hnodes
      have hL : max q (node i.castSucc:ℝ)∈Icc (0:ℝ) 1 :=
        ⟨hq.1.trans (le_max_left _ _),max_le (hq.2.trans hc.2) ((node i.castSucc).property.2.trans hc.2)⟩
      have hcl : (truncatedClamp p.2.1 i qI:ℝ)=max q (node i.castSucc:ℝ) := by
        change min (max q (node i.castSucc:ℝ)) (node i.succ:ℝ)=_
        exact min_eq_left hlt.le
      have H:=temperatureMassPotential_coleHopf Ξ ν m hm.1 qc hL
        ⟨(node i.succ).property.1,(node i.succ).property.2.trans hc.2⟩ hlt
        (fun s hs'=>hCDF i s ⟨(le_max_right _ _).trans hs'.1,hs'.2⟩) y
      simp only [truncatedStepData,hlevel,hfirst,hcl,hnode]
      simpa only [u,max_eq_right hqu.le] using H
  have ht (y : ℝ) : u (Fin.last (r+1)) y=terminalValue (scaledLogCoshTerminal m) y := by
    simp only [u,hlast,max_eq_right hq.2]
    exact temperatureMassPotential_terminal Ξ ν m hm.1 ⟨hc.1.le,hc.2⟩ hs y
  have H:=coleHopf_chain_eq_recursion_nonneg (r+1) (truncatedStepData p qI)
    (scaledLogCoshTerminal m) u (fun i=>truncatedStepData_nonneg p d.first_monotone qI i) ht hstep x
  change terminalValue (truncatedPotentialTerminal p (projIcc 0 qc hc.1.le q)) x=
    temperatureMassPotential Ξ ν m qc q x
  rw [projIcc_of_mem hc.1.le hq]
  simpa only [u,h0,max_eq_left hq.1,truncatedPotentialTerminal,p,d,qI,
    TruncatedParisiData.parameter,sectionTwoLowerData] using H.symm

theorem sectionTwoLowerData_spatialField_zero (Ξ : AdmissibleCovariance) (ν : ParisiMeasure)
    (m : ℝ) (hm : m∈Ioc (0:ℝ) 1) (qc : ℝ) (hc : qc∈Ioc (0:ℝ) 1)
    {r : ℕ} (node : Fin (r+2)→TruncatedClockDomain qc)
    (hn : StrictMono node) (h0 : (node 0:ℝ)=0)
    (hlast : (node (Fin.last (r+1)):ℝ)=qc)
    (hCDF : ∀i:Fin (r+1),∀s∈Ico (node i.castSucc:ℝ) (node i.succ:ℝ),
      Paper.parisiCDF ν s=Paper.parisiCDF ν (node i.castSucc))
    (hs : ∀s∈FRSB.parisiSupport ν,s≤qc)
    (q : ℝ) (hq : q∈Icc (0:ℝ) qc) (x : ℝ) :
    (sectionTwoLowerData Ξ ν m hm qc hc node hn h0 hlast).spatialField 0 (q,x)=
      temperatureMassGradient Ξ ν m q x := by
  have hd:=hasDerivAt_temperatureMassPotential_spatial Ξ ν m hm.1 qc q x
    ⟨hq.1,hq.2.trans hc.2⟩
  have he : temperatureMassPotential Ξ ν m qc q=
      (fun y=>(sectionTwoLowerData Ξ ν m hm qc hc node hn h0 hlast).potential q y) :=
    funext fun y=>(sectionTwoLowerData_potential Ξ ν m hm qc hc node hn h0 hlast hCDF hs q hq y).symm
  rw [he] at hd
  exact (hd.unique (hasDerivAt_terminalValue
    (truncatedPotentialTerminal (sectionTwoLowerData Ξ ν m hm qc hc node hn h0 hlast).parameter
      (projIcc 0 qc hc.1.le q)) x)).symm

theorem sectionTwoLowerData_spatialField_one (Ξ : AdmissibleCovariance) (ν : ParisiMeasure)
    (m : ℝ) (hm : m∈Ioc (0:ℝ) 1) (qc : ℝ) (hc : qc∈Ioc (0:ℝ) 1)
    {r : ℕ} (node : Fin (r+2)→TruncatedClockDomain qc)
    (hn : StrictMono node) (h0 : (node 0:ℝ)=0)
    (hlast : (node (Fin.last (r+1)):ℝ)=qc)
    (hCDF : ∀i:Fin (r+1),∀s∈Ico (node i.castSucc:ℝ) (node i.succ:ℝ),
      Paper.parisiCDF ν s=Paper.parisiCDF ν (node i.castSucc))
    (hs : ∀s∈FRSB.parisiSupport ν,s≤qc)
    (q : ℝ) (hq : q∈Icc (0:ℝ) qc) (x : ℝ) :
    (sectionTwoLowerData Ξ ν m hm qc hc node hn h0 hlast).spatialField 1 (q,x)=
      temperatureMassHessian Ξ ν m q x := by
  have hd:=hasDerivAt_temperatureMassGradient_spatial Ξ ν m q x
  have he : temperatureMassGradient Ξ ν m q=
      (fun y=>(sectionTwoLowerData Ξ ν m hm qc hc node hn h0 hlast).spatialField 0 (q,y)) :=
    funext fun y=>(sectionTwoLowerData_spatialField_zero Ξ ν m hm qc hc node hn h0 hlast hCDF hs q hq y).symm
  rw [he] at hd
  exact (hd.unique (hasDerivAt_truncatedSpatialField_zero hc.1.le
    (sectionTwoLowerData Ξ ν m hm qc hc node hn h0 hlast).parameter q x)).symm

/-- Exact revised Lemma 3.1, for any finite CDF grid of the actual measure,
with no requirement that the origin be an atom or that its mass be positive. -/
theorem revised_lemma_3_1 (Ξ : AdmissibleCovariance) (ν : ParisiMeasure)
    (m : ℝ) (hm : m∈Ioc (0:ℝ) 1) (qc : ℝ) (hc : qc∈Ioc (0:ℝ) 1)
    {r : ℕ} (node : Fin (r+2)→TruncatedClockDomain qc)
    (hn : StrictMono node) (h0 : (node 0:ℝ)=0)
    (hlast : (node (Fin.last (r+1)):ℝ)=qc)
    (hCDF : ∀i:Fin (r+1),∀s∈Ico (node i.castSucc:ℝ) (node i.succ:ℝ),
      Paper.parisiCDF ν s=Paper.parisiCDF ν (node i.castSucc))
    (hs : ∀s∈FRSB.parisiSupport ν,s≤qc) :
    ∀q∈Icc (0:ℝ) qc,∀x,
      (sectionTwoLowerData Ξ ν m hm qc hc node hn h0 hlast).potential q x=
        m⁻¹*potential (Ξ.temperatureScale m hm.1.ne') ν q (m*x)-
          m/2*(Ξ.first 1-Ξ.first qc) := by
  intro q hq x
  rw [sectionTwoLowerData_potential Ξ ν m hm qc hc node hn h0 hlast hCDF hs q hq x]
  simp only [temperatureMassPotential,temperatureCovarianceFamily_covariance Ξ m hm.1.ne']

end GeneralDepthPaper
