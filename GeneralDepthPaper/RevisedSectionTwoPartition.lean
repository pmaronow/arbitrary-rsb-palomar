module

public import GeneralDepthPaper.RevisedSectionTwoTemperature
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-! Every actual finite-support lower measure has the finite CDF partition
used by Lemma 3.1. Adding zero and the cutoff imposes no mass assumption
at either endpoint. In particular, the lower recursion is defined for all
finite atomic measures in the source theorem. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology Classical
namespace GeneralDepthPaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

structure SectionTwoFinitePartition (ν : ParisiMeasure) (qc : ℝ) where
  depth : ℕ
  node : Fin (depth+2)→TruncatedClockDomain qc
  strictMono : StrictMono node
  zero : (node 0:ℝ)=0
  last : (node (Fin.last (depth+1)):ℝ)=qc
  cdf_cell : ∀i:Fin (depth+1),∀s∈Ico (node i.castSucc:ℝ) (node i.succ:ℝ),
    Paper.parisiCDF ν s=Paper.parisiCDF ν (node i.castSucc)

theorem exists_sectionTwoFinitePartition (ν : ParisiMeasure)
    (hν : (ν:Measure Overlap).support.Finite) (qc : ℝ) (hc : 0<qc)
    (hs : ∀s∈FRSB.parisiSupport ν,s≤qc) :
    Nonempty (SectionTwoFinitePartition ν qc) := by
  let f : Overlap→TruncatedClockDomain qc := fun q=>
    ⟨min (q:ℝ) qc,⟨le_min q.property.1 hc.le,min_le_right _ _⟩⟩
  let a : TruncatedClockDomain qc:=⟨0,⟨le_rfl,hc.le⟩⟩
  let b : TruncatedClockDomain qc:=⟨qc,⟨hc.le,le_rfl⟩⟩
  let S : Finset (TruncatedClockDomain qc):=insert a (insert b (hν.toFinset.image f))
  have hab : a≠b := by intro h; have H:=congrArg Subtype.val h; exact hc.ne' H.symm
  have haS : a∈S := by simp [S]
  have hbS : b∈S := by simp [S]
  have hcard : 2≤S.card := by
    have hsub : ({a,b}:Finset (TruncatedClockDomain qc))⊆S := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl|hx
      · exact haS
      · exact Finset.mem_singleton.mp hx ▸ hbS
    have H:=Finset.card_le_card hsub
    simpa [hab] using H
  let r:=S.card-2
  have hcardeq : S.card=r+2 := by dsimp only [r]; omega
  let e : Fin (r+2)↪o TruncatedClockDomain qc:=S.orderEmbOfFin hcardeq
  have herange (x : TruncatedClockDomain qc) (hx : x∈S) : ∃j:Fin (r+2),e j=x := by
    let eS:=S.orderIsoOfFin hcardeq
    refine ⟨eS.symm ⟨x,hx⟩,?_⟩
    change (eS (eS.symm ⟨x,hx⟩)).val=x
    simp
  have hra : ∃j:Fin (r+2),e j=a := herange a haS
  have hrb : ∃j:Fin (r+2),e j=b := herange b hbS
  have he0 : (e 0:ℝ)=0 := by
    obtain ⟨j,hj⟩:=hra
    have H:=e.monotone (show (0:Fin (r+2))≤j from Nat.zero_le _)
    rw [hj] at H
    exact le_antisymm H (e 0).property.1
  have helast : (e (Fin.last (r+1)):ℝ)=qc := by
    obtain ⟨j,hj⟩:=hrb
    have H:=e.monotone (show j≤Fin.last (r+1) from Fin.le_last j)
    rw [hj] at H
    exact le_antisymm (e _).property.2 H
  have hsupport (q : Overlap) (hq : q∈(ν:Measure Overlap).support) :
      ∃j:Fin (r+2),(e j:ℝ)=(q:ℝ) := by
    have hqS : f q∈S := by
      apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      exact ⟨q,hν.mem_toFinset.mpr hq,rfl⟩
    obtain ⟨j,hj⟩:=herange (f q) hqS
    refine ⟨j,?_⟩
    rw [hj]
    exact min_eq_left (hs q ⟨q,hq,rfl⟩)
  refine ⟨⟨r,e,e.strictMono,he0,helast,?_⟩⟩
  intro i t ht
  have heq : {q:Overlap|(q:ℝ)≤t}=ᵐ[(ν:Measure Overlap)]
      {q:Overlap|(q:ℝ)≤(e i.castSucc:ℝ)} := by
    filter_upwards [(ν:Measure Overlap).support_mem_ae] with q hq
    obtain ⟨j,hj⟩:=hsupport q hq
    apply propext
    constructor
    · intro hqt
      by_contra hn
      have hij : i.castSucc<j := e.lt_iff_lt.mp (by
        change (e i.castSucc:ℝ)<(e j:ℝ)
        rw [hj]
        exact lt_of_not_ge hn)
      have hnext : i.succ≤j := by
        change i.val+1≤j.val
        exact Nat.succ_le_of_lt hij
      have H:=e.monotone hnext
      change (e i.succ:ℝ)≤(e j:ℝ) at H
      rw [hj] at H
      linarith [ht.2]
    · intro hqi
      exact hqi.trans ht.1
  unfold Paper.parisiCDF
  rw [measure_congr heq]

/-- An actual lower finite Gaussian recursion, chosen from the measure's
finite support by the preceding representation theorem. -/
def sectionTwoAtomicLowerData (Ξ : AdmissibleCovariance) (ν : ParisiMeasure)
    (hν : (ν:Measure Overlap).support.Finite)
    (m : ℝ) (hm : m∈Ioc (0:ℝ) 1) (qc : ℝ) (hc : qc∈Ioc (0:ℝ) 1)
    (hs : ∀s∈FRSB.parisiSupport ν,s≤qc) :
    TruncatedParisiData (Classical.choice (exists_sectionTwoFinitePartition ν hν qc hc.1 hs)).depth qc :=
  let p:=Classical.choice (exists_sectionTwoFinitePartition ν hν qc hc.1 hs)
  sectionTwoLowerData Ξ ν m hm qc hc p.node p.strictMono p.zero p.last

/-- Literal source-scope Lemma 3.1. The lower solution is independently
recursed from the finite atomic CDF and the scaled log-cosh terminal value;
its equality with the actual temperature-scaled solution is a theorem. -/
theorem revised_lemma_3_1_finite_atomic (Ξ : AdmissibleCovariance) (ν : ParisiMeasure)
    (hν : (ν:Measure Overlap).support.Finite)
    (m : ℝ) (hm : m∈Ioc (0:ℝ) 1) (qc : ℝ) (hc : qc∈Ioc (0:ℝ) 1)
    (hs : ∀s∈FRSB.parisiSupport ν,s<qc) :
    ∀q∈Icc (0:ℝ) qc,∀x,
      (sectionTwoAtomicLowerData Ξ ν hν m hm qc hc (fun s hs'=> (hs s hs').le)).potential q x=
        m⁻¹*potential (Ξ.temperatureScale m hm.1.ne') ν q (m*x)-
          m/2*(Ξ.first 1-Ξ.first qc) := by
  let p:=Classical.choice (exists_sectionTwoFinitePartition ν hν qc hc.1
    (fun s hs'=> (hs s hs').le))
  exact revised_lemma_3_1 Ξ ν m hm qc hc p.node p.strictMono p.zero p.last p.cdf_cell
    (fun s hs'=> (hs s hs').le)

end GeneralDepthPaper
