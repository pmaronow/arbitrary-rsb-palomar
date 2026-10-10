module

public import GeneralDepthPaper.NondegenerateStability

@[expose] public section


/-! The actual positive coefficient space of a fixed finite collection
of even exponents. Its nondegenerate finite-depth locus is open. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 1500000

def positiveCoefficientDomain (k : ℕ) : Set (Fin (k+1)→ℝ) :=
  {c|∀i,0<c i}

theorem isOpen_positiveCoefficientDomain (k : ℕ) : IsOpen (positiveCoefficientDomain k) := by
  have hh : positiveCoefficientDomain k=(⋂i:Fin (k+1),{c:Fin (k+1)→ℝ|0<c i}) := by
    ext c
    simp only [positiveCoefficientDomain,mem_setOf_eq,mem_iInter]
  rw [hh]
  exact isOpen_iInter_of_finite (fun i=>isOpen_lt continuous_const (continuous_apply i))

def indexedCovariance {k : ℕ} (p : Fin (k+1)→ℕ)
    (hp : ∀i,4≤p i) (he : ∀i,Even (p i))
    (c : Fin (k+1)→ℝ) (hc : c∈positiveCoefficientDomain k) : AdmissibleCovariance where
  degrees:=Finset.univ.image p
  nonempty:=⟨p 0,Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩⟩
  coefficient j:=c (Function.invFun p j)
  coefficient_pos j _:=hc _
  degree_ge_two j hj:=by
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hj
    have := hp i
    omega
  degree_even j hj:=by
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hj
    exact he i

theorem indexedCovariance_coefficient {k : ℕ} (p : Fin (k+1)→ℕ)
    (hp : ∀i,4≤p i) (he : ∀i,Even (p i)) (hinj : Function.Injective p)
    (c : Fin (k+1)→ℝ) (hc : c∈positiveCoefficientDomain k) (i : Fin (k+1)) :
    (indexedCovariance p hp he c hc).coefficient (p i)=c i := by
  exact congrArg c (Function.leftInverse_invFun hinj i)

theorem indexedCovariance_value {k : ℕ} (p : Fin (k+1)→ℕ)
    (hp : ∀i,4≤p i) (he : ∀i,Even (p i)) (hinj : Function.Injective p)
    (c : Fin (k+1)→ℝ) (hc : c∈positiveCoefficientDomain k) (q : ℝ) :
    (indexedCovariance p hp he c hc).value q=∑i,c i*q^(p i) := by
  change (∑j∈Finset.univ.image p,c (Function.invFun p j)*q^j)=_
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Function.leftInverse_invFun hinj i]
  · exact fun i _ j _ hij=>hinj hij

def finiteCoefficientFamily {k : ℕ} (p : Fin (k+1)→ℕ)
    (hp : ∀i,4≤p i) (he : ∀i,Even (p i)) :
    SmoothCovarianceFamily (Fin (k+1)→ℝ) where
  domain:=positiveCoefficientDomain k
  isOpen_domain:=isOpen_positiveCoefficientDomain k
  covariance c:=@dite AdmissibleCovariance (c∈positiveCoefficientDomain k) (Classical.propDecidable _)
    (fun hc=>indexedCovariance p hp he c hc)
    (fun _=>indexedCovariance p hp he (fun _=>1) (by intro i;norm_num))
  degrees:=Finset.univ.image p
  degrees_eq c hc:=by rw [dite_eq_left hc];rfl
  smooth_coefficient j _:=by
    intro c hc
    have H:∀ᶠu in 𝓝 c,u∈positiveCoefficientDomain k:=
      (isOpen_positiveCoefficientDomain k).mem_nhds hc
    apply ContDiffAt.contDiffWithinAt
    apply (contDiffAt_apply ℝ ℝ (Function.invFun p j) c).congr_of_eventuallyEq
    filter_upwards [H] with u hu
    simp only [dif_pos hu,indexedCovariance]

@[simp] theorem finiteCoefficientFamily_covariance {k : ℕ} (p : Fin (k+1)→ℕ)
    (hp : ∀i,4≤p i) (he : ∀i,Even (p i)) (c : Fin (k+1)→ℝ)
    (hc : c∈positiveCoefficientDomain k) :
    (finiteCoefficientFamily p hp he).covariance c=indexedCovariance p hp he c hc := by
  simp only [finiteCoefficientFamily,dif_pos hc]

def nondegenerateCoefficientLocus {k : ℕ} (p : Fin (k+1)→ℕ)
    (hp : ∀i,4≤p i) (he : ∀i,Even (p i)) (r : ℕ) : Set (Fin (k+1)→ℝ) :=
  {c|∃hc:c∈positiveCoefficientDomain k,∃z:AtomicPoint r,∃hz:IsAtomicPoint z,
    Nondegenerate (indexedCovariance p hp he c hc) z hz}

theorem isOpen_nondegenerateCoefficientLocus {k : ℕ} (p : Fin (k+1)→ℕ)
    (hp : ∀i,4≤p i) (he : ∀i,Even (p i)) (r : ℕ) :
    IsOpen (nondegenerateCoefficientLocus p hp he r) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro c ⟨hc,z,hz,hnd⟩
  let F:=finiteCoefficientFamily p hp he
  have hF : F.covariance c=indexedCovariance p hp he c hc:=
    finiteCoefficientFamily_covariance p hp he c hc
  obtain ⟨V,hV,hcV,hVD,zF,_,_,H⟩:=F.nondegenerate_stability hc z hz (hF.symm ▸ hnd)
  apply mem_of_superset (hV.mem_nhds hcV)
  intro u hu
  obtain ⟨hzu,Hnd⟩:=H u hu
  have hcu : u∈positiveCoefficientDomain k:=hVD hu
  refine ⟨hcu,zF u,hzu,?_⟩
  simpa only [F,finiteCoefficientFamily_covariance p hp he u hcu] using Hnd

theorem nondegenerateCoefficientLocus_depth {k : ℕ} (p : Fin (k+1)→ℕ)
    (hp : ∀i,4≤p i) (he : ∀i,Even (p i)) (r : ℕ)
    {c : Fin (k+1)→ℝ} (hc : c∈nondegenerateCoefficientLocus p hp he r) :
    ∃hpos:c∈positiveCoefficientDomain k,
      IsFiniteRSB r (parisiMinimizer (indexedCovariance p hp he c hpos)) := by
  obtain ⟨hpos,z,hz,hnd⟩:=hc
  refine ⟨hpos,?_⟩
  rw [←parisiMinimizer_unique _ _ hnd.1]
  exact atomicMeasure_isFiniteRSB z hz

end GeneralDepthPaper
