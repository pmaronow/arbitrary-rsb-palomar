module

public import FourPapersCommon.StationarySelector

@[expose] public section


/-! A genuinely smooth stationary branch on one open parameter neighborhood.
Smoothness of the equation on an open set, combined with local uniqueness,
glues the implicit branches at every point of the selected neighborhood. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace FourPapersCommon
variable {Θ E : Type*}
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_smooth_stationary_neighborhood
    (G : Θ × E → E →L[ℝ] ℝ) (U : Set (Θ × E)) (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) (p : Θ × E) (hp : p∈U) (hz : G p=0)
    (hB : ∀ u∈U,∀ v : E,v≠0 → 0 < (fderiv ℝ G u ∘L
      ContinuousLinearMap.inr ℝ Θ E) v v) :
    ∃ z : Θ → E,∃ V : Set Θ,IsOpen V ∧ p.1∈V ∧ z p.1=p.2 ∧
      ContDiffOn ℝ ∞ z V ∧ ∀ θ∈V,(θ,z θ)∈U ∧ G (θ,z θ)=0 := by
  have hGp : ContDiffAt ℝ ∞ G p := hG.contDiffAt (hU.mem_nhds hp)
  obtain ⟨z,hz0,hzr,hzs,hzu⟩ := exists_smooth_stationary_selector G p
    hGp (by norm_num) hz (hB p hp)
  obtain ⟨W,hWsub,hWopen,hpW⟩ := mem_nhds_iff.mp hzu
  have hpath : Tendsto (fun θ=>(θ,z θ)) (𝓝 p.1) (𝓝 p) := by
    simpa only [hz0,id_eq,Prod.mk.eta] using (continuousAt_id.prodMk hzr.continuousAt).tendsto
  have hpathmem : ∀ᶠ θ in 𝓝 p.1,(θ,z θ)∈U∩W :=
    hpath.eventually ((hU.inter hWopen).mem_nhds ⟨hp,hpW⟩)
  obtain ⟨V,hVsub,hVopen,hpV⟩ := mem_nhds_iff.mp (hpathmem.and hzs)
  refine ⟨z,V,hVopen,hpV,hz0,?_,?_⟩
  · intro θ hθ
    have hdata := hVsub hθ
    have hθU : (θ,z θ)∈U := hdata.1.1
    have hθW : (θ,z θ)∈W := hdata.1.2
    have hθz : G (θ,z θ)=0 := hdata.2
    have hGθ : ContDiffAt ℝ ∞ G (θ,z θ) := hG.contDiffAt (hU.mem_nhds hθU)
    obtain ⟨w,hw0,hwr,hws,_⟩ := exists_smooth_stationary_selector G (θ,z θ)
      hGθ (by norm_num) hθz (hB _ hθU)
    have hwpath : Tendsto (fun u=>(u,w u)) (𝓝 θ) (𝓝 (θ,z θ)) := by
      simpa only [hw0,id_eq] using (continuousAt_id.prodMk hwr.continuousAt).tendsto
    have hwmem : ∀ᶠ u in 𝓝 θ,(u,w u)∈W := hwpath.eventually (hWopen.mem_nhds hθW)
    have he : z =ᶠ[𝓝 θ] w := by
      filter_upwards [hwmem,hws] with u huW huG
      exact (hWsub huW).mp huG
    exact (hwr.congr_of_eventuallyEq he).contDiffWithinAt
  · intro θ hθ
    have hdata := hVsub hθ
    exact ⟨hdata.1.1,hdata.2⟩

end FourPapersCommon
