module

public import DepthPaper.CompactTiltUniformBounds
public import DepthPaper.CenteredColeHopfValue

@[expose] public section


/-! Fixed-reference precision substitution preserves uniform bounds on all
parameter derivatives over a bounded terminal ball and a positive variance
rectangle. The argument does not divide by the mass parameter. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff
namespace DepthPaper
set_option maxSynthPendingDepth 64

def coleHopfBall (A Vlo Vhi B : ℝ) : Set ColeHopfParameter :=
  {p|‖p.1.1‖≤A ∧ Vlo≤p.1.2 ∧ p.1.2≤Vhi ∧ ‖p.2‖≤B}

theorem norm_coleHopfBall_le (A Vlo Vhi B : ℝ) (hVlo : 0<Vlo)
    (p : ColeHopfParameter) (hp : p∈coleHopfBall A Vlo Vhi B) :
    ‖p‖≤max A (max Vhi B) := by
  rw [Prod.norm_def,Prod.norm_def,Real.norm_of_nonneg (hVlo.trans_le hp.2.1).le]
  exact max_le (max_le (hp.1.trans (le_max_left _ _))
    (hp.2.2.1.trans ((le_max_left Vhi B).trans (le_max_right _ _))))
    (hp.2.2.2.trans ((le_max_right Vhi B).trans (le_max_right _ _)))

theorem boundedSmoothOn_coleHopf_first (A Vlo Vhi B : ℝ)
    (hA : 0≤A) (hVlo : 0<Vlo) :
    BoundedSmoothOn (fun p:ColeHopfParameter=>p.1.1) (coleHopfBall A Vlo Vhi B) :=
  BoundedSmoothOn.linear
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ×ℝ) TerminalSpace))
    _ _ (hA.trans (le_max_left _ _)) (norm_coleHopfBall_le A Vlo Vhi B hVlo)

theorem boundedSmoothOn_coleHopf_variance (A Vlo Vhi B : ℝ)
    (hA : 0≤A) (hVlo : 0<Vlo) :
    BoundedSmoothOn (fun p:ColeHopfParameter=>p.1.2) (coleHopfBall A Vlo Vhi B) :=
  BoundedSmoothOn.linear
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ×ℝ) TerminalSpace))
    _ _ (hA.trans (le_max_left _ _)) (norm_coleHopfBall_le A Vlo Vhi B hVlo)

theorem boundedSmoothOn_coleHopf_terminal (A Vlo Vhi B : ℝ)
    (hA : 0≤A) (hVlo : 0<Vlo) :
    BoundedSmoothOn (fun p:ColeHopfParameter=>p.2) (coleHopfBall A Vlo Vhi B) :=
  BoundedSmoothOn.linear (ContinuousLinearMap.snd ℝ (ℝ×ℝ) TerminalSpace)
    _ _ (hA.trans (le_max_left _ _)) (norm_coleHopfBall_le A Vlo Vhi B hVlo)

theorem gaussianPrecisionDifference_bounds (Vlo Vhi v : ℝ) (hVlo : 0<Vlo)
    (hV : Vlo≤Vhi) (hv : v∈Icc Vlo Vhi) :
    gaussianPrecisionDifference Vhi (2*Vhi)≤gaussianPrecisionDifference v (2*Vhi) ∧
    gaussianPrecisionDifference v (2*Vhi)≤gaussianPrecisionDifference Vlo (2*Vhi) := by
  have hvlo := hv.1
  have hvhi := hv.2
  have hvpos := hVlo.trans_le hvlo
  unfold gaussianPrecisionDifference
  constructor
  · exact sub_le_sub_right (one_div_le_one_div_of_le (by positivity) (by linarith)) _
  · exact sub_le_sub_right (one_div_le_one_div_of_le (by positivity) (by linarith)) _

theorem boundedSmoothOn_coleHopf_precision (A Vlo Vhi B : ℝ)
    (hA : 0≤A) (hVlo : 0<Vlo) :
    BoundedSmoothOn (fun p:ColeHopfParameter=>gaussianPrecisionDifference p.1.2 (2*Vhi))
      (coleHopfBall A Vlo Vhi B) := by
  have hprec : BoundedSmoothOn (fun v:ℝ=>gaussianPrecisionDifference v (2*Vhi))
      (Icc Vlo Vhi) := BoundedSmoothOn.of_compact isCompact_Icc (fun v hv=>by
        have hvpos := hVlo.trans_le hv.1
        have h2 : 2*v≠0 := by positivity
        unfold gaussianPrecisionDifference
        fun_prop (disch:=assumption))
  exact hprec.comp (boundedSmoothOn_coleHopf_variance A Vlo Vhi B hA hVlo)
    (fun p hp=>⟨hp.2.1,hp.2.2.1⟩)

theorem boundedSmoothOn_centeredColeHopfValue (A Vlo Vhi B : ℝ)
    (hA : 0≤A) (hVlo : 0<Vlo) (hV : Vlo≤Vhi) (hB : 0≤B) :
    BoundedSmoothOn centeredColeHopfValue (coleHopfBall A Vlo Vhi B) := by
  let w := 2*Vhi
  let ρ := gaussianPrecisionDifference Vhi w
  let R := gaussianPrecisionDifference Vlo w
  have hVhi : 0<Vhi := hVlo.trans_le hV
  have hρ : 0<ρ := gaussianPrecisionDifference_pos hVhi (by dsimp [w]; linarith)
  have hR : 0≤R := (gaussianPrecisionDifference_pos hVlo (by dsimp [w]; linarith)).le
  have hg := boundedSmoothOn_coleHopf_terminal A Vlo Vhi B hA hVlo
  have ha := boundedSmoothOn_coleHopf_first A Vlo Vhi B hA hVlo
  have hb := boundedSmoothOn_coleHopf_precision A Vlo Vhi B hA hVlo
  have hag := ha.bilinear hg (ContinuousLinearMap.lsmul ℝ ℝ : ℝ→L[ℝ] TerminalSpace→L[ℝ] TerminalSpace)
  have hparam := (hb.prodMk (hag.prodMk (BoundedSmoothOn.const (0:TerminalSpace) _))).prodMk hg
  have hresp := (boundedSmoothOn_compactTiltResponse w.toNNReal ρ R (A*B) B hρ hR
    (mul_nonneg hA hB) hB).comp hparam (fun p hp=>by
      refine ⟨⟨?_,?_,?_⟩,hp.2.2.2⟩
      · exact (gaussianPrecisionDifference_bounds Vlo Vhi p.1.2 hVlo hV ⟨hp.2.1,hp.2.2.1⟩).1
      · exact (gaussianPrecisionDifference_bounds Vlo Vhi p.1.2 hVlo hV ⟨hp.2.1,hp.2.2.1⟩).2
      · change ‖p.1.1 • p.2‖+‖(0:TerminalSpace)‖≤A*B
        rw [norm_zero,add_zero,norm_smul]
        exact mul_le_mul hp.1 hp.2.2.2 (norm_nonneg _) hA)
  have href := hresp.compCLM unitTiltAverageCLM
  apply href.congr_of_eventuallyEq
  intro p hp
  have hv : 0<p.1.2 := hVlo.trans_le hp.2.1
  have hvw : p.1.2<w := hp.2.2.1.trans_lt (by dsimp [w]; linarith)
  have hlocal : ∀ᶠq:ColeHopfParameter in 𝓝 p,0<q.1.2 ∧ q.1.2<w :=
    ((continuous_snd.comp continuous_fst).tendsto p) (Ioo_mem_nhds hv hvw)
  filter_upwards [hlocal] with q hq
  ext x
  exact (referenceCenteredColeHopfValue_apply w q hq.1 hq.2 x).trans
    (centeredColeHopfValue_apply q hq.1 x).symm

end DepthPaper
