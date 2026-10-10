module

public import Mathlib

set_option backward.privateInPublic true

@[expose] public section


/-! Lemma 2.6: actual C² contact-set stability, proved by compactness and
strict concavity near each moving double zero. -/
noncomputable section
open Set Filter
open scoped Topology
namespace GeneralDepthPaper
set_option maxHeartbeats 600000

private theorem negative_away_of_strictConcave
    (f : ℝ→ℝ) {a b c x : ℝ} (hc : c∈Icc a b) (hx : x∈Icc a b)
    (hconc : StrictConcaveOn ℝ (Icc a b) f) (hd : HasDerivAt f 0 c)
    (hzero : f c=0) (hne : x≠c) : f x<0 := by
  rcases lt_or_gt_of_ne hne with hxc|hcx
  · have h := hconc.lt_slope_of_hasDerivAt hx hc hxc hd
    rw [slope_def_field,hzero,zero_sub] at h
    have hh := (lt_div_iff₀ (sub_pos.mpr hxc)).mp h
    linarith
  · have h := hconc.slope_lt_of_hasDerivAt hc hx hcx hd
    rw [slope_def_field,hzero,sub_zero] at h
    exact (div_lt_iff₀ (sub_pos.mpr hcx)).mp h |>.trans_eq (by ring)

private theorem negative_curvature_neighborhood
    (F : ℝ→ℝ) (f : ℕ→ℝ→ℝ) {bar c : ℝ}
    (hc : c∈Ioo (0:ℝ) bar) (hF : ContDiffOn ℝ 2 F (Icc (0:ℝ) bar))
    (hneg : deriv (deriv F) c<0)
    (hconv : TendstoUniformlyOn (fun n=>deriv (deriv (f n)))
      (deriv (deriv F)) atTop (Ioo (0:ℝ) bar)) :
    ∃ e>0, Icc (c-e) (c+e)⊆Ioo (0:ℝ) bar ∧
      ∀ᶠ n in atTop,∀ x∈Icc (c-e) (c+e),deriv (deriv (f n)) x<0 := by
  have hcd : ContDiffAt ℝ 2 F c := hF.contDiffAt (Icc_mem_nhds hc.1 hc.2)
  have hcont : ContinuousAt (deriv (deriv F)) c :=
    ((hcd.derivWithin (m:=1) (by norm_num)).derivWithin (m:=0) (by norm_num)).continuousAt
  have hn : {x : ℝ|x∈Ioo (0:ℝ) bar ∧ deriv (deriv F) x<deriv (deriv F) c/2}∈nhds c :=
    Filter.inter_mem (isOpen_Ioo.mem_nhds hc)
      (hcont.eventually (eventually_lt_nhds (by linarith :
        deriv (deriv F) c<deriv (deriv F) c/2)))
  obtain ⟨d,hd,hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨d/2,by positivity,?_,?_⟩
  · intro x hx
    apply (hball ?_).1
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    constructor <;> linarith [hx.1,hx.2]
  · have hε : 0< -(deriv (deriv F) c)/2 := by linarith
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hconv) _ hε] with n hn
    intro x hx
    have hb := hball (show x∈Metric.ball c d by
      rw [Metric.mem_ball,Real.dist_eq,abs_lt]
      constructor <;> linarith [hx.1,hx.2])
    have hh := hn x hb.1
    rw [Real.dist_eq,abs_lt] at hh
    linarith [hb.2,hh.1]

/-- The contact-set perturbation lemma. The finite positive contacts are
indexed by `Fin r`; the origin is fixed separately. Ordinary derivatives are
used only at interior contacts, and C² regularity is required on the literal
closed interval. -/
theorem contact_perturbation {r : ℕ} (F : ℝ→ℝ) (f : ℕ→ℝ→ℝ)
    (q : Fin r→ℝ) (qn : ℕ→Fin r→ℝ) {bar δ : ℝ}
    (hbar : 0<bar) (hbar1 : bar≤1) (hδ : 0<δ)
    (hF : ContDiffOn ℝ 2 F (Icc (0:ℝ) bar))
    (hf : ∀ n,ContDiffOn ℝ 2 (f n) (Icc (0:ℝ) bar))
    (hFle : ∀ x∈Icc (0:ℝ) bar,F x≤0)
    (hFzero : ∀ x∈Icc (0:ℝ) bar,F x=0 ↔ x=0 ∨ ∃ i,q i=x)
    (hq : ∀ i,q i∈Ioo (0:ℝ) bar)
    (hFneg : ∀ i,deriv (deriv F) (q i)<0)
    (hconv0 : TendstoUniformlyOn f F atTop (Icc (0:ℝ) bar))
    (hconv2 : TendstoUniformlyOn (fun n=>deriv (deriv (f n)))
      (deriv (deriv F)) atTop (Ioo (0:ℝ) bar))
    (hqn : ∀ i,Tendsto (fun n=>qn n i) atTop (nhds (q i)))
    (hzero : ∀ n,f n 0=0)
    (horigin : ∀ n,∀ x∈Ioc (0:ℝ) δ,f n x<0)
    (hcontact : ∀ n i,f n (qn n i)=0)
    (hcritical : ∀ n i,deriv (f n) (qn n i)=0) :
    ∀ᶠ n in atTop,
      (∀ x∈Icc (0:ℝ) bar,f n x≤0) ∧
      (∀ x∈Icc (0:ℝ) bar,f n x=0 ↔ x=0 ∨ ∃ i,x=qn n i) ∧
      (∀ i,deriv (deriv (f n)) (qn n i)<0) := by
  classical
  have hnb (i : Fin r) := negative_curvature_neighborhood F f (hq i) hF (hFneg i) hconv2
  choose e he hesub heneg using hnb
  have hqclose (i : Fin r) : ∀ᶠ n in atTop,qn n i∈Ioo (q i-e i) (q i+e i) :=
    (hqn i).eventually (isOpen_Ioo.mem_nhds ⟨by linarith [he i],by linarith [he i]⟩)
  have hcurv : ∀ᶠ n in atTop,∀ i,deriv (deriv (f n)) (qn n i)<0 := by
    apply eventually_all.mpr
    intro i
    filter_upwards [heneg i,hqclose i] with n hn hclose
    exact hn _ (Ioo_subset_Icc_self hclose)
  have hstrict : ∀ᶠ n in atTop,∀ x∈Icc (0:ℝ) bar,
      x≠0 → (∀ i,x≠qn n i) → f n x<0 := by
    by_contra h
    have hbad : ∃ᶠ n in atTop,∃ x∈Icc (0:ℝ) bar,
        x≠0 ∧ (∀ i,x≠qn n i) ∧ 0≤f n x := by
      have hn := not_eventually.mp h
      simpa only [not_forall,not_imp,not_lt,exists_prop] using hn
    obtain ⟨idx,hidx,hbadidx⟩ := extraction_of_frequently_atTop hbad
    choose x hx hxbad using hbadidx
    obtain ⟨c,hc,k,hk,hxc⟩ := isCompact_Icc.tendsto_subseq hx
    let nk : ℕ→ℕ := idx∘k
    let xk : ℕ→ℝ := x∘k
    have hnk : Tendsto nk atTop atTop := (hidx.comp hk).tendsto_atTop
    have hxk : Tendsto xk atTop (nhds c) := hxc
    have hxwithin : Tendsto xk atTop (nhdsWithin c (Icc (0:ℝ) bar)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hxk,.of_forall fun n=>hx (k n)⟩
    have hval : Tendsto (fun n=>f (nk n) (xk n)) atTop (nhds (F c)) :=
      (hconv0.seq_tendstoUniformlyOn nk hnk).tendsto_comp (hF.continuousOn c hc) hxwithin
    have hc0 : F c=0 := le_antisymm (hFle c hc)
      (le_of_tendsto_of_tendsto tendsto_const_nhds hval
        (.of_forall fun n=>(hxbad (k n)).2.2))
    rcases (hFzero c hc).mp hc0 with hc0|⟨i,hi⟩
    · have hevent : ∀ᶠ n in atTop,xk n<δ :=
        hxk.eventually (eventually_lt_nhds (by simpa only [hc0] using hδ))
      obtain ⟨n,hn⟩ := hevent.exists
      have hxp : 0<xk n := lt_of_le_of_ne (hx (k n)).1 (hxbad (k n)).1.symm
      have hh := horigin (nk n) (xk n) ⟨hxp,hn.le⟩
      exact (not_lt_of_ge (hxbad (k n)).2.2) hh
    · have hxclose : ∀ᶠ n in atTop,xk n∈Ioo (q i-e i) (q i+e i) := by
        rw [←hi] at hxk
        exact hxk.eventually (isOpen_Ioo.mem_nhds ⟨by linarith [he i],by linarith [he i]⟩)
      have hnc : ∀ᶠ n in atTop,∀ y∈Icc (q i-e i) (q i+e i),
          deriv (deriv (f (nk n))) y<0 := hnk.eventually (heneg i)
      have hqc := hnk.eventually (hqclose i)
      obtain ⟨n,⟨hn,hxn⟩,hcn⟩ := (hnc.and hxclose |>.and hqc).exists
      have hci : qn (nk n) i∈Icc (q i-e i) (q i+e i) := Ioo_subset_Icc_self hcn
      have hxi : xk n∈Icc (q i-e i) (q i+e i) := Ioo_subset_Icc_self hxn
      have hconc : StrictConcaveOn ℝ (Icc (q i-e i) (q i+e i)) (f (nk n)) := by
        apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _)
          ((hf (nk n)).continuousOn.mono (fun y hy=>Ioo_subset_Icc_self (hesub i hy)))
        intro y hy
        simpa only [Function.iterate_succ_apply',Function.iterate_zero_apply] using
          hn y (interior_subset hy)
      have hdiff : DifferentiableAt ℝ (f (nk n)) (qn (nk n) i) :=
        ((hf (nk n)).contDiffAt (Icc_mem_nhds (hesub i hci).1 (hesub i hci).2)).differentiableAt
          (by norm_num)
      have hder : HasDerivAt (f (nk n)) 0 (qn (nk n) i) := by
        simpa only [hcritical (nk n) i] using hdiff.hasDerivAt
      have hh := negative_away_of_strictConcave (f (nk n)) hci hxi hconc hder
        (hcontact (nk n) i) ((hxbad (k n)).2.1 i)
      exact (not_lt_of_ge (hxbad (k n)).2.2) hh
  filter_upwards [hstrict,hcurv] with n hn hcn
  refine ⟨?_,?_,hcn⟩
  · intro x hx
    by_cases hx0 : x=0
    · simp only [hx0,hzero n,le_refl]
    by_cases hxc : ∃ i,x=qn n i
    · obtain ⟨i,rfl⟩ := hxc
      exact (hcontact n i).le
    · exact (hn x hx hx0 (by simpa only [not_exists] using hxc)).le
  · intro x hx
    constructor
    · intro hzero'
      by_contra h
      push Not at h
      exact (ne_of_lt (hn x hx h.1 h.2)) hzero'
    · rintro (rfl|⟨i,rfl⟩)
      · exact hzero n
      · exact hcontact n i

/-- Derivatives intrinsic to the closed interval, including its one-sided
endpoint derivatives. This prevents the C² norm from depending on an
arbitrary extension outside the manuscript's interval. -/
def closedJet (bar : ℝ) (j : ℕ) (f : ℝ→ℝ) : ℝ→ℝ :=
  ((fun g : ℝ→ℝ=>derivWithin g (Icc (0:ℝ) bar))^[j]) f

private theorem closedJet_two_eq {bar x : ℝ} (f : ℝ→ℝ)
    (hx : x∈Ioo (0:ℝ) bar) : closedJet bar 2 f x=deriv (deriv f) x := by
  change derivWithin (derivWithin f (Icc (0:ℝ) bar)) (Icc (0:ℝ) bar) x=deriv (deriv f) x
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  exact derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)

/-- Literal closed-interval C² version of Lemma 2.6. Convergence controls
all intrinsic derivatives of orders zero through two uniformly, so arbitrary
extensions beyond either endpoint are irrelevant. -/
theorem contact_perturbation_closed_C2 {r : ℕ} (F : ℝ→ℝ) (f : ℕ→ℝ→ℝ)
    (q : Fin r→ℝ) (qn : ℕ→Fin r→ℝ) {bar δ : ℝ}
    (hbar : 0<bar) (hbar1 : bar≤1) (hδ : 0<δ)
    (hF : ContDiffOn ℝ 2 F (Icc (0:ℝ) bar))
    (hf : ∀n,ContDiffOn ℝ 2 (f n) (Icc (0:ℝ) bar))
    (hFle : ∀x∈Icc (0:ℝ) bar,F x≤0)
    (hFzero : ∀x∈Icc (0:ℝ) bar,F x=0 ↔ x=0 ∨ ∃i,q i=x)
    (hq : ∀i,q i∈Ioo (0:ℝ) bar)
    (hFneg : ∀i,closedJet bar 2 F (q i)<0)
    (hconv : ∀j≤2,TendstoUniformlyOn (fun n=>closedJet bar j (f n))
      (closedJet bar j F) atTop (Icc (0:ℝ) bar))
    (hqn : ∀i,Tendsto (fun n=>qn n i) atTop (nhds (q i)))
    (hzero : ∀n,f n 0=0)
    (horigin : ∀n,∀x∈Ioc (0:ℝ) δ,f n x<0)
    (hcontact : ∀n i,f n (qn n i)=0)
    (hcritical : ∀n i,deriv (f n) (qn n i)=0) :
    ∀ᶠ n in atTop,
      (∀x∈Icc (0:ℝ) bar,f n x≤0) ∧
      (∀x∈Icc (0:ℝ) bar,f n x=0 ↔ x=0 ∨ ∃i,x=qn n i) ∧
      (∀i,closedJet bar 2 (f n) (qn n i)<0) := by
  have hconv0 : TendstoUniformlyOn f F atTop (Icc (0:ℝ) bar) := by
    simpa only [closedJet,Function.iterate_zero_apply] using hconv 0 (by norm_num)
  have hconv2 : TendstoUniformlyOn (fun n=>deriv (deriv (f n)))
      (deriv (deriv F)) atTop (Ioo (0:ℝ) bar) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp (hconv 2 le_rfl)) ε hε] with n hn
    intro x hx
    have hh := hn x (Ioo_subset_Icc_self hx)
    simpa only [closedJet_two_eq F hx,closedJet_two_eq (f n) hx] using hh
  have hneg (i : Fin r) : deriv (deriv F) (q i)<0 := by
    simpa only [closedJet_two_eq F (hq i)] using hFneg i
  have hcore := contact_perturbation F f q qn hbar hbar1 hδ hF hf hFle hFzero hq
    hneg hconv0 hconv2 hqn hzero horigin hcontact hcritical
  have hinside : ∀ᶠ n in atTop,∀i,qn n i∈Ioo (0:ℝ) bar := by
    apply eventually_all.mpr
    intro i
    exact (hqn i).eventually (isOpen_Ioo.mem_nhds (hq i))
  filter_upwards [hcore,hinside] with n hn hi
  refine ⟨hn.1,hn.2.1,?_⟩
  intro i
  rw [closedJet_two_eq (f n) (hi i)]
  exact hn.2.2 i

end GeneralDepthPaper
