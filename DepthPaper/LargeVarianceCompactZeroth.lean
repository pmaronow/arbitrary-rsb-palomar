module

public import DepthPaper.LargeVarianceZeroth
public import Mathlib.Topology.Order.Compact

@[expose] public section


/-! Uniform zeroth-order Appendix B.1 estimate on every compact positive-mass
set. Higher mixed derivative claims are not included in this theorem. -/
noncomputable section
open Set
open scoped NNReal
namespace DepthPaper

 theorem largeVarianceError_uniform_zeroth {ε m:ℝ} (hε:0<ε) (hεm:ε≤m) (hm1:m≤1)
     (V:ℝ≥0) (hV:2*Real.log 2/ε^2≤(V:ℝ)) (x:ℝ) :
     |largeVarianceError m V x|≤(2/ε)*Real.exp (-(ε^2/2)*(V:ℝ)) := by
   have hm:0 < m:=hε.trans_le hεm
   have hs:ε^2≤m^2:=sq_le_sq₀ hε.le hm.le |>.mpr hεm
   have hbase:Real.log 2≤(V:ℝ)*ε^2/2:=by
     have hv':2*Real.log 2≤(V:ℝ)*ε^2:=(div_le_iff₀ (sq_pos_of_pos hε)).mp hV
     linarith
   have hlarge:2≤Real.exp ((V:ℝ)*m^2/2):=by
     calc
       (2:ℝ)=Real.exp (Real.log 2):=(Real.exp_log (by norm_num : (0:ℝ)<2)).symm
       _≤Real.exp ((V:ℝ)*m^2/2):=Real.exp_le_exp.mpr (hbase.trans (by gcongr))
   apply (largeVarianceError_zeroth_bound hm hm1 V hlarge x).trans
   have hcoef:2/m≤2/ε:=div_le_div_of_nonneg_left (by norm_num) hε hεm
   have hexp:Real.exp (-(V:ℝ)*m^2/2)≤Real.exp (-(ε^2/2)*(V:ℝ)):=by
     apply Real.exp_le_exp.mpr
     nlinarith [mul_le_mul_of_nonneg_left hs V.coe_nonneg]
   exact mul_le_mul hcoef hexp (Real.exp_pos _).le (div_pos (by norm_num) hε).le

 theorem largeVarianceError_compact_zeroth (I:Set ℝ) (hI:IsCompact I)
     (hsub:I⊆Ioc (0:ℝ) 1) :
     ∃Vbar c C:ℝ,1≤Vbar ∧ 0<c ∧ 0<C ∧
       ∀m∈I,∀V:ℝ≥0,Vbar≤(V:ℝ) → ∀x:ℝ,
         |largeVarianceError m V x|≤C*Real.exp (-c*(V:ℝ)) := by
   by_cases hne:I.Nonempty
   · obtain ⟨ε,hεI,hεmin⟩:=hI.exists_isMinOn hne continuousOn_id
     have hε:0<ε:=(hsub hεI).1
     refine ⟨max 1 (2*Real.log 2/ε^2),ε^2/2,2/ε,le_max_left _ _,by positivity,by positivity,?_⟩
     intro m hm V hV x
     exact largeVarianceError_uniform_zeroth hε (hεmin hm) (hsub hm).2 V
       ((le_max_right _ _).trans hV) x
   · refine ⟨1,1,1,le_rfl,by norm_num,by norm_num,?_⟩
     intro m hm
     exact (hne ⟨m,hm⟩).elim

end DepthPaper
