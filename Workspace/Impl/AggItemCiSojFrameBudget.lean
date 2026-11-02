import Workspace.Impl.AggItemCiSojFrameWt

/-! # The actual rectangle queue meets the global polynomial item bound -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang
open GI.Cited (Val)

/-- Every retained field and latest answer is a subvalue of the actual queue
input, so the input bound already pays for all four fields. -/
theorem itcs_queue_input_parts (payload : Val) (pending answers : List Val) (u : Val) {n : ℕ}
    (hw : (Val.list [.list [payload,.list pending,.list answers],u]).wt≤ n) :
    payload.wt≤ n ∧ (Val.list pending).wt≤ n ∧ (Val.list answers).wt≤ n ∧ u.wt≤ n := by
  have hk : (Val.list [payload,.list pending,.list answers]).wt≤ n :=
    (st_wt_mem (List.mem_cons_self ..)).trans hw
  exact ⟨(st_wt_mem (List.mem_cons_self ..)).trans hk,
    (st_wt_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))).trans hk,
    (st_wt_mem (by simp)).trans hk,
    (st_wt_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))).trans hw⟩

/-- The complete proved finalizer at any smaller actual input weight fits the
next monotone analysis budget. -/
theorem itcs_final_cost_next (pf : Prim) (Bc Br : ℕ → ℕ)
    (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W) {a n : ℕ} (ha : a≤ n) :
    itcsFinalC pf a≤ itcsGrow pf Bc Br hBc hBr n :=
  itcs_stage_cost_le pf Bc Br hBc hBr
    (f:=fun W => itcsFinalC pf W) (by simp only [itcsCostFns,List.mem_cons,List.not_mem_nil,or_false,true_or,or_true]) ha

/-- The actual queue costs at most two further analysis steps. This covers both
the pending-query branch and the finalizer call, with every field bound proved
from the encoded queue input. -/
theorem itcs_queue_global (pf : Prim) (Bc Br : ℕ → ℕ)
    (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W) (W n : ℕ)
    (hcap : n≤(itcsGrow pf Bc Br hBc hBr)^[126] (W+100))
    (payload : Val) (pending answers : List Val) (u : Val) {Cf : ℕ}
    (hp : payload.wt≤ n) (hn : (Val.list pending).wt≤ n) (ha : (Val.list answers).wt≤ n) (hu : u.wt≤ n)
    (hc : Cf≤ itcsGrow pf Bc Br hBc hBr n) :
    100*(itcsQueueW payload pending answers u Cf+1)+Cf≤ itcsXs pf Bc Br hBc hBr W := by
  have hg := itcs_grow_le pf Bc Br hBc hBr n
  have hscalar := itcs_queue_cost_scalar payload pending answers u
    (hp.trans hg) (hn.trans hg) (ha.trans hg) (hu.trans hg) hc
  have hwrap := itcs_wrapper_linear (itcsGrow pf Bc Br hBc hBr n)
  have hstage := itcs_stage_cost_le pf Bc Br hBc hBr (f:=itcsWrapperC)
    (by simp only [itcsCostFns,List.mem_cons,List.not_mem_nil,or_false,true_or,or_true])
    (a:=itcsGrow pf Bc Br hBc hBr n) (W:=itcsGrow pf Bc Br hBc hBr n) (le_refl _)
  exact hscalar.trans (hwrap.trans (hstage.trans (itcs_budget_tail pf Bc Br hBc hBr W hcap)))

end GI.Impl
