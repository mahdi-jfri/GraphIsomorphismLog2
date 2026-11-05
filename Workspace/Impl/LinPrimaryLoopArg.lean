module

public import Workspace.Impl.LinPrimaryLoopTerminal

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

def linPrimaryLoopArgE : Expr :=
  .snoc (.snoc (mk4 (.get (arg 2) (.nat 0)) (.get (arg 2) (.nat 1))
    (.get (arg 2) (.nat 2)) (.get (arg 0) (.nat 3))) (.get (arg 0) (.nat 4))) (arg 1)

set_option maxHeartbeats 1000000 in
theorem linPrimaryLoopArg_spec {P : Program} {d : ℕ} (v1 v2 v3 c1 c2 c3 : Val)
    (p : ℕ) (ν : Fin d → ℕ) (j : ℕ) :
    let orig := Val.list [v1, v2, v3, .nat p, encFun ν]
    let cur := Val.list [c1, c2, c3]
    let a := Val.list [orig, .nat j, cur]
    Det P [a] linPrimaryLoopArgE (.list [c1, c2, c3, .nat p, encFun ν, .nat j]) (100000 * (a.wt + 1)) := by
  let orig := Val.list [v1, v2, v3, .nat p, encFun ν]
  let cur := Val.list [c1, c2, c3]
  let a := Val.list [orig, .nat j, cur]
  have wo : orig.wt < a.wt := wt_le_wt_list (by simp [a])
  have wc : cur.wt < a.wt := wt_le_wt_list (by simp [a])
  have wj : (Val.nat j).wt < a.wt := wt_le_wt_list (by simp [a])
  have w1 : c1.wt < cur.wt := wt_le_wt_list (by simp [cur])
  have w2 : c2.wt < cur.wt := wt_le_wt_list (by simp [cur])
  have w3 : c3.wt < cur.wt := wt_le_wt_list (by simp [cur])
  have wp : (Val.nat p).wt < orig.wt := wt_le_wt_list (by simp [orig])
  have wν : (encFun ν).wt < orig.wt := wt_le_wt_list (by simp [orig])
  have do' := Det.arg' (P := P) (vs := [orig, .nat j, cur]) (rest := []) (j := 0) rfl
  have dc := Det.arg' (P := P) (vs := [orig, .nat j, cur]) (rest := []) (j := 2) rfl
  have dj := Det.arg' (P := P) (vs := [orig, .nat j, cur]) (rest := []) (j := 1) rfl
  have d1 := Det.get' dc (Det.nat 0) rfl
  have d2 := Det.get' dc (Det.nat 1) rfl
  have d3 := Det.get' dc (Det.nat 2) rfl
  have dp := Det.get' do' (Det.nat 3) rfl
  have dν := Det.get' do' (Det.nat 4) rfl
  have dd := Det.snoc (Det.snoc (Det.mk4 d1 d2 d3 dp) dν) dj
  refine dd.mono ?_
  have w4 := wt_list4_le c1 c2 c3 (.nat p)
  have w5 := wt_list_snoc_le [c1, c2, c3, .nat p] (encFun ν)
  have w6 := wt_list_snoc_le [c1, c2, c3, .nat p, encFun ν] (.nat j)
  dsimp only [a, cur, orig] at *
  simp only [List.cons_append, List.nil_append] at *
  omega

end GI.Impl
