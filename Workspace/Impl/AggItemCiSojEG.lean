module

public import Workspace.Impl.AggItemCiSojET

@[expose] public section

/-!
# Materializing one edge exchange

The test reads `[table, j, v, a, b]`. The result is the transposition `(a,b)`
when the edge is present, and the identity transposition `(a,a)` otherwise.
The existing transposition-table program builds the permutation on the old labels.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm)

variable {q : ℕ}

/-- On `[[table,j,v,a,b], range]`, one edge exchange as a permutation table. -/
def itcsEdgeGF (fe swt : ℕ) : Expr :=
  .letE (.call fe (arg 0))
    (.call swt (mk2 (mk2 (.get (arg 0) (.nat 3))
      (.ite (.var 1) (.get (arg 0) (.nat 4)) (.get (arg 0) (.nat 3)))) (arg 1)))

/-- Cost and correctness with a common bound on the built values. -/
theorem itcs_edge_gen {Pg : Program} {f fe swt : ℕ}
    (hf : Pg.funs[f]? = some (itcsEdgeGF fe swt))
    (he : Pg.funs[fe]? = some itcsEdgeT)
    (hs : ∀ u z : Fin q, FunDet Pg swt
      (.list [.list [.nat u, .nat z], natList (List.range q)])
      (encPerm (Equiv.swap u z)) (10 ^ 5 * (q + 1) ^ 3))
    (X : PairCfg q) (v : ℕ) (a b : Fin q) {W : ℕ}
    (hW : (Val.list [.list [rcColVal X, .nat X.j, .nat v, .nat a, .nat b],
      natList (List.range q)]).wt ≤ W)
    (hswap : ∀ z : Fin q, (Val.list [.list [.nat a, .nat z], natList (List.range q)]).wt ≤ W)
    (hout : ∀ z : Fin q, (encPerm (Equiv.swap a z)).wt ≤ W) (h8 : 8 ≤ W) :
    FunDet Pg f (.list [.list [rcColVal X, .nat X.j, .nat v, .nat a, .nat b],
      natList (List.range q)]) (encPerm (itcsEdge X v a b))
      (200 * (W + 1) + 10 ^ 5 * (q + 1) ^ 3) := by
  classical
  let dat : Val := .list [rcColVal X, .nat X.j, .nat v, .nat a, .nat b]
  let inp : Val := .list [dat, natList (List.range q)]
  have hd : dat.wt ≤ W := (st_wt_mem (by simp [dat])).trans hW
  have hr : (natList (List.range q)).wt ≤ W := (st_wt_mem (by simp)).trans hW
  have ha : (Val.nat a).wt ≤ W := (st_wt_mem (by simp : Val.nat a ∈
    [rcColVal X, .nat X.j, .nat v, .nat a, .nat b])).trans hd
  have hb : (Val.nat b).wt ≤ W := (st_wt_mem (by simp : Val.nat b ∈
    [rcColVal X, .nat X.j, .nat v, .nat a, .nat b])).trans hd
  let z : Fin q := if X.edge v a b then b else a
  have hz : (Val.nat z).wt ≤ W := by unfold z; split_ifs <;> assumption
  have hp : (Val.list [.nat a, .nat z]).wt ≤ W :=
    (st_wt_mem (by simp : Val.list [.nat a, .nat z] ∈
      [.list [.nat a, .nat z], natList (List.range q)])).trans (hswap z)
  have hd0 : StDC Pg [inp] (arg 0) dat 3 0 W :=
    StDC.arg rfl hW (by omega) hd
  have call0 := StDC.call (cb := 100 * (W + 1)) hd0
    (itcs_edgeT_spec he X v a b hd h8) ((wt_boolVal_le _).trans (by omega))
  let env : List Val := [inp, boolVal (decide (X.edge v a b))]
  have g0 : StDC Pg env (arg 0) dat 3 0 W := StDC.arg rfl hW (by omega) hd
  have gR : StDC Pg env (arg 1) (natList (List.range q)) 3 0 W :=
    StDC.arg rfl hW (by omega) hr
  have gA := StDC.get g0 (StDC.nat 3 (by omega)) (v := .nat a) rfl ha
  have gB := StDC.get g0 (StDC.nat 4 (by omega)) (v := .nat b) rfl hb
  have cond : StDC Pg env (.var 1) (boolVal (decide (X.edge v a b))) 1 0 W :=
    StDC.var' rfl ((wt_boolVal_le _).trans (by omega))
  have gz : StDC Pg env (.ite (.var 1) (.get (arg 0) (.nat 4)) (.get (arg 0) (.nat 3)))
      (.nat z) 12 0 W := by
    refine (StDC.ite (nt := 5) (ne := 5) (Et := 0) (Ee := 0) cond ?_ ?_ hz).mono
      (by omega) (by omega)
    · intro h
      have hh : X.edge v a b := by simpa [boolVal] using h
      simpa only [z, if_pos hh] using gB
    · intro h
      have hh : ¬ X.edge v a b := by simpa [boolVal] using h
      simpa only [z, if_neg hh] using gA
  have ga := StDC.mk2 (StDC.mk2 gA gz hp (by omega)) gR (hswap z) (by omega)
  have call1 := StDC.call ga (hs a z) (hout z)
  have body := StDC.letE call0 call1 (hout z)
  have houtEq : Equiv.swap a z = itcsEdge X v a b := by
    unfold z itcsEdge
    split_ifs <;> simp only [Equiv.swap_self] <;> rfl
  rw [houtEq] at body
  exact StDC.funDet hf body (by omega)

end GI.Impl
