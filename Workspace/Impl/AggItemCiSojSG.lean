module

public import Workspace.Impl.AggItemCiSojSq

@[expose] public section

/-!
# Constructing an edge exchange at a square index

The quotient and remainder select the two old labels. The wrapper builds the
edge-test argument and uses the already proved exchange program. All weight
hypotheses are explicit here so the bulk map can use one common bound.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm)

/-- Construct a list of five values. -/
def itcsMk5 (a b c d e : Expr) : Expr := .snoc (mk4 a b c d) e

/-- Counted cost of the five-value constructor. -/
theorem itcs_mk5 {Pg : Program} {env : List Val} {W : ℕ}
    {a b c d e : Expr} {va vb vc vd ve : Val} {na nb nc nd ne Ea Eb Ec Ed Ee : ℕ}
    (ha : StDC Pg env a va na Ea W) (hb : StDC Pg env b vb nb Eb W)
    (hc : StDC Pg env c vc nc Ec W) (hd : StDC Pg env d vd nd Ed W)
    (he : StDC Pg env e ve ne Ee W) (hw : (Val.list [va, vb, vc, vd, ve]).wt ≤ W)
    (h4 : 4 ≤ W) :
    StDC Pg env (itcsMk5 a b c d e) (.list [va, vb, vc, vd, ve])
      (na + nb + nc + nd + ne + 6) (Ea + Eb + Ec + Ed + Ee) W := by
  have hpre : (Val.list [va, vb, vc, vd]).wt ≤ W :=
    (wt_list_mono (by exact ⟨[ve], rfl⟩)).trans hw
  exact (StDC.snoc (StDC.mk4 ha hb hc hd hpre h4) he hw).mono (by omega) (by omega)

/-- On `[[table,j,v,q,range], t]`, the edge exchange at `(t/q,t%q)`. -/
def itcsSqGF (eg : ℕ) : Expr :=
  .letE (.arith .div (arg 1) (.get (arg 0) (.nat 3)))
    (.letE (.arith .mod (arg 1) (.get (arg 0) (.nat 3)))
      (.call eg (mk2 (itcsMk5 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))
        (.get (arg 0) (.nat 2)) (.var 1) (.var 2)) (.get (arg 0) (.nat 4)))))

variable {q : ℕ}

/-- The indexed exchange wrapper, within a common weight bound. -/
theorem itcs_sqG_spec {Pg : Program} {f eg : ℕ}
    (hf : Pg.funs[f]? = some (itcsSqGF eg)) (X : PairCfg q) (v : ℕ)
    (t : Fin (q * q)) {W Cg : ℕ}
    (hgen : ∀ a b : Fin q, FunDet Pg eg
      (.list [.list [rcColVal X, .nat X.j, .nat v, .nat a, .nat b], natList (List.range q)])
      (encPerm (itcsEdge X v a b)) Cg)
    (hW : (Val.list [.list [rcColVal X, .nat X.j, .nat v, .nat q, natList (List.range q)],
      .nat t]).wt ≤ W)
    (harg : ∀ a b : Fin q, (Val.list [.list [rcColVal X, .nat X.j, .nat v, .nat a, .nat b],
      natList (List.range q)]).wt ≤ W)
    (hout : ∀ a b : Fin q, (encPerm (itcsEdge X v a b)).wt ≤ W) (hq : q + 10 ≤ W) :
    FunDet Pg f (.list [.list [rcColVal X, .nat X.j, .nat v, .nat q, natList (List.range q)],
      .nat t]) (encPerm (itcsSqEdge X v t)) (100 * (W + 1) + Cg) := by
  let a : Fin q := ((itciPE q).symm t).1
  let b : Fin q := ((itciPE q).symm t).2
  let dat : Val := .list [rcColVal X, .nat X.j, .nat v, .nat q, natList (List.range q)]
  let inp : Val := .list [dat, .nat t]
  have hd : dat.wt ≤ W := (st_wt_mem (by simp [dat])).trans hW
  have ht : (Val.nat t).wt ≤ W := (st_wt_mem (by simp)).trans hW
  have hdval {i : ℕ} {w : Val} (hi : [rcColVal X, .nat X.j, .nat v, .nat q,
      natList (List.range q)][i]? = some w) : w.wt ≤ W :=
    (st_wt_mem (List.mem_of_getElem? hi)).trans hd
  have getD (rest : List Val) {i : ℕ} {w : Val}
      (hi : [rcColVal X, .nat X.j, .nat v, .nat q, natList (List.range q)][i]? = some w)
      (hiW : i + 2 ≤ W) : StDC Pg (inp :: rest) (.get (arg 0) (.nat i)) w 5 0 W :=
    StDC.get (StDC.arg rfl hW (by omega) hd) (StDC.nat i hiW) hi (hdval hi)
  have getT (rest : List Val) : StDC Pg (inp :: rest) (arg 1) (.nat t) 3 0 W :=
    StDC.arg rfl hW (by omega) ht
  have div := StDC.arith' (getT []) (getD [] (i := 3) rfl (by omega)) (op := .div)
    (z := (a : ℕ)) rfl (by have := a.isLt; omega)
  have md := StDC.arith' (getT [.nat a]) (getD [.nat a] (i := 3) rfl (by omega)) (op := .mod)
    (z := (b : ℕ)) rfl (by have := b.isLt; omega)
  let rest : List Val := [.nat a, .nat b]
  have av : StDC Pg (inp :: rest) (.var 1) (.nat a) 1 0 W :=
    StDC.var' rfl ((wt_nat_le _).trans (by have := a.isLt; omega))
  have bv : StDC Pg (inp :: rest) (.var 2) (.nat b) 1 0 W :=
    StDC.var' rfl ((wt_nat_le _).trans (by have := b.isLt; omega))
  have hdata : (Val.list [rcColVal X, .nat X.j, .nat v, .nat a, .nat b]).wt ≤ W :=
    (st_wt_mem (List.mem_cons_self ..)).trans (harg a b)
  have arg5 := itcs_mk5 (getD rest (i := 0) rfl (by omega))
    (getD rest (i := 1) rfl (by omega)) (getD rest (i := 2) rfl (by omega)) av bv hdata (by omega)
  have args := StDC.mk2 arg5 (getD rest (i := 4) rfl (by omega)) (harg a b) (by omega)
  have call := StDC.call args (hgen a b) (hout a b)
  have body := StDC.letE div (StDC.letE md call (hout a b)) (hout a b)
  exact StDC.funDet hf body (by omega)

end GI.Impl
