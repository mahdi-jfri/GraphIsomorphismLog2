module

public import Workspace.Lang.Lib.Search
public import Workspace.Lang.Lib.NatList

@[expose] public section

/-!
# Costs counted in units of a weight bound

Proving a cost bound for a function body adds up the costs of all its subexpressions. When every
value the body handles weighs at most `W`, each step costs at most `W + 1` plus the costs of the
calls it makes. `StDC P env e v n E W` says that `e` evaluates to `v` at cost at most
`n * (W + 1) + E`: `n` counts the steps and `E` sums the costs of the calls. The lemmas below
build `n` and `E` along the expression, so a body proof only supplies the weight facts, and
the cost bound is one inequality at the end.
-/

namespace GI.Impl

open GI.Lang
open GI.Cited (Val)
open GI.Machine (BinOp)

/-- `e` evaluates to `v` at cost at most `n (W + 1) + E`. -/
def StDC (P : Program) (env : List Val) (e : Expr) (v : Val) (n E W : ℕ) : Prop :=
  Det P env e v (n * (W + 1) + E)

namespace StDC

variable {P : Program} {env : List Val} {W : ℕ}

theorem det {e : Expr} {v : Val} {n E : ℕ} (h : StDC P env e v n E W) :
    Det P env e v (n * (W + 1) + E) := h

theorem mono {e : Expr} {v : Val} {n E n' E' : ℕ} (h : StDC P env e v n E W) (hn : n ≤ n')
    (hE : E ≤ E') : StDC P env e v n' E' W :=
  Det.mono h (Nat.add_le_add (Nat.mul_le_mul_right _ hn) hE)

theorem var' {i : ℕ} {v : Val} (h : env[i]? = some v) (hw : v.wt ≤ W) :
    StDC P env (.var i) v 1 0 W :=
  (Det.var' h).mono (by omega)

theorem nat (k : ℕ) (hk : k + 2 ≤ W) : StDC P env (.nat k) (.nat k) 1 0 W :=
  (Det.nat k).mono (by omega)

theorem arith {op : BinOp} {a b : Expr} {x y z na nb Ea Eb : ℕ}
    (ha : StDC P env a (.nat x) na Ea W) (hb : StDC P env b (.nat y) nb Eb W)
    (hz : op.eval x y = z) (hw : (Val.nat z).wt ≤ W) :
    StDC P env (.arith op a b) (.nat z) (na + nb + 1) (Ea + Eb) W := by
  subst hz
  refine (Det.arith ha hb).mono ?_
  have : (na + nb + 1) * (W + 1) = na * (W + 1) + nb * (W + 1) + (W + 1) := by ring
  omega

theorem arith' {op : BinOp} {a b : Expr} {x y z na nb Ea Eb : ℕ}
    (ha : StDC P env a (.nat x) na Ea W) (hb : StDC P env b (.nat y) nb Eb W)
    (hz : op.eval x y = z) (hw : z + 2 ≤ W) :
    StDC P env (.arith op a b) (.nat z) (na + nb + 1) (Ea + Eb) W :=
  arith ha hb hz ((wt_nat_le z).trans hw)

theorem get {l i : Expr} {vs : List Val} {x na nb Ea Eb : ℕ} {v : Val}
    (ha : StDC P env l (.list vs) na Ea W) (hb : StDC P env i (.nat x) nb Eb W)
    (hv : vs[x]? = some v) (hw : v.wt ≤ W) :
    StDC P env (.get l i) v (na + nb + 1) (Ea + Eb) W := by
  refine (Det.get' ha hb hv).mono ?_
  have : (na + nb + 1) * (W + 1) = na * (W + 1) + nb * (W + 1) + (W + 1) := by ring
  omega

theorem length {l : Expr} {vs : List Val} {na Ea : ℕ} (ha : StDC P env l (.list vs) na Ea W)
    (hl : vs.length + 2 ≤ W) : StDC P env (.length l) (.nat vs.length) (na + 1) Ea W := by
  refine (Det.length ha).mono ?_
  have : (na + 1) * (W + 1) = na * (W + 1) + (W + 1) := by ring
  omega

theorem nil (hW : 4 ≤ W) : StDC P env .nil (.list []) 1 0 W := Det.nil.mono (by omega)

theorem snoc {l e : Expr} {vs : List Val} {v : Val} {na nb Ea Eb : ℕ}
    (ha : StDC P env l (.list vs) na Ea W) (hb : StDC P env e v nb Eb W)
    (hw : (Val.list (vs ++ [v])).wt ≤ W) :
    StDC P env (.snoc l e) (.list (vs ++ [v])) (na + nb + 1) (Ea + Eb) W := by
  refine (Det.snoc ha hb).mono ?_
  have : (na + nb + 1) * (W + 1) = na * (W + 1) + nb * (W + 1) + (W + 1) := by ring
  omega

theorem mk2 {a b : Expr} {va vb : Val} {na nb Ea Eb : ℕ} (ha : StDC P env a va na Ea W)
    (hb : StDC P env b vb nb Eb W) (hw : (Val.list [va, vb]).wt ≤ W) (hW : 4 ≤ W) :
    StDC P env (GI.Lang.mk2 a b) (.list [va, vb]) (na + nb + 3) (Ea + Eb) W := by
  refine (Det.mk2 ha hb).mono ?_
  have : (na + nb + 3) * (W + 1) = na * (W + 1) + nb * (W + 1) + 3 * (W + 1) := by ring
  omega

theorem mk3 {a b c : Expr} {va vb vc : Val} {na nb nc Ea Eb Ec : ℕ}
    (ha : StDC P env a va na Ea W) (hb : StDC P env b vb nb Eb W) (hc : StDC P env c vc nc Ec W)
    (hw : (Val.list [va, vb, vc]).wt ≤ W) (hW : 4 ≤ W) :
    StDC P env (GI.Lang.mk3 a b c) (.list [va, vb, vc]) (na + nb + nc + 4) (Ea + Eb + Ec) W := by
  refine (Det.mk3 ha hb hc).mono ?_
  have : (na + nb + nc + 4) * (W + 1) =
    na * (W + 1) + nb * (W + 1) + nc * (W + 1) + 4 * (W + 1) := by ring
  omega

theorem mk4 {a b c d : Expr} {va vb vc vd : Val} {na nb nc nd Ea Eb Ec Ed : ℕ}
    (ha : StDC P env a va na Ea W) (hb : StDC P env b vb nb Eb W) (hc : StDC P env c vc nc Ec W)
    (hd : StDC P env d vd nd Ed W) (hw : (Val.list [va, vb, vc, vd]).wt ≤ W) (hW : 4 ≤ W) :
    StDC P env (GI.Lang.mk4 a b c d) (.list [va, vb, vc, vd]) (na + nb + nc + nd + 5)
      (Ea + Eb + Ec + Ed) W := by
  refine (Det.mk4 ha hb hc hd).mono ?_
  have : (na + nb + nc + nd + 5) * (W + 1) =
    na * (W + 1) + nb * (W + 1) + nc * (W + 1) + nd * (W + 1) + 5 * (W + 1) := by ring
  omega

theorem call {f : ℕ} {a : Expr} {v w : Val} {na Ea cb : ℕ} (ha : StDC P env a v na Ea W)
    (hf : FunDet P f v w cb) (hw : w.wt ≤ W) :
    StDC P env (.call f a) w (na + 1) (Ea + cb) W := by
  refine (Det.call ha hf).mono ?_
  have : (na + 1) * (W + 1) = na * (W + 1) + (W + 1) := by ring
  omega

theorem letE {e body : Expr} {v w : Val} {na nb Ea Eb : ℕ} (ha : StDC P env e v na Ea W)
    (hb : StDC P (env ++ [v]) body w nb Eb W) (hw : w.wt ≤ W) :
    StDC P env (.letE e body) w (na + nb + 1) (Ea + Eb) W := by
  refine (Det.letE ha hb).mono ?_
  have : (na + nb + 1) * (W + 1) = na * (W + 1) + nb * (W + 1) + (W + 1) := by ring
  omega

/-- `if` on a known number. -/
theorem ite {c t e : Expr} {x : ℕ} {v : Val} {nc nt ne Ec Et Ee : ℕ}
    (hc : StDC P env c (.nat x) nc Ec W) (ht : x ≠ 0 → StDC P env t v nt Et W)
    (he : x = 0 → StDC P env e v ne Ee W) (hw : v.wt ≤ W) :
    StDC P env (.ite c t e) v (nc + nt + ne + 1) (Ec + Et + Ee) W := by
  have e1 : (nc + nt + ne + 1) * (W + 1) =
    nc * (W + 1) + nt * (W + 1) + ne * (W + 1) + (W + 1) := by ring
  by_cases hx : x = 0
  · subst hx
    refine (Det.ite_zero hc (he rfl)).mono ?_
    omega
  · refine (Det.ite_pos hc hx (ht hx)).mono ?_
    omega

/-- Entry `j` of a list argument. -/
theorem arg {vs rest : List Val} {j : ℕ} {v : Val} (hv : vs[j]? = some v)
    (hW : (Val.list vs).wt ≤ W) (hj : j + 2 ≤ W) (hw : v.wt ≤ W) :
    StDC P (.list vs :: rest) (GI.Lang.arg j) v 3 0 W :=
  (get (var' (by simp) hW) (nat j hj) hv hw).mono (by omega) (by omega)

/-- A deterministic function from a body with counted cost. -/
theorem funDet {f : ℕ} {body : Expr} (hf : P.funs[f]? = some body) {v w : Val} {n E c : ℕ}
    (h : StDC P [v] body w n E W) (hc : n * (W + 1) + E ≤ c) : FunDet P f v w c :=
  FunDet.intro hf (Det.mono h hc)

end StDC

/-! ### Weights of short lists -/

theorem st_wt_list2 {a b : Val} {X : ℕ} (ha : a.wt ≤ X) (hb : b.wt ≤ X) :
    (Val.list [a, b]).wt ≤ 4 * X + 6 := by
  have := wt_list2_le a b; omega

theorem st_wt_list3 {a b c : Val} {X : ℕ} (ha : a.wt ≤ X) (hb : b.wt ≤ X) (hc : c.wt ≤ X) :
    (Val.list [a, b, c]).wt ≤ 6 * X + 7 := by
  have := wt_list3_le a b c; omega

theorem st_wt_list4 {a b c d : Val} {X : ℕ} (ha : a.wt ≤ X) (hb : b.wt ≤ X) (hc : c.wt ≤ X)
    (hd : d.wt ≤ X) : (Val.list [a, b, c, d]).wt ≤ 8 * X + 8 := by
  have := wt_list4_le a b c d; omega

theorem st_wt_mem {vs : List Val} {v : Val} (h : v ∈ vs) : v.wt ≤ (Val.list vs).wt :=
  (wt_le_wt_list h).le

theorem st_wt_nat {k X : ℕ} (h : k + 2 ≤ X) : (Val.nat k).wt ≤ X := (wt_nat_le k).trans h

end GI.Impl
