module

public import Workspace.Impl.LinChain
public import Workspace.Lang.Prims.PermGroups

@[expose] public section

/-! The successive cyclic orders in A.20, computed from permutation-group values.
The two group-order calls return binary natural values. The cost bound uses their
bit weights, so it remains polynomial even when the group order is exponential. -/
namespace GI.Impl
open GI.Cited GI.Lang
open GI.Machine (len_div_le)

/-- On [U_i,U_{i+1}], return |U_{i+1}| / |U_i|. -/
def linOrderRatioF (j : ℕ) : Expr :=
  .letE (.prim j (arg 0))
    (.letE (.prim j (arg 1)) (.arith .div (.var 2) (.var 1)))

noncomputable def linOrderRatioCost (h : GroupOrder) (n : ℕ) (gv hv : Val) : ℕ :=
  (groupOrderPrim h).bound gv + (groupOrderPrim h).bound hv +
    4 * (Val.list [gv, hv]).wt + 10 * (n ^ 2 + 4) + 20

/-- Two calls of GroupOrder and one division compute the index of nested groups. -/
theorem linOrderRatio_spec (h : GroupOrder) {P : Program} {f j n : ℕ}
    (hf : P.funs[f]? = some (linOrderRatioF j))
    (hj : P.prims[j]? = some (groupOrderPrim h))
    {gv hv : Val} {H K : Subgroup (Equiv.Perm (Fin n))}
    (hH : GroupVal n gv H) (hK : GroupVal n hv K) (hHK : H ≤ K) :
    FunDet P f (.list [gv, hv]) (.nat (H.relIndex K)) (linOrderRatioCost h n gv hv) := by
  have dH := groupOrder_call h hj (Det.arg' (P := P) (rest := [])
    (vs := [gv, hv]) (j := 0) rfl) hH
  have dK := groupOrder_call h hj (Det.arg' (P := P) (rest := [.nat (Nat.card H)])
    (vs := [gv, hv]) (j := 1) rfl) hK
  have d1 := Det.var' (P := P)
    (env := [.list [gv, hv], .nat (Nat.card H), .nat (Nat.card K)]) (i := 1) rfl
  have d2 := Det.var' (P := P)
    (env := [.list [gv, hv], .nat (Nat.card H), .nat (Nat.card K)]) (i := 2) rfl
  have dd := Det.arith (op := .div) d2 d1
  have hq : (Val.nat (Nat.card K / Nat.card H)).wt ≤ n ^ 2 + 3 := by
    have := wt_card_le K
    have := len_div_le (Nat.card K) (Nat.card H)
    simp only [wt_nat] at *
    omega
  have wh := wt_card_le H
  have wk := wt_card_le K
  have df := Det.letE dH (Det.letE dK dd)
  have hr := linChain_orderRatio H K hHK
  rw [hr]
  apply FunDet.intro hf
  refine df.mono ?_
  unfold linOrderRatioCost
  simp only [GI.Machine.BinOp.eval_div]
  omega

end GI.Impl
