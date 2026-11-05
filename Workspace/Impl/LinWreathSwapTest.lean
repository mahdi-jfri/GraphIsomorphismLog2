module

public import Workspace.Impl.LinWreathStab

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang Equiv

def linWreathSwapTestF : Expr :=
  .arith .eq (.arith .lt (.get (arg 1) (.nat 0)) (arg 0)) (.nat 0)

theorem linWreathSwapTest_spec {P : Program} {f n : ℕ}
    (hf : P.funs[f]? = some linWreathSwapTestF) (hn : 0 < n)
    (σ : Perm (Fin (n + n))) :
    FunDet P f (.list [.nat n, encPerm σ])
      (boolVal (decide (n ≤ (σ ⟨0, by omega⟩ : ℕ))))
      (1000 * ((Val.list [.nat n, encPerm σ]).wt + 1)) := by
  let a := Val.list [.nat n, encPerm σ]
  let z : Fin (n + n) := ⟨0, by omega⟩
  have dn := Det.arg' (P := P) (vs := [.nat n, encPerm σ]) (rest := []) (j := 0) rfl
  have ds := Det.arg' (P := P) (vs := [.nat n, encPerm σ]) (rest := []) (j := 1) rfl
  have dz := Det.get' ds (Det.nat 0) (v := .nat (σ z)) (by
    simp only [encPerm, List.getElem?_map]
    rw [List.getElem?_eq_getElem (by simp; omega)]
    simp [List.getElem_finRange, z])
  have dl := Det.arith (op := .lt) dz dn
  have de := Det.arith (op := .eq) dl (Det.nat 0)
  have wn : (Val.nat n).wt < a.wt := wt_le_wt_list (by simp [a])
  have ws : (encPerm σ).wt < a.wt := wt_le_wt_list (by simp [a])
  have wz : (Val.nat (σ z)).wt < (encPerm σ).wt :=
    wt_le_wt_list (by simp [encPerm])
  have wl : (Val.nat (GI.Machine.BinOp.lt.eval (σ z) n)).wt ≤ 3 := by
    simp only [GI.Machine.BinOp.eval]; split_ifs <;> decide
  have we : (Val.nat (GI.Machine.BinOp.eq.eval (GI.Machine.BinOp.lt.eval (σ z) n) 0)).wt ≤ 3 := by
    simp only [GI.Machine.BinOp.eval]; split_ifs <;> decide
  apply FunAll.intro hf
  refine de.post fun cost hc => ⟨?_, ?_⟩
  · by_cases h : n ≤ (σ z : ℕ) <;> simp [GI.Machine.BinOp.eval, boolVal, h, Nat.not_lt_of_ge, Nat.lt_of_not_ge, z]
  · change cost ≤ 1000 * (a.wt + 1)
    have w0 : (Val.nat 0).wt = 2 := rfl
    dsimp only [a] at *
    omega

end GI.Impl
