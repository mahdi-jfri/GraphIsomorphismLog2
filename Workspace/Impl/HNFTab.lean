import Workspace.Impl.LinTabulate

/-!
# Tables of a matrix, as a program

On `[c, r, n]`, the program `hnfTab` returns the `r × n` table whose entry `(i, j)` is computed
by a cell function on `[[[c, r, n], i], j]`. It is two nested uses of `linTabulate`. The cost is
a function of one number `X` that bounds the weight of `[c, r, n]`, `r` and `n`.
-/

namespace GI.Impl

open GI.Cited GI.Lang

def hnfTabF (tab : ℕ) : Expr := .call tab (mk2 (.var 0) (.get (.var 0) (.nat 1)))
def hnfTabRowF (tab : ℕ) : Expr := .call tab (mk2 (.var 0) (.get (arg 0) (.nat 2)))

def hnfTabFuns (b cell : ℕ) : List Expr :=
  [hnfTabF (b + 1)] ++ linTabulateFuns (b + 1) (b + 8) ++ [hnfTabRowF (b + 9)] ++
    linTabulateFuns (b + 9) cell

theorem hnfTabFuns_length (b cell : ℕ) : (hnfTabFuns b cell).length = 16 := rfl

structure hnfTabAt (P : Program) (b cell : ℕ) : Prop where
  entry : P.funs[b]? = some (hnfTabF (b + 1))
  rows : linTabulateAt P (b + 1) (b + 8)
  row : P.funs[b + 8]? = some (hnfTabRowF (b + 9))
  cols : linTabulateAt P (b + 9) cell

theorem hnfTabAt_of {P : Program} {b cell : ℕ} (h : P.HasAt b (hnfTabFuns b cell)) :
    hnfTabAt P b cell where
  entry := (h.block (gs := [hnfTabF (b + 1)]) 0 rfl).single
  rows := linTabulateAt_of (h.block 1 rfl)
  row := (h.block (gs := [hnfTabRowF (b + 9)]) 8 rfl).single
  cols := linTabulateAt_of (h.block 9 rfl)

def hnfTabRowCost (X B : ℕ) : ℕ := 2 * linTabulateCost (12 * X + 60) X B + 100 * (X + 1)
def hnfTabCost (X B : ℕ) : ℕ := 2 * linTabulateCost (4 * X + 20) X (hnfTabRowCost X B) + 100 * (X + 1)

theorem hnfTabCost_mono {X Y B C : ℕ} (hX : X ≤ Y) (hB : B ≤ C) : hnfTabCost X B ≤ hnfTabCost Y C := by
  unfold hnfTabCost hnfTabRowCost
  have h1 := linTabulateCost_mono (show 12 * X + 60 ≤ 12 * Y + 60 by omega) hX hB
  have h2 := linTabulateCost_mono (show 4 * X + 20 ≤ 4 * Y + 20 by omega) hX
    (show 2 * linTabulateCost (12 * X + 60) X B + 100 * (X + 1) ≤
      2 * linTabulateCost (12 * Y + 60) Y C + 100 * (Y + 1) by omega)
  omega

set_option maxHeartbeats 1000000 in
/-- **A table.** -/
theorem hnfTab_spec {P : Program} {b cell : ℕ} (h : hnfTabAt P b cell) (c : Val) (r n : ℕ)
    (F : Fin r → Fin n → Val) (B X : ℕ) (hX : (Val.list [c, .nat r, .nat n]).wt ≤ X)
    (hrX : r ≤ X) (hnX : n ≤ X)
    (hf : ∀ (i : Fin r) (j : Fin n), FunDet P cell (.list [.list [.list [c, .nat r, .nat n], .nat i], .nat j]) (F i j) B) :
    FunDet P b (.list [c, .nat r, .nat n])
      (.list ((List.finRange r).map fun i => .list ((List.finRange n).map (F i)))) (hnfTabCost X B) := by
  set a := Val.list [c, .nat r, .nat n] with ha
  have wr : (Val.nat r).wt < a.wt := wt_le_wt_list (by simp [ha])
  have wn : (Val.nat n).wt < a.wt := wt_le_wt_list (by simp [ha])
  have hr := wt_nat_le r
  have hn := wt_nat_le n
  have hrow : ∀ i : Fin r, FunDet P (b + 8) (.list [a, .nat i])
      (.list ((List.finRange n).map (F i))) (hnfTabRowCost X B) := by
    intro i
    have ht := linTabulate_spec h.cols (.list [a, .nat i]) (F i) B (hf i)
    have dv := Det.var' (P := P) (env := [Val.list [a, .nat i]]) (i := 0) rfl
    have dn := Det.get' (Det.arg' (P := P) (vs := [a, .nat i]) (rest := []) (j := 0) rfl)
      (Det.nat 2) (show [c, .nat r, .nat n][2]? = some (.nat n) from rfl)
    have dout := Det.call (Det.mk2 dv dn) ht
    apply FunDet.intro h.row
    refine dout.mono ?_
    have wo := ht.wt_lt
    have w1 := wt_list2_le a (.nat i)
    have w2 := wt_list2_le (.list [a, .nat i]) (.nat n)
    have wi := wt_nat_le (i : ℕ)
    have hi := i.isLt
    have hm := linTabulateCost_mono (show (Val.list [.list [a, .nat i], .nat n]).wt ≤ 12 * X + 60 by
      omega) (show n ≤ X by omega) (le_refl B)
    have e2 : (Val.nat 2).wt = 4 := rfl
    unfold hnfTabRowCost
    omega
  have ht := linTabulate_spec h.rows a (fun i => .list ((List.finRange n).map (F i)))
    (hnfTabRowCost X B) hrow
  have dv := Det.var' (P := P) (env := [a]) (i := 0) rfl
  have dr := Det.get' dv (Det.nat 1) (show [c, .nat r, .nat n][1]? = some (.nat r) from rfl)
  have dout := Det.call (Det.mk2 dv dr) ht
  apply FunDet.intro h.entry
  refine dout.mono ?_
  have wo := ht.wt_lt
  have w1 := wt_list2_le a (.nat r)
  have hm := linTabulateCost_mono (show (Val.list [a, .nat r]).wt ≤ 4 * X + 20 by omega)
    (show r ≤ X by omega) (le_refl (hnfTabRowCost X B))
  have e1 : (Val.nat 1).wt = 3 := rfl
  unfold hnfTabCost
  omega

end GI.Impl
