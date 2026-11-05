module

public import Workspace.Impl.LinMapSource
public import Workspace.Impl.LinPrimaryRecord
public import Workspace.Lang.Lib.Search

@[expose] public section

/-! Trial primality for the bounded characteristics. Its cost is polynomial
in the numeric candidate, which is at most the explicit permutation degree. -/
namespace GI.Impl
open GI.Cited GI.Lang
open GI.Machine (BinOp)

def linPrimeTestCellF : Expr :=
  .ite (.arith .lt (arg 1) (.nat 2)) (.nat 1)
    (.arith .lt (.nat 0) (.arith .mod (arg 0) (arg 1)))

def linPrimeTestPred (n : ℕ) : Val → Bool
  | .nat j => decide (j < 2 ∨ n % j ≠ 0)
  | _ => false

def linPrimeTestF (range all : ℕ) : Expr :=
  .letE (.call range (.var 0))
    (.ite (.arith .lt (.nat 1) (.var 0))
      (.call all (mk2 (.var 0) (.var 1))) (.nat 0))

def linPrimeTestFuns (b : ℕ) : List Expr :=
  [linPrimeTestF (b + 1) (b + 4)] ++ rangeFuns (b + 1) ++
    allFuns (b + 4) (b + 7) ++ [linPrimeTestCellF]

theorem linPrimeTestFuns_length (b : ℕ) : (linPrimeTestFuns b).length = 8 := rfl

structure linPrimeTestAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linPrimeTestF (b + 1) (b + 4))
  range : P.HasAt (b + 1) (rangeFuns (b + 1))
  all : P.HasAt (b + 4) (allFuns (b + 4) (b + 7))
  cell : P.funs[b + 7]? = some linPrimeTestCellF

theorem linPrimeTestAt_of {P : Program} {b : ℕ} (h : P.HasAt b (linPrimeTestFuns b)) :
    linPrimeTestAt P b where
  entry := (h.block (gs := [linPrimeTestF (b + 1) (b + 4)]) 0 rfl).single
  range := h.block 1 rfl
  all := h.block 4 rfl
  cell := (h.block (gs := [linPrimeTestCellF]) 7 rfl).single

set_option maxHeartbeats 1000000 in
theorem linPrimeTestCell_spec {P : Program} {f : ℕ}
    (hf : P.funs[f]? = some linPrimeTestCellF) (n j : ℕ) (hj : j < n) :
    FunDet P f (.list [.nat n, .nat j]) (boolVal (linPrimeTestPred n (.nat j)))
      (10000 * (n + 1)) := by
  have dn := Det.arg' (P := P) (vs := [.nat n, .nat j]) (rest := []) (j := 0) rfl
  have dj := Det.arg' (P := P) (vs := [.nat n, .nat j]) (rest := []) (j := 1) rfl
  have wenv := wt_list2_le (.nat n) (.nat j)
  have wn := wt_nat_le n
  have wj := wt_nat_le j
  have wm : (Val.nat (n % j)).wt ≤ (Val.nat n).wt := by
    simp only [wt_nat]
    exact Nat.add_le_add_right (GI.Machine.len_mono (Nat.mod_le _ _)) 2
  have wone : (Val.nat 1).wt = 3 := rfl
  have wzero : (Val.nat 0).wt = 2 := rfl
  apply FunDet.intro hf
  by_cases hsmall : j < 2
  · have dt := Det.arith' (op := .lt) dj (Det.nat 2) (z := 1) (by simp [BinOp.eval, hsmall])
    have dd := Det.ite_pos (e := .arith .lt (.nat 0) (.arith .mod (arg 0) (arg 1)))
      dt (by decide : 1 ≠ 0) (Det.nat 1)
    refine dd.post fun cost hc => ⟨by simp [linPrimeTestPred, hsmall, boolVal], by omega⟩
  · have dt := Det.arith' (op := .lt) dj (Det.nat 2) (z := 0) (by simp [BinOp.eval, hsmall])
    have dm := Det.arith (op := .mod) dn dj
    have dl := Det.arith (op := .lt) (Det.nat 0) dm
    refine (Det.ite_zero (t := .nat 1) dt dl).post fun cost hc => ⟨?_, ?_⟩
    · simp only [BinOp.eval_lt, BinOp.eval_mod, linPrimeTestPred, hsmall, false_or]
      by_cases hz : n % j = 0 <;> simp [boolVal, hz]
    · simp only [BinOp.eval_lt, BinOp.eval_mod] at hc
      have wb := linArithWt .lt 0 (n % j)
      simp only [BinOp.eval_lt] at wb
      omega

def linPrimeTestCost (n : ℕ) : ℕ := 100000000 * (n + 1) ^ 3

end GI.Impl
