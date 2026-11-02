import Workspace.Impl.LinWreathMatrix
import Workspace.Impl.LinMapEncoded

namespace GI.Impl
open GI.Cited GI.Lang Equiv

/-- Mode zero acts on the first copy, mode one on the second, and mode two
exchanges the copies. -/
def linWreathBlock {R : Type*} [Zero R] [One R] {d : ℕ} (hd : 0 < d)
    (A : Matrix (Fin d) (Fin d) R) (mode : ℕ)
    (i j : Fin (d + d)) : R :=
  let x : Fin d := ⟨i.val % d, Nat.mod_lt _ hd⟩
  let y : Fin d := ⟨j.val % d, Nat.mod_lt _ hd⟩
  let same := (i.val < d) = (j.val < d)
  let active := (i.val < d) = (mode = 0)
  if mode < 2 then
    if same then if active then A x y else if x = y then 1 else 0 else 0
  else if same then 0 else if x = y then 1 else 0

/-- The cell routine reads `[ [A,mode,row], column ]`. -/
def linWreathBlockCellF : Expr :=
  let a := .get (arg 0) (.nat 0)
  let mode := .get (arg 0) (.nat 1)
  let i := .get (arg 0) (.nat 2)
  let j := arg 1
  let d := .length a
  let x := .arith .mod i d
  let y := .arith .mod j d
  let same := .arith .eq (.arith .lt i d) (.arith .lt j d)
  let active := .arith .eq (.arith .lt i d) (.arith .eq mode (.nat 0))
  let unit := .arith .eq x y
  .ite (.arith .lt mode (.nat 2))
    (.ite same (.ite active (.get (.get a x) y) unit) (.nat 0))
    (.ite same (.nat 0) unit)

private theorem linWreathBlock_indicator_zero (P : Prop) [Decidable P] :
    ((if P then 1 else 0 : ℕ) = 0) ↔ ¬P := by split_ifs <;> simp_all

private theorem linWreathBlock_indicator_eq (P Q : Prop) [Decidable P] [Decidable Q] :
    ((if P then 1 else 0 : ℕ) = (if Q then 1 else 0)) ↔ P = Q := by
  by_cases P <;> by_cases Q <;> simp_all

theorem linWreathBlock_formula {p d : ℕ} (hp : p.Prime) (hd : 0 < d)
    (A : Matrix (Fin d) (Fin d) (ZMod p)) (mode : Fin 3) (i j : Fin (d + d)) :
    let same := GI.Machine.BinOp.eq.eval (GI.Machine.BinOp.lt.eval i.val d)
      (GI.Machine.BinOp.lt.eval j.val d)
    let active := GI.Machine.BinOp.eq.eval (GI.Machine.BinOp.lt.eval i.val d)
      (GI.Machine.BinOp.eq.eval mode.val 0)
    let unit := Val.nat (GI.Machine.BinOp.eq.eval (i.val % d) (j.val % d))
    let cell := Val.nat (A ⟨i.val % d, Nat.mod_lt _ hd⟩ ⟨j.val % d, Nat.mod_lt _ hd⟩).val
    (if GI.Machine.BinOp.lt.eval mode.val 2 = 0 then
      (if same = 0 then unit else Val.nat 0) else
      (if same = 0 then Val.nat 0 else if active = 0 then unit else cell)) =
      Val.nat (linWreathBlock hd A mode i j).val := by
  dsimp only
  simp only [GI.Machine.BinOp.eval,
    linWreathBlock_indicator_zero (mode.val < 2),
    linWreathBlock_indicator_zero
      ((if i.val < d then 1 else 0 : ℕ) = (if j.val < d then 1 else 0)),
    linWreathBlock_indicator_zero
      ((if i.val < d then 1 else 0 : ℕ) = (if mode.val = 0 then 1 else 0)),
    linWreathBlock_indicator_eq (i.val < d) (j.val < d),
    linWreathBlock_indicator_eq (i.val < d) (mode.val = 0),
    ite_not, linWreathBlock, Fin.ext_iff,
    ZMod.val_zero, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hp.one_lt]
  split_ifs <;> simp_all only [not_true_eq_false, not_false_eq_true, Fin.ext_iff, ZMod.val_zero,
    ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hp.one_lt, if_pos, if_neg]

end GI.Impl
