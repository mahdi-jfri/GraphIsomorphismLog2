import Workspace.Impl.AggItemCiSojQuery
import Workspace.Impl.AggItemCiCfgS

/-!
# Reading matrix bits through the representation's cell codes

A nonzero cell code stores the actual left and right labels. Source colors read
those labels in the source table. Target colors first apply the alignment and the
parity twist, then read the target table. No new positions are created.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val encPerm)

variable {q : ℕ} {W R : Finset (Fin q)}

/-- Recovering the left label from a nonzero cell code. -/
theorem itcs_cell_row (w : W) (r : R) :
    (rcCellCode (some (w, r)) - 1) / q = (w.val : ℕ) := by
  have hq : 0 < q := Nat.zero_lt_of_lt r.val.isLt
  have he : rcCellCode (some (w, r)) - 1 = (w.val : ℕ) * q + (r.val : ℕ) := by
    simp only [rcCellCode]; omega
  rw [he, Nat.mul_comm (w.val : ℕ) q, Nat.mul_add_div hq,
    Nat.div_eq_of_lt r.val.isLt, Nat.add_zero]

/-- Recovering the right label from a nonzero cell code. -/
theorem itcs_cell_col (w : W) (r : R) :
    (rcCellCode (some (w, r)) - 1) % q = (r.val : ℕ) := by
  have he : rcCellCode (some (w, r)) - 1 = (w.val : ℕ) * q + (r.val : ℕ) := by
    simp only [rcCellCode]; omega
  rw [he, Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt r.val.isLt]

/-- The three color codes are zero off cells and one plus the matrix bit on cells. -/
theorem itcs_qcode_bit (b : Bool) : itcsQCode (some b) = 1 + b.toNat := by
  cases b <;> rfl

/-- On `[table, edge color, q, cell code, p]`, the bit pulled back through `p`. -/
def itcsPullF : Expr :=
  .ite (.arith .eq (arg 3) (.nat 0)) (.nat 0)
    (.arith .add (.nat 1) (.arith .eq
      (.get (.get (arg 0) (.get (arg 4) (.arith .div (.arith .sub (arg 3) (.nat 1)) (arg 2))))
        (.get (arg 4) (.arith .mod (.arith .sub (arg 3) (.nat 1)) (arg 2)))) (arg 1)))

/-- One pulled-back bit, from the original pair table and an actual label permutation. -/
theorem itcs_pull_spec {Pg : Program} {f : ℕ} (hf : Pg.funs[f]? = some itcsPullF)
    (X : PairCfg q) (v : ℕ) (p : Perm (Fin q)) (cell : Option (W × R)) {Bw : ℕ}
    (hW : (Val.list [rcColVal X, .nat v, .nat q, .nat (rcCellCode cell), encPerm p]).wt ≤ Bw)
    (hq : q * q + q + 10 ≤ Bw) :
    FunDet Pg f (.list [rcColVal X, .nat v, .nat q, .nat (rcCellCode cell), encPerm p])
      (.nat (itcsQCode (cell.map fun c => decide (X.col (p c.1.val) (p c.2.val) = v))))
      (150 * (Bw + 1)) := by
  classical
  let vs : List Val := [rcColVal X, .nat v, .nat q, .nat (rcCellCode cell), encPerm p]
  let env : List Val := [.list vs]
  have sub {i : ℕ} {w : Val} (hi : vs[i]? = some w) : w.wt ≤ Bw :=
    (st_wt_mem (List.mem_of_getElem? hi)).trans hW
  have g0 : StDC Pg env (arg 0) (rcColVal X) 3 0 Bw :=
    StDC.arg rfl hW (by omega) (sub (i := 0) rfl)
  have g1 : StDC Pg env (arg 1) (.nat v) 3 0 Bw :=
    StDC.arg rfl hW (by omega) (sub (i := 1) rfl)
  have g2 : StDC Pg env (arg 2) (.nat q) 3 0 Bw :=
    StDC.arg rfl hW (by omega) (sub (i := 2) rfl)
  have g3 : StDC Pg env (arg 3) (.nat (rcCellCode cell)) 3 0 Bw :=
    StDC.arg rfl hW (by omega) (sub (i := 3) rfl)
  have g4 : StDC Pg env (arg 4) (encPerm p) 3 0 Bw :=
    StDC.arg rfl hW (by omega) (sub (i := 4) rfl)
  have gc := StDC.arith' g3 (StDC.nat 0 (by omega)) (op := .eq)
    (z := if rcCellCode cell = 0 then 1 else 0) (by simp [Machine.BinOp.eval_eq])
    (by split_ifs <;> omega)
  have hbody : StDC Pg env itcsPullF
      (.nat (itcsQCode (cell.map fun c => decide (X.col (p c.1.val) (p c.2.val) = v))))
      140 0 Bw := by
    cases cell with
    | none =>
      simp only [rcCellCode] at gc
      norm_num at gc
      refine (StDC.ite (nt := 1) (ne := 1) (Et := 0) (Ee := 0) gc
        (fun _ => StDC.nat 0 (by omega)) (fun h => by omega)
        ((wt_nat_le 0).trans (by omega))).mono
        (by omega) (by omega)
    | some c =>
      obtain ⟨w, r⟩ := c
      have hne : rcCellCode (some (w, r)) ≠ 0 := by simp [rcCellCode]
      simp only [if_neg hne] at gc
      have hraw : rcCellCode (some (w, r)) - 1 ≤ q * q := by
        change 1 + (w.val : ℕ) * q + (r.val : ℕ) - 1 ≤ q * q
        have hmul := Nat.mul_le_mul_right q (Nat.succ_le_of_lt w.val.isLt)
        have hr := r.val.isLt
        simp only [Nat.succ_mul] at hmul
        omega
      have gs := StDC.arith' g3 (StDC.nat 1 (by omega)) (op := .sub)
        (z := rcCellCode (some (w, r)) - 1) rfl (by omega)
      have gd := StDC.arith' gs g2 (op := .div) (z := (w.val : ℕ))
        (itcs_cell_row w r) (by have := w.val.isLt; omega)
      have gm := StDC.arith' gs g2 (op := .mod) (z := (r.val : ℕ))
        (itcs_cell_col w r) (by have := r.val.isLt; omega)
      have gw := StDC.get (v := .nat (p w.val)) g4 gd (encFun_getElem? (fun x => (p x : ℕ)) w.val)
        ((wt_nat_le _).trans (by have := (p w.val).isLt; omega))
      have gr := StDC.get (v := .nat (p r.val)) g4 gm (encFun_getElem? (fun x => (p x : ℕ)) r.val)
        ((wt_nat_le _).trans (by have := (p r.val).isLt; omega))
      have hrw : (encFun (X.col (p w.val))).wt ≤ Bw :=
        (st_wt_mem (List.mem_of_getElem? (itcq_col_get X (p w.val)))).trans (sub (i := 0) rfl)
      have hval : (Val.nat (X.col (p w.val) (p r.val))).wt ≤ Bw :=
        (st_wt_mem (List.mem_of_getElem? (encFun_getElem? (X.col (p w.val)) (p r.val)))).trans hrw
      have row := StDC.get g0 gw (itcq_col_get X (p w.val)) hrw
      have value := StDC.get row gr (encFun_getElem? (X.col (p w.val)) (p r.val)) hval
      have eqt := StDC.arith' value g1 (op := .eq)
        (z := (decide (X.col (p w.val) (p r.val) = v)).toNat)
        (by simp [Machine.BinOp.eval_eq]; split_ifs <;> simp_all)
        (by cases decide (X.col (p w.val) (p r.val) = v) <;> simp <;> omega)
      have add := StDC.arith' (StDC.nat 1 (by omega)) eqt (op := .add)
        (z := 1 + (decide (X.col (p w.val) (p r.val) = v)).toNat) rfl
        (by cases decide (X.col (p w.val) (p r.val) = v) <;> simp <;> omega)
      rw [← itcs_qcode_bit] at add
      refine (StDC.ite (nt := 1) (ne := 120) (Et := 0) (Ee := 0) gc
        (fun h => by omega) (fun _ => add.mono (by omega) le_rfl)
        ((wt_nat_le _).trans (by have := itcs_qcode_le (some (decide (X.col (p w.val) (p r.val) = v))); omega))).mono
        (by omega) (by omega)
  exact StDC.funDet hf hbody (by omega)

end GI.Impl
