/-
Expressions: notation, evaluation lemmas, and cost bounds.

* Notation. `Expr` gets `+ - * / %` and numerals, so `.reg 1 + 2` is an expression. The
  `simp` lemmas `Expr.add_eq` and so on rewrite these back to `.bin` and `.const`, and the
  `simp` lemmas `evalExpr_const` and so on then compute both the value and the cost. So
  `simp` evaluates any concrete expression in a symbolic state.
* Cost bounds. If every value met while evaluating `e` is at most `M` (`Expr.ValsLe`), the
  cost is at most `e.size * (2 * len M + 1)` (`Expr.cost_le`). `Expr.ValsLe` unfolds by `simp`
  into one inequality per subexpression.
* The `simp` set `machine_simps` holds all these lemmas and `Function.update_apply`. Use
  `Function.update_apply` rather than rewriting inside `Function.update f a v`: the value `v`
  depends on `a` in the type of `Function.update`, so `simp` cannot rewrite `a` there.
-/
module

public import Workspace.Machine.Run
public import Workspace.Machine.Attr

@[expose] public section

namespace GI.Machine

/-! ### Notation -/

instance : Add Expr := ⟨.bin .add⟩
instance : Sub Expr := ⟨.bin .sub⟩
instance : Mul Expr := ⟨.bin .mul⟩
instance : Div Expr := ⟨.bin .div⟩
instance : Mod Expr := ⟨.bin .mod⟩
instance {k : ℕ} : OfNat Expr k := ⟨.const k⟩

/-- `Expr.lt a b` is 1 if `a < b` and 0 otherwise. -/
abbrev Expr.lt (a b : Expr) : Expr := .bin .lt a b
/-- `Expr.eq a b` is 1 if `a = b` and 0 otherwise. -/
abbrev Expr.eq (a b : Expr) : Expr := .bin .eq a b

namespace Expr

@[simp, machine_simps] theorem add_eq (a b : Expr) : a + b = .bin .add a b := rfl
@[simp, machine_simps] theorem sub_eq (a b : Expr) : a - b = .bin .sub a b := rfl
@[simp, machine_simps] theorem mul_eq (a b : Expr) : a * b = .bin .mul a b := rfl
@[simp, machine_simps] theorem div_eq (a b : Expr) : a / b = .bin .div a b := rfl
@[simp, machine_simps] theorem mod_eq (a b : Expr) : a % b = .bin .mod a b := rfl
@[simp, machine_simps] theorem ofNat_eq (k : ℕ) : (OfNat.ofNat k : Expr) = .const k := rfl

end Expr

/-! ### Evaluation -/

@[simp, machine_simps] theorem BinOp.eval_add (a b : ℕ) : BinOp.add.eval a b = a + b := rfl
@[simp, machine_simps] theorem BinOp.eval_sub (a b : ℕ) : BinOp.sub.eval a b = a - b := rfl
@[simp, machine_simps] theorem BinOp.eval_mul (a b : ℕ) : BinOp.mul.eval a b = a * b := rfl
@[simp, machine_simps] theorem BinOp.eval_div (a b : ℕ) : BinOp.div.eval a b = a / b := rfl
@[simp, machine_simps] theorem BinOp.eval_mod (a b : ℕ) : BinOp.mod.eval a b = a % b := rfl
@[simp, machine_simps] theorem BinOp.eval_lt (a b : ℕ) : BinOp.lt.eval a b = if a < b then 1 else 0 := rfl
@[simp, machine_simps] theorem BinOp.eval_eq (a b : ℕ) : BinOp.eq.eval a b = if a = b then 1 else 0 := rfl

@[simp, machine_simps] theorem evalExpr_const (st : State) (k : ℕ) : evalExpr st (.const k) = (k, 1 + len k) :=
  rfl

@[simp, machine_simps] theorem evalExpr_reg (st : State) (r : ℕ) :
    evalExpr st (.reg r) = (st.regs r, 1 + len (st.regs r)) := rfl

@[simp, machine_simps] theorem evalExpr_load (st : State) (a : Expr) :
    evalExpr st (.load a) = (st.mem (evalExpr st a).1,
      (evalExpr st a).2 + 1 + len (evalExpr st a).1 + len (st.mem (evalExpr st a).1)) := rfl

@[simp, machine_simps] theorem evalExpr_bin (st : State) (op : BinOp) (a b : Expr) :
    evalExpr st (.bin op a b) = (op.eval (evalExpr st a).1 (evalExpr st b).1,
      (evalExpr st a).2 + (evalExpr st b).2 + 1 + len (evalExpr st a).1 +
        len (evalExpr st b).1) := rfl

@[simp, machine_simps] theorem evalArgs_nil (st : State) : evalArgs st [] = ([], 0) := rfl

@[simp, machine_simps] theorem evalArgs_cons (st : State) (e : Expr) (es : List Expr) :
    evalArgs st (e :: es) = ((evalExpr st e).1 :: (evalArgs st es).1,
      (evalExpr st e).2 + (evalArgs st es).2) := rfl

/-- The values of the arguments are the values of the expressions. -/
theorem evalArgs_fst (st : State) (es : List Expr) :
    (evalArgs st es).1 = es.map (fun e => (evalExpr st e).1) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [ih]

/-- An expression depends only on the registers and the memory. -/
theorem evalExpr_congr {st st' : State} (hm : st.mem = st'.mem) (hr : st.regs = st'.regs)
    (e : Expr) : evalExpr st e = evalExpr st' e := by
  rw [State.ext' hm hr]

/-! ### Cost bounds -/

/-- The number of nodes of an expression. -/
def Expr.size : Expr → ℕ
  | .const _ => 1
  | .reg _ => 1
  | .load a => a.size + 1
  | .bin _ a b => a.size + b.size + 1

@[simp, machine_simps] theorem Expr.size_const (k : ℕ) : (Expr.const k).size = 1 := rfl
@[simp, machine_simps] theorem Expr.size_reg (r : ℕ) : (Expr.reg r).size = 1 := rfl
@[simp, machine_simps] theorem Expr.size_load (a : Expr) : (Expr.load a).size = a.size + 1 := rfl
@[simp, machine_simps] theorem Expr.size_bin (op : BinOp) (a b : Expr) :
    (Expr.bin op a b).size = a.size + b.size + 1 := rfl

/-- Every number whose length the evaluation of `e` pays for is at most `M`: constants,
register values, addresses, values read from memory, and operands. -/
def Expr.ValsLe (st : State) (M : ℕ) : Expr → Prop
  | .const k => k ≤ M
  | .reg r => st.regs r ≤ M
  | .load a => a.ValsLe st M ∧ (evalExpr st a).1 ≤ M ∧ st.mem (evalExpr st a).1 ≤ M
  | .bin _ a b => a.ValsLe st M ∧ b.ValsLe st M ∧ (evalExpr st a).1 ≤ M ∧ (evalExpr st b).1 ≤ M

@[simp, machine_simps] theorem Expr.valsLe_const (st : State) (M k : ℕ) : (Expr.const k).ValsLe st M ↔ k ≤ M :=
  Iff.rfl
@[simp, machine_simps] theorem Expr.valsLe_reg (st : State) (M r : ℕ) :
    (Expr.reg r).ValsLe st M ↔ st.regs r ≤ M := Iff.rfl
@[simp, machine_simps] theorem Expr.valsLe_load (st : State) (M : ℕ) (a : Expr) :
    (Expr.load a).ValsLe st M ↔
      a.ValsLe st M ∧ (evalExpr st a).1 ≤ M ∧ st.mem (evalExpr st a).1 ≤ M := Iff.rfl
@[simp, machine_simps] theorem Expr.valsLe_bin (st : State) (M : ℕ) (op : BinOp) (a b : Expr) :
    (Expr.bin op a b).ValsLe st M ↔
      a.ValsLe st M ∧ b.ValsLe st M ∧ (evalExpr st a).1 ≤ M ∧ (evalExpr st b).1 ≤ M := Iff.rfl

theorem Expr.ValsLe.mono {st : State} {M M' : ℕ} {e : Expr} (h : e.ValsLe st M) (hM : M ≤ M') :
    e.ValsLe st M' := by
  induction e with
  | const k => exact le_trans h hM
  | reg r => exact le_trans h hM
  | load a ih => exact ⟨ih h.1, le_trans h.2.1 hM, le_trans h.2.2 hM⟩
  | bin op a b iha ihb => exact ⟨iha h.1, ihb h.2.1, le_trans h.2.2.1 hM, le_trans h.2.2.2 hM⟩

/-- The cost of an expression whose values are at most `M`. -/
theorem Expr.cost_le {st : State} {M : ℕ} {e : Expr} (h : e.ValsLe st M) :
    (evalExpr st e).2 ≤ e.size * (2 * len M + 1) := by
  induction e with
  | const k =>
    have := len_mono (show k ≤ M from h)
    simp only [evalExpr_const, size_const]; omega
  | reg r =>
    have := len_mono (show st.regs r ≤ M from h)
    simp only [evalExpr_reg, size_reg]; omega
  | load a ih =>
    have h1 := ih h.1
    have h2 := len_mono h.2.1
    have h3 := len_mono h.2.2
    simp only [evalExpr_load, size_load, Nat.add_mul]; omega
  | bin op a b iha ihb =>
    have h1 := iha h.1
    have h2 := ihb h.2.1
    have h3 := len_mono h.2.2.1
    have h4 := len_mono h.2.2.2
    simp only [evalExpr_bin, size_bin, Nat.add_mul]; omega

/-- The total size of a list of expressions. -/
def Expr.listSize (es : List Expr) : ℕ := (es.map Expr.size).sum

@[simp] theorem Expr.listSize_nil : Expr.listSize [] = 0 := rfl
@[simp] theorem Expr.listSize_cons (e : Expr) (es : List Expr) :
    Expr.listSize (e :: es) = e.size + Expr.listSize es := by
  simp [Expr.listSize]

/-- The cost of a list of arguments whose values are at most `M`. -/
theorem evalArgs_cost_le {st : State} {M : ℕ} {es : List Expr} (h : ∀ e ∈ es, e.ValsLe st M) :
    (evalArgs st es).2 ≤ Expr.listSize es * (2 * len M + 1) := by
  induction es with
  | nil => simp
  | cons e es ih =>
    simp only [evalArgs_cons, Expr.listSize_cons, Nat.add_mul]
    have h1 := Expr.cost_le (h e (by simp))
    have h2 := ih (fun e' he' => h e' (by simp [he']))
    omega

attribute [machine_simps] Function.update_apply Function.update_self ite_true ite_false
  if_true if_false

end GI.Machine
