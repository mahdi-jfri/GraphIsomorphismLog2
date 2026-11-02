/-
The language `GI.Lang`: a first-order functional language over values (`GI.Cited.Val`), with
its big-step semantics and its cost model.

**Syntax** (`GI.Lang.Expr`). An expression is evaluated in an environment, a list of values.
Variables are positions in this list, counted from the front: `var 0` is the first entry. A
function body starts with the environment `[arg]`, and `letE e body` evaluates `body` with the
value of `e` added at the end. The constructs are number literals, arithmetic on numbers
(the operations of the machine, `GI.Machine.BinOp`), the empty list, adding an entry at the
end of a list, the length of a list, indexing, a test of whether a value is a number, `if`,
`let`, calls of user functions by index (recursion is allowed), and calls of primitives.

**Primitives** (`GI.Lang.Prim`). A primitive is a machine program with a contract in the style
of `GI.Cited.PolyTimeAt`: on every value `v` with `Pre v`, stored at any base address `b`, it
keeps the cells below `b`, returns an address `r ≥ b` holding some `w` with `Post v w`, and costs
at most `c * (size v + len b + 2) ^ k`. A cited algorithm gives a primitive
(`GI.Lang.Prim.ofCited`).

**Semantics.** `GI.Lang.Eval P env e v cost` says that `e` can evaluate to `v` at cost `cost`.
It is nondeterministic only through the postconditions of primitives. `GI.Lang.EvalAll P env e
Q` says that *every* evaluation of `e` finishes and every result `v` with its cost satisfies
`Q`; it is the form the compiler theorem uses, because the compiled code makes one particular
choice at each primitive call. `EvalAll.sound` and `EvalAll.exists_eval` relate the two.

**Cost model.** Every step pays one plus the weight `Val.wt` of the value it returns (its number
of cells plus the bit lengths of its cells), on top of the cost of its subexpressions. A call
of primitive `p` on `v` also pays `p.bound v = p.c * (size v + 2) ^ p.k`. Indexing pays for the
entry it returns, not for the entries it skips; the compiler pays for those from the cost of
computing the list.
-/
import Workspace.Lang.Val

namespace GI.Lang

open GI.Machine (PolyTimeWith BinOp len)
open GI.Cited (Val ValAt PolyTimeAt)

/-- Expressions of the language. -/
inductive Expr where
  /-- Entry `i` of the environment. -/
  | var (i : ℕ)
  /-- The number `k`. -/
  | nat (k : ℕ)
  /-- A machine operation on two numbers. -/
  | arith (op : BinOp) (a b : Expr)
  /-- The empty list. -/
  | nil
  /-- The list `l` with the value of `e` added at the end. -/
  | snoc (l e : Expr)
  /-- The number of entries of a list. -/
  | length (l : Expr)
  /-- Entry `i` of list `l`, counted from 0. -/
  | get (l i : Expr)
  /-- 1 if the value is a number, 0 if it is a list. -/
  | isNat (e : Expr)
  /-- `t` if `c` is a nonzero number, `e` if it is 0. -/
  | ite (c t e : Expr)
  /-- Evaluate `e`, add its value at the end of the environment, and evaluate `body`. -/
  | letE (e body : Expr)
  /-- Call user function `f` on the value of `a`. -/
  | call (f : ℕ) (a : Expr)
  /-- Call primitive `j` on the value of `a`. -/
  | prim (j : ℕ) (a : Expr)
  deriving Repr

/-- The list of the values of `es`, built with `snoc`. -/
def Expr.mkList (es : List Expr) : Expr := es.foldl .snoc .nil

/-- 1 for a number, 0 for a list. -/
def _root_.GI.Cited.Val.isNatNum : Val → ℕ
  | .nat _ => 1
  | .list _ => 0

/-- The task of a primitive with precondition `Pre` and postcondition `Post`: an instance is a
value with `Pre`, stored in the value format, and a correct output for `v` is a value `w` with
`Post v w`. -/
def primTask (Pre : Val → Prop) (Post : Val → Val → Prop) : GI.Cited.Task {v // Pre v} :=
  GI.Cited.Task.ofVal Subtype.val (fun x w => Post x.1 w)

/-- A primitive: a machine program `prog` with its contract. -/
structure Prim where
  Pre : Val → Prop
  Post : Val → Val → Prop
  c : ℕ
  k : ℕ
  prog : GI.Machine.Program
  spec : PolyTimeWith (primTask Pre Post) prog c k

/-- What a call of primitive `p` on `v` costs in the language: the bound of its contract, with
the length of the base address left out. -/
def Prim.bound (p : Prim) (v : Val) : ℕ := p.c * (v.size + 2) ^ p.k

/-- A program: the bodies of its user functions, and its primitives. -/
structure Program where
  funs : List Expr
  prims : List Prim

/-! ### Semantics -/

/-- `Eval P env e v cost`: in program `P` and environment `env`, the expression `e` can evaluate
to `v`, at cost `cost`. -/
inductive Eval (P : Program) : List Val → Expr → Val → ℕ → Prop where
  | var {env : List Val} {i : ℕ} (h : i < env.length) :
      Eval P env (.var i) env[i] (env[i].wt + 1)
  | nat {env : List Val} (k : ℕ) :
      Eval P env (.nat k) (.nat k) ((Val.nat k).wt + 1)
  | arith {env : List Val} {op : BinOp} {a b : Expr} {x y ca cb : ℕ}
      (ha : Eval P env a (.nat x) ca) (hb : Eval P env b (.nat y) cb) :
      Eval P env (.arith op a b) (.nat (op.eval x y)) (ca + cb + (Val.nat (op.eval x y)).wt + 1)
  | nil {env : List Val} :
      Eval P env .nil (.list []) ((Val.list []).wt + 1)
  | snoc {env : List Val} {l e : Expr} {vs : List Val} {v : Val} {ca cb : ℕ}
      (ha : Eval P env l (.list vs) ca) (hb : Eval P env e v cb) :
      Eval P env (.snoc l e) (.list (vs ++ [v])) (ca + cb + (Val.list (vs ++ [v])).wt + 1)
  | length {env : List Val} {l : Expr} {vs : List Val} {ca : ℕ}
      (ha : Eval P env l (.list vs) ca) :
      Eval P env (.length l) (.nat vs.length) (ca + (Val.nat vs.length).wt + 1)
  | get {env : List Val} {l i : Expr} {vs : List Val} {x ca cb : ℕ}
      (ha : Eval P env l (.list vs) ca) (hb : Eval P env i (.nat x) cb) (hx : x < vs.length) :
      Eval P env (.get l i) vs[x] (ca + cb + vs[x].wt + 1)
  | isNat {env : List Val} {e : Expr} {v : Val} {ca : ℕ}
      (ha : Eval P env e v ca) :
      Eval P env (.isNat e) (.nat v.isNatNum) (ca + (Val.nat v.isNatNum).wt + 1)
  | ite_true {env : List Val} {c t e : Expr} {x : ℕ} {v : Val} {ca cb : ℕ}
      (hc : Eval P env c (.nat x) ca) (hx : x ≠ 0) (ht : Eval P env t v cb) :
      Eval P env (.ite c t e) v (ca + cb + v.wt + 1)
  | ite_false {env : List Val} {c t e : Expr} {v : Val} {ca cb : ℕ}
      (hc : Eval P env c (.nat 0) ca) (he : Eval P env e v cb) :
      Eval P env (.ite c t e) v (ca + cb + v.wt + 1)
  | letE {env : List Val} {e body : Expr} {v w : Val} {ca cb : ℕ}
      (ha : Eval P env e v ca) (hb : Eval P (env ++ [v]) body w cb) :
      Eval P env (.letE e body) w (ca + cb + w.wt + 1)
  | call {env : List Val} {f : ℕ} {a body : Expr} {v w : Val} {ca cb : ℕ}
      (hf : P.funs[f]? = some body) (ha : Eval P env a v ca) (hb : Eval P [v] body w cb) :
      Eval P env (.call f a) w (ca + cb + w.wt + 1)
  | prim {env : List Val} {j : ℕ} {a : Expr} {p : Prim} {v w : Val} {ca : ℕ}
      (hj : P.prims[j]? = some p) (ha : Eval P env a v ca) (hpre : p.Pre v) (hpost : p.Post v w) :
      Eval P env (.prim j a) w (ca + p.bound v + w.wt + 1)

/-- `EvalAll P env e Q`: every evaluation of `e` in `env` finishes, and every result `v` with
its cost satisfies `Q`. A compound expression is described through a condition `R` on the
results of its subexpressions. -/
inductive EvalAll (P : Program) : List Val → Expr → (Val → ℕ → Prop) → Prop where
  | var {env : List Val} {i : ℕ} {Q : Val → ℕ → Prop} (h : i < env.length)
      (hq : Q env[i] (env[i].wt + 1)) : EvalAll P env (.var i) Q
  | nat {env : List Val} {k : ℕ} {Q : Val → ℕ → Prop}
      (hq : Q (.nat k) ((Val.nat k).wt + 1)) : EvalAll P env (.nat k) Q
  | arith {env : List Val} {op : BinOp} {a b : Expr} {Q Ra Rb : Val → ℕ → Prop}
      (ha : EvalAll P env a Ra) (hb : EvalAll P env b Rb)
      (hq : ∀ va ca vb cb, Ra va ca → Rb vb cb → ∃ x y, va = .nat x ∧ vb = .nat y ∧
        Q (.nat (op.eval x y)) (ca + cb + (Val.nat (op.eval x y)).wt + 1)) :
      EvalAll P env (.arith op a b) Q
  | nil {env : List Val} {Q : Val → ℕ → Prop}
      (hq : Q (.list []) ((Val.list []).wt + 1)) : EvalAll P env .nil Q
  | snoc {env : List Val} {l e : Expr} {Q Ra Rb : Val → ℕ → Prop}
      (ha : EvalAll P env l Ra) (hb : EvalAll P env e Rb)
      (hq : ∀ va ca vb cb, Ra va ca → Rb vb cb → ∃ vs, va = .list vs ∧
        Q (.list (vs ++ [vb])) (ca + cb + (Val.list (vs ++ [vb])).wt + 1)) :
      EvalAll P env (.snoc l e) Q
  | length {env : List Val} {l : Expr} {Q Ra : Val → ℕ → Prop}
      (ha : EvalAll P env l Ra)
      (hq : ∀ va ca, Ra va ca → ∃ vs, va = .list vs ∧
        Q (.nat vs.length) (ca + (Val.nat vs.length).wt + 1)) :
      EvalAll P env (.length l) Q
  | get {env : List Val} {l i : Expr} {Q Ra Rb : Val → ℕ → Prop}
      (ha : EvalAll P env l Ra) (hb : EvalAll P env i Rb)
      (hq : ∀ va ca vb cb, Ra va ca → Rb vb cb → ∃ vs x, va = .list vs ∧ vb = .nat x ∧
        ∃ hx : x < vs.length, Q vs[x] (ca + cb + vs[x].wt + 1)) :
      EvalAll P env (.get l i) Q
  | isNat {env : List Val} {e : Expr} {Q Ra : Val → ℕ → Prop}
      (ha : EvalAll P env e Ra)
      (hq : ∀ va ca, Ra va ca → Q (.nat va.isNatNum) (ca + (Val.nat va.isNatNum).wt + 1)) :
      EvalAll P env (.isNat e) Q
  | ite {env : List Val} {c t e : Expr} {Q Rc : Val → ℕ → Prop}
      (hc : EvalAll P env c Rc)
      (hn : ∀ vc cc, Rc vc cc → ∃ x, vc = .nat x)
      (hb : ∀ x cc, Rc (.nat x) cc →
        EvalAll P env (if x = 0 then e else t) (fun w cb => Q w (cc + cb + w.wt + 1))) :
      EvalAll P env (.ite c t e) Q
  | letE {env : List Val} {e body : Expr} {Q Ra : Val → ℕ → Prop}
      (ha : EvalAll P env e Ra)
      (hb : ∀ v ca, Ra v ca →
        EvalAll P (env ++ [v]) body (fun w cb => Q w (ca + cb + w.wt + 1))) :
      EvalAll P env (.letE e body) Q
  | call {env : List Val} {f : ℕ} {a body : Expr} {Q Ra : Val → ℕ → Prop}
      (hf : P.funs[f]? = some body) (ha : EvalAll P env a Ra)
      (hb : ∀ v ca, Ra v ca → EvalAll P [v] body (fun w cb => Q w (ca + cb + w.wt + 1))) :
      EvalAll P env (.call f a) Q
  | prim {env : List Val} {j : ℕ} {a : Expr} {p : Prim} {Q Ra : Val → ℕ → Prop}
      (hj : P.prims[j]? = some p) (ha : EvalAll P env a Ra)
      (hb : ∀ v ca, Ra v ca → p.Pre v ∧ ∀ w, p.Post v w → Q w (ca + p.bound v + w.wt + 1)) :
      EvalAll P env (.prim j a) Q

namespace EvalAll

variable {P : Program}

/-- The consequence rule. -/
theorem mono {env : List Val} {e : Expr} {Q Q' : Val → ℕ → Prop} (h : EvalAll P env e Q)
    (hQ : ∀ v c, Q v c → Q' v c) : EvalAll P env e Q' := by
  induction h generalizing Q' with
  | var h hq => exact .var h (hQ _ _ hq)
  | nat hq => exact .nat (hQ _ _ hq)
  | arith ha hb hq _ _ =>
    refine .arith ha hb fun va ca vb cb h1 h2 => ?_
    obtain ⟨x, y, h3, h4, h5⟩ := hq va ca vb cb h1 h2
    exact ⟨x, y, h3, h4, hQ _ _ h5⟩
  | nil hq => exact .nil (hQ _ _ hq)
  | snoc ha hb hq _ _ =>
    refine .snoc ha hb fun va ca vb cb h1 h2 => ?_
    obtain ⟨vs, h3, h4⟩ := hq va ca vb cb h1 h2
    exact ⟨vs, h3, hQ _ _ h4⟩
  | length ha hq _ =>
    refine .length ha fun va ca h1 => ?_
    obtain ⟨vs, h3, h4⟩ := hq va ca h1
    exact ⟨vs, h3, hQ _ _ h4⟩
  | get ha hb hq _ _ =>
    refine .get ha hb fun va ca vb cb h1 h2 => ?_
    obtain ⟨vs, x, h3, h4, hx, h5⟩ := hq va ca vb cb h1 h2
    exact ⟨vs, x, h3, h4, hx, hQ _ _ h5⟩
  | isNat ha hq _ => exact .isNat ha fun va ca h1 => hQ _ _ (hq va ca h1)
  | ite hc hn hb _ ih => exact .ite hc hn fun x cc h1 => ih x cc h1 fun w cb hw => hQ _ _ hw
  | letE ha hb _ ih => exact .letE ha fun v ca h1 => ih v ca h1 fun w cb hw => hQ _ _ hw
  | call hf ha hb _ ih => exact .call hf ha fun v ca h1 => ih v ca h1 fun w cb hw => hQ _ _ hw
  | prim hj ha hb _ =>
    exact .prim hj ha fun v ca h1 => ⟨(hb v ca h1).1, fun w hw => hQ _ _ ((hb v ca h1).2 w hw)⟩

/-- Every evaluation satisfies the postcondition. -/
theorem sound {env : List Val} {e : Expr} {Q : Val → ℕ → Prop} (h : EvalAll P env e Q)
    {v : Val} {c : ℕ} (he : Eval P env e v c) : Q v c := by
  induction h generalizing v c with
  | var h hq => cases he; exact hq
  | nat hq => cases he; exact hq
  | arith ha hb hq iha ihb =>
    cases he with
    | arith h1 h2 =>
      obtain ⟨x, y, h3, h4, h5⟩ := hq _ _ _ _ (iha h1) (ihb h2)
      cases h3; cases h4; exact h5
  | nil hq => cases he; exact hq
  | snoc ha hb hq iha ihb =>
    cases he with
    | snoc h1 h2 =>
      obtain ⟨vs, h3, h4⟩ := hq _ _ _ _ (iha h1) (ihb h2)
      cases h3; exact h4
  | length ha hq iha =>
    cases he with
    | length h1 =>
      obtain ⟨vs, h3, h4⟩ := hq _ _ (iha h1)
      cases h3; exact h4
  | get ha hb hq iha ihb =>
    cases he with
    | get h1 h2 hx =>
      obtain ⟨vs, x, h3, h4, hx', h5⟩ := hq _ _ _ _ (iha h1) (ihb h2)
      cases h3; cases h4; exact h5
  | isNat ha hq iha =>
    cases he with
    | isNat h1 => exact hq _ _ (iha h1)
  | ite hc hn hb ihc ih =>
    cases he with
    | ite_true h1 hx h2 => exact ih _ _ (ihc h1) (by rw [if_neg hx]; exact h2)
    | ite_false h1 h2 => exact ih _ _ (ihc h1) (by rw [if_pos rfl]; exact h2)
  | letE ha hb iha ih =>
    cases he with
    | letE h1 h2 => exact ih _ _ (iha h1) h2
  | call hf ha hb iha ih =>
    cases he with
    | call hf' h1 h2 =>
      rw [hf] at hf'; cases hf'
      exact ih _ _ (iha h1) h2
  | prim hj ha hb iha =>
    cases he with
    | prim hj' h1 hpre hpost =>
      rw [hj] at hj'; cases hj'
      exact (hb _ _ (iha h1)).2 _ hpost

/-- Every result that `EvalAll` describes comes from an evaluation. -/
theorem withEval {env : List Val} {e : Expr} {Q : Val → ℕ → Prop} (h : EvalAll P env e Q) :
    EvalAll P env e (fun v c => Q v c ∧ Eval P env e v c) := by
  induction h with
  | var h hq => exact .var h ⟨hq, .var h⟩
  | nat hq => exact .nat ⟨hq, .nat _⟩
  | arith _ _ hq iha ihb =>
    refine .arith iha ihb fun va ca vb cb ⟨h1, e1⟩ ⟨h2, e2⟩ => ?_
    obtain ⟨x, y, rfl, rfl, h5⟩ := hq va ca vb cb h1 h2
    exact ⟨x, y, rfl, rfl, h5, .arith e1 e2⟩
  | nil hq => exact .nil ⟨hq, .nil⟩
  | snoc _ _ hq iha ihb =>
    refine .snoc iha ihb fun va ca vb cb ⟨h1, e1⟩ ⟨h2, e2⟩ => ?_
    obtain ⟨vs, rfl, h4⟩ := hq va ca vb cb h1 h2
    exact ⟨vs, rfl, h4, .snoc e1 e2⟩
  | length _ hq iha =>
    refine .length iha fun va ca ⟨h1, e1⟩ => ?_
    obtain ⟨vs, rfl, h4⟩ := hq va ca h1
    exact ⟨vs, rfl, h4, .length e1⟩
  | get _ _ hq iha ihb =>
    refine .get iha ihb fun va ca vb cb ⟨h1, e1⟩ ⟨h2, e2⟩ => ?_
    obtain ⟨vs, x, rfl, rfl, hx, h5⟩ := hq va ca vb cb h1 h2
    exact ⟨vs, x, rfl, rfl, hx, h5, .get e1 e2 hx⟩
  | isNat _ hq iha => exact .isNat iha fun va ca ⟨h1, e1⟩ => ⟨hq va ca h1, .isNat e1⟩
  | ite _ hn _ ihc ih =>
    refine .ite ihc (fun vc cc h1 => hn vc cc h1.1) fun x cc ⟨h1, e1⟩ => ?_
    refine (ih x cc h1).mono fun w cb ⟨hw, ew⟩ => ⟨hw, ?_⟩
    by_cases hx : x = 0
    · subst hx; rw [if_pos rfl] at ew; exact .ite_false e1 ew
    · rw [if_neg hx] at ew; exact .ite_true e1 hx ew
  | letE _ _ iha ih =>
    exact .letE iha fun v ca ⟨h1, e1⟩ =>
      (ih v ca h1).mono fun w cb ⟨hw, ew⟩ => ⟨hw, .letE e1 ew⟩
  | call hf _ _ iha ih =>
    exact .call hf iha fun v ca ⟨h1, e1⟩ =>
      (ih v ca h1).mono fun w cb ⟨hw, ew⟩ => ⟨hw, .call hf e1 ew⟩
  | prim hj _ hb iha =>
    exact .prim hj iha fun v ca ⟨h1, e1⟩ =>
      ⟨(hb v ca h1).1, fun w hw => ⟨(hb v ca h1).2 w hw, .prim hj e1 (hb v ca h1).1 hw⟩⟩

end EvalAll

/-! ### Primitives -/

/-- A memory holding `v` at address 0, and 0 after it. -/
def memOfVal (v : Val) : ℕ → ℕ := fun i => v.cells.getD i 0

theorem valAt_memOfVal (v : Val) : ValAt (memOfVal v) 0 v := fun i hi => by
  simp only [memOfVal, Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    Option.getD_some]

/-- A primitive has an output for every input that meets its precondition. -/
theorem Prim.exists_post (p : Prim) {v : Val} (hv : p.Pre v) : ∃ w, p.Post v w := by
  obtain ⟨_, _, st, _, _, _, _, ⟨w, _, hw⟩, _⟩ := p.spec ⟨v, hv⟩ 0 (memOfVal v) (valAt_memOfVal v)
  exact ⟨w, hw⟩

/-- An evaluation that every evaluation satisfies `Q` has an evaluation. -/
theorem EvalAll.exists_eval {P : Program} {env : List Val} {e : Expr} {Q : Val → ℕ → Prop}
    (h : EvalAll P env e Q) : ∃ v c, Eval P env e v c ∧ Q v c := by
  induction h with
  | var h hq => exact ⟨_, _, .var h, hq⟩
  | nat hq => exact ⟨_, _, .nat _, hq⟩
  | arith ha hb hq iha ihb =>
    obtain ⟨va, ca, h1, r1⟩ := iha
    obtain ⟨vb, cb, h2, r2⟩ := ihb
    obtain ⟨x, y, rfl, rfl, h5⟩ := hq _ _ _ _ r1 r2
    exact ⟨_, _, .arith h1 h2, h5⟩
  | nil hq => exact ⟨_, _, .nil, hq⟩
  | snoc ha hb hq iha ihb =>
    obtain ⟨va, ca, h1, r1⟩ := iha
    obtain ⟨vb, cb, h2, r2⟩ := ihb
    obtain ⟨vs, rfl, h5⟩ := hq _ _ _ _ r1 r2
    exact ⟨_, _, .snoc h1 h2, h5⟩
  | length ha hq iha =>
    obtain ⟨va, ca, h1, r1⟩ := iha
    obtain ⟨vs, rfl, h5⟩ := hq _ _ r1
    exact ⟨_, _, .length h1, h5⟩
  | get ha hb hq iha ihb =>
    obtain ⟨va, ca, h1, r1⟩ := iha
    obtain ⟨vb, cb, h2, r2⟩ := ihb
    obtain ⟨vs, x, rfl, rfl, hx, h5⟩ := hq _ _ _ _ r1 r2
    exact ⟨_, _, .get h1 h2 hx, h5⟩
  | isNat ha hq iha =>
    obtain ⟨va, ca, h1, r1⟩ := iha
    exact ⟨_, _, .isNat h1, hq _ _ r1⟩
  | ite hc hn hb ihc ih =>
    obtain ⟨vc, cc, h1, r1⟩ := ihc
    obtain ⟨x, rfl⟩ := hn _ _ r1
    obtain ⟨w, cb, h2, r2⟩ := ih _ _ r1
    by_cases hx : x = 0
    · subst hx; rw [if_pos rfl] at h2; exact ⟨_, _, .ite_false h1 h2, r2⟩
    · rw [if_neg hx] at h2; exact ⟨_, _, .ite_true h1 hx h2, r2⟩
  | letE ha hb iha ih =>
    obtain ⟨v, ca, h1, r1⟩ := iha
    obtain ⟨w, cb, h2, r2⟩ := ih _ _ r1
    exact ⟨_, _, .letE h1 h2, r2⟩
  | call hf ha hb iha ih =>
    obtain ⟨v, ca, h1, r1⟩ := iha
    obtain ⟨w, cb, h2, r2⟩ := ih _ _ r1
    exact ⟨_, _, .call hf h1 h2, r2⟩
  | prim hj ha hb iha =>
    obtain ⟨v, ca, h1, r1⟩ := iha
    obtain ⟨hpre, hq⟩ := hb _ _ r1
    obtain ⟨w, hw⟩ := Prim.exists_post _ hpre
    exact ⟨_, _, .prim hj h1 hpre hw, hq w hw⟩

/-- A cited algorithm `p` for the task `Task.ofVal enc Correct`, with the constants `c, k` of its
bound, as a primitive. Its precondition says that the value encodes an instance, and its
postcondition that the output is correct for some instance with this encoding. -/
def Prim.ofCited {α : Type} (enc : α → Val) (Correct : α → Val → Prop) (prog : GI.Machine.Program)
    (c k : ℕ) (h : PolyTimeWith (GI.Cited.Task.ofVal enc Correct) prog c k) : Prim where
  Pre v := ∃ x, enc x = v
  Post v w := ∃ x, enc x = v ∧ Correct x w
  c := c
  k := k
  prog := prog
  spec := by
    rintro ⟨v, x, rfl⟩ b mem hx
    obtain ⟨fuel, o, st, cost, hrun, hbelow, hge, ⟨w, hw, hc⟩, hcost⟩ := h x b mem hx
    exact ⟨fuel, o, st, cost, hrun, hbelow, hge, ⟨w, hw, x, rfl, hc⟩, hcost⟩

/-- Every cited algorithm in the value format gives a primitive with the same program. -/
theorem Prim.exists_ofCited {α : Type} {enc : α → Val} {Correct : α → Val → Prop}
    {prog : GI.Machine.Program} (h : PolyTimeAt (GI.Cited.Task.ofVal enc Correct) prog) :
    ∃ p : Prim, p.prog = prog ∧ (∀ v, p.Pre v ↔ ∃ x, enc x = v) ∧
      ∀ v w, p.Post v w ↔ ∃ x, enc x = v ∧ Correct x w := by
  obtain ⟨c, k, h⟩ := h
  exact ⟨Prim.ofCited enc Correct prog c k h, rfl, fun _ => Iff.rfl, fun _ _ => Iff.rfl⟩

end GI.Lang
