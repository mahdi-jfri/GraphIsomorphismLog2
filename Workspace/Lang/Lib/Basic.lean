/-
Basic tools for writing and verifying `GI.Lang` programs.

**Linking.** A program addresses its functions and primitives by index. A specification
`EvalAll P env e Q` only uses `P` through the lookups `P.funs[f]?` and `P.prims[j]?` of the
indices that `e` reaches. So:
* `EvalAll.of_sub`: a specification stays true in any program that extends `P` at the end
  (`Program.Sub`);
* `EvalAll.relink`: more generally, renaming the indices of `e` along maps `rf, rp` keeps the
  specification in any program `P'` that holds, at the renamed indices, the renamed bodies
  and the same primitives (`Program.Relinks`).
Library functions are written as Lean functions of the indices they occupy and call (see
`Workspace.Lang.Lib.Loop`), and their specifications assume only lookups, so they hold in
every program that places them at those indices.

**Function specifications.** `FunAll P f v Q` says that user function `f` exists and every run
of its body on the argument `v` finishes with a result and a cost satisfying `Q`.
`EvalAll.call_funAll` turns it into a specification of a call.

**Deterministic pieces.** `Det P env e v c` says that every evaluation of `e` gives `v`, at cost
at most `c`. The `Det.*` lemmas build these facts construct by construct.

**Cost facts.** Every evaluation pays at least the weight of its result (`EvalAll.wt_lt`), and
`wt_list_le`, `wt_le_wt_list` relate the weight of a list to the weights of its entries.
-/
module

public import Workspace.Lang.Syntax
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace GI.Lang

open GI.Machine (BinOp len len_le_self len_mono)
open GI.Cited (Val)

/-! ### Linking -/

/-- `P'` extends `P`: its lists of functions and primitives start with those of `P`. -/
def Program.Sub (P P' : Program) : Prop := P.funs <+: P'.funs ∧ P.prims <+: P'.prims

theorem Program.Sub.refl (P : Program) : P.Sub P := ⟨List.prefix_refl _, List.prefix_refl _⟩

theorem Program.Sub.trans {P P' P'' : Program} (h : P.Sub P') (h' : P'.Sub P'') : P.Sub P'' :=
  ⟨h.1.trans h'.1, h.2.trans h'.2⟩

theorem Program.Sub.funs_eq {P P' : Program} (h : P.Sub P') {f : ℕ} {body : Expr}
    (hf : P.funs[f]? = some body) : P'.funs[f]? = some body := by
  obtain ⟨l, hl⟩ := h.1
  rw [← hl, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hf).1]
  exact hf

theorem Program.Sub.prims_eq {P P' : Program} (h : P.Sub P') {j : ℕ} {p : Prim}
    (hj : P.prims[j]? = some p) : P'.prims[j]? = some p := by
  obtain ⟨l, hl⟩ := h.2
  rw [← hl, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hj).1]
  exact hj

/-- A specification stays true in a larger program. -/
theorem EvalAll.of_sub {P P' : Program} (hs : P.Sub P') {env : List Val} {e : Expr}
    {Q : Val → ℕ → Prop} (h : EvalAll P env e Q) : EvalAll P' env e Q := by
  induction h with
  | var h hq => exact .var h hq
  | nat hq => exact .nat hq
  | arith _ _ hq iha ihb => exact .arith iha ihb hq
  | nil hq => exact .nil hq
  | snoc _ _ hq iha ihb => exact .snoc iha ihb hq
  | length _ hq iha => exact .length iha hq
  | get _ _ hq iha ihb => exact .get iha ihb hq
  | isNat _ hq iha => exact .isNat iha hq
  | ite _ hn _ ihc ih => exact .ite ihc hn ih
  | letE _ _ iha ih => exact .letE iha ih
  | call hf _ _ iha ih => exact .call (hs.funs_eq hf) iha ih
  | prim hj _ hb iha => exact .prim (hs.prims_eq hj) iha hb

/-- Rename the function indices of an expression by `rf` and the primitive indices by `rp`. -/
def Expr.relink (rf rp : ℕ → ℕ) : Expr → Expr
  | .var i => .var i
  | .nat k => .nat k
  | .arith op a b => .arith op (a.relink rf rp) (b.relink rf rp)
  | .nil => .nil
  | .snoc l e => .snoc (l.relink rf rp) (e.relink rf rp)
  | .length l => .length (l.relink rf rp)
  | .get l i => .get (l.relink rf rp) (i.relink rf rp)
  | .isNat e => .isNat (e.relink rf rp)
  | .ite c t e => .ite (c.relink rf rp) (t.relink rf rp) (e.relink rf rp)
  | .letE e body => .letE (e.relink rf rp) (body.relink rf rp)
  | .call f a => .call (rf f) (a.relink rf rp)
  | .prim j a => .prim (rp j) (a.relink rf rp)

/-- `P'` holds a renamed copy of `P`: function `f` of `P`, renamed, is function `rf f` of `P'`,
and primitive `j` of `P` is primitive `rp j` of `P'`. -/
def Program.Relinks (P P' : Program) (rf rp : ℕ → ℕ) : Prop :=
  (∀ f body, P.funs[f]? = some body → P'.funs[rf f]? = some (body.relink rf rp)) ∧
    ∀ j p, P.prims[j]? = some p → P'.prims[rp j]? = some p

/-- A specification moves along a renaming of indices. -/
theorem EvalAll.relink {P P' : Program} {rf rp : ℕ → ℕ} (hr : P.Relinks P' rf rp)
    {env : List Val} {e : Expr} {Q : Val → ℕ → Prop} (h : EvalAll P env e Q) :
    EvalAll P' env (e.relink rf rp) Q := by
  induction h with
  | var h hq => exact .var h hq
  | nat hq => exact .nat hq
  | arith _ _ hq iha ihb => exact .arith iha ihb hq
  | nil hq => exact .nil hq
  | snoc _ _ hq iha ihb => exact .snoc iha ihb hq
  | length _ hq iha => exact .length iha hq
  | get _ _ hq iha ihb => exact .get iha ihb hq
  | isNat _ hq iha => exact .isNat iha hq
  | ite _ hn _ ihc ih =>
    refine .ite ihc hn fun x cc h => ?_
    have := ih x cc h
    by_cases hx : x = 0
    · simp only [hx, if_pos] at this ⊢; exact this
    · simp only [hx, if_false] at this ⊢; exact this
  | letE _ _ iha ih => exact .letE iha ih
  | call hf _ _ iha ih => exact .call (hr.1 _ _ hf) iha ih
  | prim hj _ hb iha => exact .prim (hr.2 _ _ hj) iha hb

/-- Shifting all indices by fixed offsets: a program whose lists of functions and primitives
contain those of `P` at offsets `df` and `dp`, with function bodies shifted. -/
theorem Program.relinks_shift {P P' : Program} {df dp : ℕ}
    (hf : ∀ f (h : f < P.funs.length),
      P'.funs[df + f]? = some (P.funs[f].relink (df + ·) (dp + ·)))
    (hp : ∀ j (h : j < P.prims.length), P'.prims[dp + j]? = some P.prims[j]) :
    P.Relinks P' (df + ·) (dp + ·) := by
  refine ⟨fun f body hb => ?_, fun j p hj => ?_⟩
  · obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.mp hb
    exact hf f h
  · obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.mp hj
    exact hp j h

/-- The functions `fs` sit in `P` at indices `b, b + 1, …`. Library modules of several
functions are placed with this. -/
def Program.HasAt (P : Program) (b : ℕ) (fs : List Expr) : Prop :=
  ∀ j (h : j < fs.length), P.funs[b + j]? = some fs[j]

theorem Program.hasAt_append (A fs B : List Expr) (ps : List Prim) :
    (Program.mk (A ++ fs ++ B) ps).HasAt A.length fs := by
  intro j h
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left h, List.getElem?_eq_getElem h]

theorem Program.HasAt.get {P : Program} {b : ℕ} {fs : List Expr} (h : P.HasAt b fs) {j : ℕ}
    (hj : j < fs.length) : P.funs[b + j]? = some fs[j] := h j hj

/-! ### Function specifications -/

/-- User function `f` of `P` exists, and every run of its body on `v` finishes with a result
and a cost satisfying `Q`. The cost is that of the body; a call adds the cost of the argument
and the weight of the result plus one. -/
def FunAll (P : Program) (f : ℕ) (v : Val) (Q : Val → ℕ → Prop) : Prop :=
  ∃ body, P.funs[f]? = some body ∧ EvalAll P [v] body Q

theorem FunAll.mono {P : Program} {f : ℕ} {v : Val} {Q Q' : Val → ℕ → Prop}
    (h : FunAll P f v Q) (hQ : ∀ w c, Q w c → Q' w c) : FunAll P f v Q' := by
  obtain ⟨body, hb, h⟩ := h
  exact ⟨body, hb, h.mono hQ⟩

theorem FunAll.of_sub {P P' : Program} (hs : P.Sub P') {f : ℕ} {v : Val}
    {Q : Val → ℕ → Prop} (h : FunAll P f v Q) : FunAll P' f v Q := by
  obtain ⟨body, hb, h⟩ := h
  exact ⟨body, hs.funs_eq hb, h.of_sub hs⟩

theorem FunAll.intro {P : Program} {f : ℕ} {body : Expr} (hf : P.funs[f]? = some body)
    {v : Val} {Q : Val → ℕ → Prop} (h : EvalAll P [v] body Q) : FunAll P f v Q :=
  ⟨body, hf, h⟩

/-- A call of a function with a specification. -/
theorem EvalAll.call_funAll {P : Program} {env : List Val} {f : ℕ} {a : Expr}
    {Q Ra : Val → ℕ → Prop} (ha : EvalAll P env a Ra)
    (hb : ∀ v ca, Ra v ca → FunAll P f v (fun w cb => Q w (ca + cb + w.wt + 1))) :
    EvalAll P env (.call f a) Q := by
  obtain ⟨v₀, c₀, -, h₀⟩ := ha.exists_eval
  obtain ⟨body, hf, -⟩ := hb v₀ c₀ h₀
  refine .call hf ha fun v ca h => ?_
  obtain ⟨body', hf', hb'⟩ := hb v ca h
  rw [hf] at hf'
  cases hf'
  exact hb'

/-! ### Every evaluation pays for its result -/

theorem Eval.wt_lt {P : Program} {env : List Val} {e : Expr} {v : Val} {c : ℕ}
    (h : Eval P env e v c) : v.wt < c := by
  cases h <;> omega

theorem EvalAll.wt_lt {P : Program} {env : List Val} {e : Expr} {Q : Val → ℕ → Prop}
    (h : EvalAll P env e Q) : EvalAll P env e (fun v c => Q v c ∧ v.wt < c) :=
  h.withEval.mono fun _ _ h => ⟨h.1, h.2.wt_lt⟩

theorem FunAll.wt_lt {P : Program} {f : ℕ} {v : Val} {Q : Val → ℕ → Prop}
    (h : FunAll P f v Q) : FunAll P f v (fun w c => Q w c ∧ w.wt < c) := by
  obtain ⟨body, hb, h⟩ := h
  exact ⟨body, hb, h.wt_lt⟩

/-! ### Weights -/

theorem cellWt_cellsList (vs : List Val) : cellWt (Val.cellsList vs) = (vs.map Val.wt).sum := by
  induction vs with
  | nil => simp
  | cons v vs ih => simp [ih, Val.wt]

theorem length_cellsList (vs : List Val) : (Val.cellsList vs).length = (vs.map Val.size).sum := by
  induction vs with
  | nil => simp
  | cons v vs ih => simp [ih, size_eq_length]

theorem sum_size_le_sum_wt (vs : List Val) : (vs.map Val.size).sum ≤ (vs.map Val.wt).sum := by
  induction vs with
  | nil => simp
  | cons v vs ih => have := v.size_le_wt; simp; omega

/-- The weight of a list: the weights of its entries and the header. -/
theorem wt_list_eq (vs : List Val) :
    (Val.list vs).wt = (vs.map Val.wt).sum + len vs.length + len (vs.map Val.size).sum + 4 := by
  rw [wt_list, cellWt_cellsList, length_cellsList]; omega

theorem wt_list_le (vs : List Val) :
    (Val.list vs).wt ≤ 2 * (vs.map Val.wt).sum + vs.length + 4 := by
  rw [wt_list_eq]
  have := len_le_self vs.length
  have := len_le_self (vs.map Val.size).sum
  have := sum_size_le_sum_wt vs
  omega

theorem sum_wt_lt_wt_list (vs : List Val) : (vs.map Val.wt).sum < (Val.list vs).wt := by
  rw [wt_list_eq]; omega

theorem wt_le_wt_list {vs : List Val} {v : Val} (hv : v ∈ vs) : v.wt < (Val.list vs).wt :=
  lt_of_le_of_lt (List.le_sum_of_mem (List.mem_map_of_mem hv)) (sum_wt_lt_wt_list vs)

theorem wt_getElem_lt (vs : List Val) (i : ℕ) (h : i < vs.length) : vs[i].wt < (Val.list vs).wt :=
  wt_le_wt_list (List.getElem_mem h)

theorem length_lt_wt_list (vs : List Val) : vs.length < (Val.list vs).wt := by
  have : vs.length ≤ (vs.map Val.wt).sum := by
    have h := length_le_cellsList vs
    have := sum_size_le_sum_wt vs
    rw [length_cellsList] at h; omega
  have := sum_wt_lt_wt_list vs; omega

/-- A list is heavier than any of its prefixes. -/
theorem wt_list_mono {vs ws : List Val} (h : vs <+: ws) : (Val.list vs).wt ≤ (Val.list ws).wt := by
  obtain ⟨l, rfl⟩ := h
  rw [wt_list_eq, wt_list_eq]
  simp only [List.map_append, List.sum_append, List.length_append]
  have := len_mono (show vs.length ≤ vs.length + l.length by omega)
  have := len_mono (show (vs.map Val.size).sum ≤ (vs.map Val.size).sum + (l.map Val.size).sum
    by omega)
  omega

@[simp] theorem wt_list_nil : (Val.list []).wt = 4 := by decide

theorem wt_nat' (k : ℕ) : (Val.nat k).wt = len k + 2 := wt_nat k

theorem wt_nat_le (k : ℕ) : (Val.nat k).wt ≤ k + 2 := by
  rw [wt_nat]; have := len_le_self k; omega

/-- The weight of a list of four values. -/
theorem wt_list4_le (a b c d : Val) :
    (Val.list [a, b, c, d]).wt ≤ 2 * (a.wt + b.wt + c.wt + d.wt) + 8 := by
  have := wt_list_le [a, b, c, d]; simp at this; omega

theorem wt_list3_le (a b c : Val) :
    (Val.list [a, b, c]).wt ≤ 2 * (a.wt + b.wt + c.wt) + 7 := by
  have := wt_list_le [a, b, c]; simp at this; omega

theorem wt_list2_le (a b : Val) :
    (Val.list [a, b]).wt ≤ 2 * (a.wt + b.wt) + 6 := by
  have := wt_list_le [a, b]; simp at this; omega

theorem wt_list1_le (a : Val) : (Val.list [a]).wt ≤ 2 * a.wt + 5 := by
  have := wt_list_le [a]; simp at this; omega

/-! ### Deterministic pieces -/

/-- Every evaluation of `e` gives `v`, at cost at most `c`. -/
def Det (P : Program) (env : List Val) (e : Expr) (v : Val) (c : ℕ) : Prop :=
  EvalAll P env e (fun w c' => w = v ∧ c' ≤ c)

namespace Det

variable {P : Program} {env : List Val}

theorem mono {e : Expr} {v : Val} {c c' : ℕ} (h : Det P env e v c) (hc : c ≤ c') :
    Det P env e v c' :=
  EvalAll.mono h fun _ _ h => ⟨h.1, h.2.trans hc⟩

theorem of_sub {P' : Program} (hs : P.Sub P') {e : Expr} {v : Val} {c : ℕ}
    (h : Det P env e v c) : Det P' env e v c := EvalAll.of_sub hs h

/-- Use a deterministic piece in a specification. -/
theorem post {e : Expr} {v : Val} {c : ℕ} {Q : Val → ℕ → Prop} (h : Det P env e v c)
    (hq : ∀ c' ≤ c, Q v c') : EvalAll P env e Q :=
  EvalAll.mono h fun _ _ h => h.1 ▸ hq _ h.2

theorem var {i : ℕ} (h : i < env.length) : Det P env (.var i) env[i] (env[i].wt + 1) :=
  EvalAll.var h ⟨rfl, le_rfl⟩

theorem var' {i : ℕ} {v : Val} (h : env[i]? = some v) : Det P env (.var i) v (v.wt + 1) := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp h
  exact var hi

theorem nat (k : ℕ) : Det P env (.nat k) (.nat k) (k + 3) :=
  EvalAll.nat ⟨rfl, by have := wt_nat_le k; omega⟩

theorem arith {op : BinOp} {a b : Expr} {x y ca cb : ℕ} (ha : Det P env a (.nat x) ca)
    (hb : Det P env b (.nat y) cb) :
    Det P env (.arith op a b) (.nat (op.eval x y)) (ca + cb + (Val.nat (op.eval x y)).wt + 1) :=
  EvalAll.arith ha hb fun _ _ _ _ h1 h2 => ⟨x, y, h1.1, h2.1, rfl, by omega⟩

theorem nil : Det P env .nil (.list []) 5 := EvalAll.nil ⟨rfl, by simp⟩

theorem snoc {l e : Expr} {vs : List Val} {v : Val} {ca cb : ℕ} (ha : Det P env l (.list vs) ca)
    (hb : Det P env e v cb) :
    Det P env (.snoc l e) (.list (vs ++ [v])) (ca + cb + (Val.list (vs ++ [v])).wt + 1) :=
  EvalAll.snoc ha hb fun _ _ _ _ h1 h2 => by
    obtain ⟨rfl, h1⟩ := h1
    obtain ⟨rfl, h2⟩ := h2
    exact ⟨vs, rfl, rfl, by omega⟩

theorem length {l : Expr} {vs : List Val} {ca : ℕ} (ha : Det P env l (.list vs) ca) :
    Det P env (.length l) (.nat vs.length) (ca + vs.length + 3) :=
  EvalAll.length ha fun _ _ h1 => ⟨vs, h1.1, rfl, by have := wt_nat_le vs.length; omega⟩

theorem get {l i : Expr} {vs : List Val} {x ca cb : ℕ} (ha : Det P env l (.list vs) ca)
    (hb : Det P env i (.nat x) cb) (hx : x < vs.length) :
    Det P env (.get l i) vs[x] (ca + cb + vs[x].wt + 1) :=
  EvalAll.get ha hb fun _ _ _ _ h1 h2 => ⟨vs, x, h1.1, h2.1, hx, rfl, by omega⟩

theorem isNat {e : Expr} {v : Val} {ca : ℕ} (ha : Det P env e v ca) :
    Det P env (.isNat e) (.nat v.isNatNum) (ca + 4) :=
  EvalAll.isNat ha fun w _ h1 => by
    obtain ⟨rfl, h1⟩ := h1
    refine ⟨rfl, ?_⟩
    have : (Val.nat w.isNatNum).wt ≤ 3 := by
      cases w <;> simp [Val.isNatNum, wt_nat, GI.Machine.len_zero]
    omega

theorem post_add {t : Expr} {v : Val} {ct cc' cc : ℕ} (ht : Det P env t v ct) (h2 : cc' ≤ cc) :
    EvalAll P env t (fun w cb => (fun w c' => w = v ∧ c' ≤ cc + ct + v.wt + 1) w
      (cc' + cb + w.wt + 1)) :=
  EvalAll.mono ht fun _ _ h => ⟨h.1, by rw [h.1]; omega⟩

theorem ite_pos {c t e : Expr} {x : ℕ} {v : Val} {cc ct : ℕ} (hc : Det P env c (.nat x) cc)
    (hx : x ≠ 0) (ht : Det P env t v ct) : Det P env (.ite c t e) v (cc + ct + v.wt + 1) :=
  EvalAll.ite hc (fun _ _ h => ⟨x, h.1⟩) fun y cc' h => by
    obtain ⟨h1, h2⟩ := h
    cases h1
    rw [if_neg hx]
    exact post_add ht h2

theorem ite_zero {c t e : Expr} {v : Val} {cc ce : ℕ} (hc : Det P env c (.nat 0) cc)
    (he : Det P env e v ce) : Det P env (.ite c t e) v (cc + ce + v.wt + 1) :=
  EvalAll.ite hc (fun _ _ h => ⟨0, h.1⟩) fun y cc' h => by
    obtain ⟨h1, h2⟩ := h
    cases h1
    rw [if_pos rfl]
    exact post_add he h2

/-- `if` on a test whose value is known. -/
theorem ite {c t e : Expr} {x : ℕ} {v : Val} {cc ct ce : ℕ} (hc : Det P env c (.nat x) cc)
    (ht : x ≠ 0 → Det P env t v ct) (he : x = 0 → Det P env e v ce) :
    Det P env (.ite c t e) v (cc + max ct ce + v.wt + 1) := by
  by_cases hx : x = 0
  · subst hx; exact (ite_zero hc (he rfl)).mono (by omega)
  · exact (ite_pos hc hx (ht hx)).mono (by omega)

theorem letE {e body : Expr} {v w : Val} {ca cb : ℕ} (ha : Det P env e v ca)
    (hb : Det P (env ++ [v]) body w cb) : Det P env (.letE e body) w (ca + cb + w.wt + 1) :=
  EvalAll.letE ha fun _ _ h => by
    obtain ⟨h1, h2⟩ := h
    subst h1
    exact EvalAll.mono hb fun _ _ h => ⟨h.1, by rw [h.1]; omega⟩

/-- A call of a function that computes `w` at cost at most `cb`. -/
theorem call {f : ℕ} {a : Expr} {v w : Val} {ca cb : ℕ} (ha : Det P env a v ca)
    (hf : FunAll P f v (fun w' c => w' = w ∧ c ≤ cb)) :
    Det P env (.call f a) w (ca + cb + w.wt + 1) :=
  EvalAll.call_funAll ha fun _ _ h => by
    obtain ⟨h1, h2⟩ := h
    subst h1
    exact hf.mono fun _ _ h => ⟨h.1, by rw [h.1]; omega⟩

/-- A call of a primitive whose postcondition fixes the result. -/
theorem prim {j : ℕ} {a : Expr} {p : Prim} {v w : Val} {ca : ℕ} (hj : P.prims[j]? = some p)
    (ha : Det P env a v ca) (hpre : p.Pre v) (hpost : ∀ w', p.Post v w' → w' = w) :
    Det P env (.prim j a) w (ca + p.bound v + w.wt + 1) :=
  EvalAll.prim hj ha fun _ _ h => by
    obtain ⟨h1, h2⟩ := h
    subst h1
    exact ⟨hpre, fun w' hw' => by have := hpost w' hw'; subst this; exact ⟨rfl, by omega⟩⟩

end Det

/-- A deterministic function: every run of `f` on `v` gives `w`, at cost at most `c`. -/
abbrev FunDet (P : Program) (f : ℕ) (v w : Val) (c : ℕ) : Prop :=
  FunAll P f v (fun w' c' => w' = w ∧ c' ≤ c)

theorem FunDet.intro {P : Program} {f : ℕ} {body : Expr} (hf : P.funs[f]? = some body)
    {v w : Val} {c : ℕ} (h : Det P [v] body w c) : FunDet P f v w c := ⟨body, hf, h⟩

theorem FunDet.mono {P : Program} {f : ℕ} {v w : Val} {c c' : ℕ} (h : FunDet P f v w c)
    (hc : c ≤ c') : FunDet P f v w c' :=
  FunAll.mono h fun _ _ h => ⟨h.1, h.2.trans hc⟩

/-! ### Arguments

Functions of several arguments take one list. `arg j` is entry `j` of the argument. -/

/-- Entry `j` of the argument of a function. -/
def arg (j : ℕ) : Expr := .get (.var 0) (.nat j)

/-- Reading an entry of the argument costs at most twice the weight of the argument, plus
`j + 6`. -/
theorem Det.arg {P : Program} {vs : List Val} {rest : List Val} {j : ℕ} (hj : j < vs.length) :
    Det P (.list vs :: rest) (GI.Lang.arg j) vs[j] (2 * (Val.list vs).wt + j + 5) := by
  have h := Det.get (P := P) (Det.var (env := .list vs :: rest) (i := 0) (by simp)) (Det.nat j) hj
  refine h.mono ?_
  have := wt_getElem_lt vs j hj
  simp only [List.getElem_cons_zero]
  omega

/-! ### Short lists -/

/-- The list `[a]`. -/
def mk1 (a : Expr) : Expr := .snoc .nil a
/-- The list `[a, b]`. -/
def mk2 (a b : Expr) : Expr := .snoc (mk1 a) b
/-- The list `[a, b, c]`. -/
def mk3 (a b c : Expr) : Expr := .snoc (mk2 a b) c
/-- The list `[a, b, c, d]`. -/
def mk4 (a b c d : Expr) : Expr := .snoc (mk3 a b c) d

namespace Det

variable {P : Program} {env : List Val}

theorem mk1 {a : Expr} {va : Val} {ca : ℕ} (ha : Det P env a va ca) :
    Det P env (GI.Lang.mk1 a) (.list [va]) (ca + (Val.list [va]).wt + 6) :=
  (Det.snoc Det.nil ha).mono (by simp; omega)

theorem mk2 {a b : Expr} {va vb : Val} {ca cb : ℕ} (ha : Det P env a va ca)
    (hb : Det P env b vb cb) :
    Det P env (GI.Lang.mk2 a b) (.list [va, vb]) (ca + cb + 2 * (Val.list [va, vb]).wt + 7) := by
  have h1 := wt_list_mono (show [va] <+: [va, vb] from ⟨[vb], rfl⟩)
  exact (Det.snoc (mk1 ha) hb).mono (by simp only [List.cons_append, List.nil_append]; omega)

theorem mk3 {a b c : Expr} {va vb vc : Val} {ca cb cc : ℕ} (ha : Det P env a va ca)
    (hb : Det P env b vb cb) (hc : Det P env c vc cc) :
    Det P env (GI.Lang.mk3 a b c) (.list [va, vb, vc])
      (ca + cb + cc + 3 * (Val.list [va, vb, vc]).wt + 8) := by
  have h1 := wt_list_mono (show [va, vb] <+: [va, vb, vc] from ⟨[vc], rfl⟩)
  exact (Det.snoc (mk2 ha hb) hc).mono (by simp only [List.cons_append, List.nil_append]; omega)

theorem mk4 {a b c d : Expr} {va vb vc vd : Val} {ca cb cc cd : ℕ} (ha : Det P env a va ca)
    (hb : Det P env b vb cb) (hc : Det P env c vc cc) (hd : Det P env d vd cd) :
    Det P env (GI.Lang.mk4 a b c d) (.list [va, vb, vc, vd])
      (ca + cb + cc + cd + 4 * (Val.list [va, vb, vc, vd]).wt + 9) := by
  have h1 := wt_list_mono (show [va, vb, vc] <+: [va, vb, vc, vd] from ⟨[vd], rfl⟩)
  exact (Det.snoc (mk3 ha hb hc) hd).mono (by simp only [List.cons_append, List.nil_append]; omega)

end Det

/-- Adding a value with any specification at the end of a known list. -/
theorem EvalAll.snoc_det {P : Program} {env : List Val} {l e : Expr} {vs : List Val} {ca : ℕ}
    {Rb : Val → ℕ → Prop} (ha : Det P env l (.list vs) ca) (hb : EvalAll P env e Rb) :
    EvalAll P env (.snoc l e) (fun v c => ∃ w cb, Rb w cb ∧ v = .list (vs ++ [w]) ∧
      c ≤ ca + cb + (Val.list (vs ++ [w])).wt + 1) :=
  .snoc ha hb fun _ _ w cb h1 h2 => by
    obtain ⟨rfl, h1⟩ := h1
    exact ⟨vs, rfl, w, cb, h2, rfl, by omega⟩

/-- The list `[a, b, c, d]` where only `d` may have several results. -/
theorem EvalAll.mk4_last {P : Program} {env : List Val} {a b c d : Expr} {va vb vc : Val}
    {ca cb cc : ℕ} {Rd : Val → ℕ → Prop} (ha : Det P env a va ca) (hb : Det P env b vb cb)
    (hc : Det P env c vc cc) (hd : EvalAll P env d Rd) :
    EvalAll P env (mk4 a b c d) (fun v cost => ∃ vd cd, Rd vd cd ∧ v = .list [va, vb, vc, vd] ∧
      cost ≤ ca + cb + cc + cd + 4 * (Val.list [va, vb, vc, vd]).wt + 9) := by
  refine (EvalAll.snoc_det (Det.mk3 ha hb hc) hd).mono ?_
  rintro v cost ⟨w, cd, h1, rfl, h2⟩
  refine ⟨w, cd, h1, rfl, ?_⟩
  have := wt_list_mono (show [va, vb, vc] <+: [va, vb, vc, w] from ⟨[w], rfl⟩)
  simp only [List.cons_append, List.nil_append] at *
  omega

/-- The list `[a, b]` where only `b` may have several results. -/
theorem EvalAll.mk2_last {P : Program} {env : List Val} {a b : Expr} {va : Val}
    {ca : ℕ} {Rb : Val → ℕ → Prop} (ha : Det P env a va ca) (hb : EvalAll P env b Rb) :
    EvalAll P env (mk2 a b) (fun v cost => ∃ vb cb, Rb vb cb ∧ v = .list [va, vb] ∧
      cost ≤ ca + cb + 2 * (Val.list [va, vb]).wt + 7) := by
  refine (EvalAll.snoc_det (Det.mk1 ha) hb).mono ?_
  rintro v cost ⟨w, cd, h1, rfl, h2⟩
  refine ⟨w, cd, h1, rfl, ?_⟩
  have := wt_list_mono (show [va] <+: [va, w] from ⟨[w], rfl⟩)
  simp only [List.cons_append, List.nil_append] at *
  omega

/-- Reading entry `j` of the argument, when it is known to be `v`. -/
theorem Det.arg' {P : Program} {vs : List Val} {rest : List Val} {j : ℕ} {v : Val}
    (hj : vs[j]? = some v) : Det P (.list vs :: rest) (GI.Lang.arg j) v (2 * (Val.list vs).wt + j + 5) := by
  obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.mp hj
  exact Det.arg h

/-- An operation on numbers whose value is known, with its weight bounded by the value. -/
theorem Det.arith' {P : Program} {env : List Val} {op : BinOp} {a b : Expr} {x y z ca cb : ℕ}
    (ha : Det P env a (.nat x) ca) (hb : Det P env b (.nat y) cb) (hz : op.eval x y = z) :
    Det P env (.arith op a b) (.nat z) (ca + cb + z + 3) := by
  subst hz
  exact (Det.arith ha hb).mono (by have := wt_nat_le (op.eval x y); omega)

/-- Indexing, when the entry is known. -/
theorem Det.get' {P : Program} {env : List Val} {l i : Expr} {vs : List Val} {x ca cb : ℕ}
    {v : Val} (ha : Det P env l (.list vs) ca) (hb : Det P env i (.nat x) cb)
    (hv : vs[x]? = some v) : Det P env (.get l i) v (ca + cb + v.wt + 1) := by
  obtain ⟨hx, rfl⟩ := List.getElem?_eq_some_iff.mp hv
  exact Det.get ha hb hx

/-- Sums over the positions of a list. -/
theorem sum_range_getD {α : Type} (xs : List α) (d : α) (f : α → ℕ) :
    ∑ i ∈ Finset.range xs.length, f (xs.getD i d) = (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, ← ih]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    omega

/-- `if` on a known number, with the value written as an `if`. -/
theorem Det.ite' {P : Program} {env : List Val} {c t e : Expr} {x : ℕ} {v1 v0 : Val}
    {cc ct ce : ℕ} (hc : Det P env c (.nat x) cc) (ht : Det P env t v1 ct)
    (he : Det P env e v0 ce) :
    Det P env (.ite c t e) (if x = 0 then v0 else v1) (cc + max ct ce + max v1.wt v0.wt + 1) := by
  by_cases hx : x = 0
  · subst hx; rw [if_pos rfl]; exact (Det.ite_zero hc he).mono (by omega)
  · rw [if_neg hx]; exact (Det.ite_pos hc hx ht).mono (by omega)

/-- A Boolean as a number: 1 or 0. -/
abbrev boolVal (b : Bool) : Val := .nat b.toNat

theorem wt_boolVal_le (b : Bool) : (boolVal b).wt ≤ 3 := by
  cases b <;> simp [boolVal, wt_nat, GI.Machine.len_zero]

/-- Adding one entry to a list adds at most twice its weight plus 2. -/
theorem wt_list_snoc_le (l : List Val) (x : Val) :
    (Val.list (l ++ [x])).wt ≤ (Val.list l).wt + 2 * x.wt + 2 := by
  rw [wt_list_eq, wt_list_eq]
  simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, List.length_append, List.length_cons, List.length_nil]
  have h1 := GI.Machine.len_succ_le l.length
  have h2 := GI.Machine.len_add_le_add (l.map Val.size).sum x.size
  have h3 := len_le_self x.size
  have h4 := x.size_le_wt
  simp only [Nat.zero_add, Nat.add_zero] at *
  omega

theorem Program.HasAt.left {P : Program} {b : ℕ} {A B : List Expr} (h : P.HasAt b (A ++ B)) :
    P.HasAt b A := fun j hj => by
  have := h j (by simp; omega)
  rwa [List.getElem_append_left hj] at this

theorem Program.HasAt.right {P : Program} {b : ℕ} {A B : List Expr} (h : P.HasAt b (A ++ B)) :
    P.HasAt (b + A.length) B := fun j hj => by
  have := h (A.length + j) (by simp; omega)
  rw [List.getElem_append_right (by omega)] at this
  simpa [Nat.add_assoc] using this

theorem Program.HasAt.single {P : Program} {b : ℕ} {e : Expr} (h : P.HasAt b [e]) :
    P.funs[b]? = some e := by simpa using h 0 (by simp)

/-- A list of `n` values that are related entrywise to `l.map f`, by a relation that fixes the
value on each `f a`, is `l.map g`. -/
theorem forall₂_map_eq {α : Type} {R : Val → Val → Prop} {l : List α} {f g : α → Val}
    {ws : List Val} (hR : ∀ a ∈ l, ∀ w, R (f a) w → w = g a) (h : List.Forall₂ R (l.map f) ws) :
    ws = l.map g := by
  induction l generalizing ws with
  | nil => simpa using h
  | cons a l ih =>
    rw [List.map_cons] at h
    obtain ⟨w, ws', hw, hws', rfl⟩ := List.forall₂_cons_left_iff.mp h
    rw [List.map_cons, hR a (by simp) w hw, ih (fun a ha => hR a (by simp [ha])) hws']

end GI.Lang
