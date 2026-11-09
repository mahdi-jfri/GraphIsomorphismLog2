module

public import Workspace.Lang.Lib.Basic

@[expose] public section

/-!
# Passing the degree to every function

The state value has no field for the degree `D`, and the functions of the general algorithm rebuild
child values in a fixed format. Only the case decision reads `D`. So the proofs work with a program
`P` that holds `D` as a number in its text, one program for each `D`. This file turns such programs
into one program `P'` that does not depend on `D`, and takes `D` as an extra input of each function.

`thr e` is the text of `e` where each function gets `[D, v]`. A function body stores `D` and `v` in
the environment (`thrBody`), so that reading `D` costs little. Every entry of the environment moves
up by two, and a call passes `D` on.

`Rel D e e'` says that `e'` is such a text for `e`, where the number `D` in `e` may also become a
read of `D`. `EvalAll.thread` shows that `P'` does what `P` does, at a cost larger by the factor
`threadM D`, which is polynomial in the length of `D`.
-/

namespace GI.Degree

open GI.Lang
open GI.Cited (Val)

/-- The text of `e` with the degree in the environment. -/
def thr : Expr → Expr
  | .var i => .var (i + 2)
  | .nat k => .nat k
  | .arith op a b => .arith op (thr a) (thr b)
  | .nil => .nil
  | .snoc l e => .snoc (thr l) (thr e)
  | .length l => .length (thr l)
  | .get l i => .get (thr l) (thr i)
  | .isNat e => .isNat (thr e)
  | .ite c t e => .ite (thr c) (thr t) (thr e)
  | .letE e b => .letE (thr e) (thr b)
  | .call f a => .call f (.snoc (.snoc .nil (.var 1)) (thr a))
  | .prim j a => .prim j (thr a)

/-- The body of a function that takes `[D, v]`. -/
def thrBody (e : Expr) : Expr :=
  .letE (.get (.var 0) (.nat 0)) (.letE (.get (.var 0) (.nat 1)) e)

/-- `e'` is a text for `e`, with the degree in the environment. -/
inductive Rel (D : ℕ) : Expr → Expr → Prop where
  | var (i) : Rel D (.var i) (.var (i + 2))
  | nat (k) : Rel D (.nat k) (.nat k)
  | degree : Rel D (.nat D) (.var 1)
  | arith (op) {a a' b b'} (ha : Rel D a a') (hb : Rel D b b') :
      Rel D (.arith op a b) (.arith op a' b')
  | nil : Rel D .nil .nil
  | snoc {a a' b b'} (ha : Rel D a a') (hb : Rel D b b') : Rel D (.snoc a b) (.snoc a' b')
  | length {a a'} (ha : Rel D a a') : Rel D (.length a) (.length a')
  | get {a a' b b'} (ha : Rel D a a') (hb : Rel D b b') : Rel D (.get a b) (.get a' b')
  | isNat {a a'} (ha : Rel D a a') : Rel D (.isNat a) (.isNat a')
  | ite {a a' b b' c c'} (ha : Rel D a a') (hb : Rel D b b') (hc : Rel D c c') :
      Rel D (.ite a b c) (.ite a' b' c')
  | letE {a a' b b'} (ha : Rel D a a') (hb : Rel D b b') : Rel D (.letE a b) (.letE a' b')
  | call (f) {a a'} (ha : Rel D a a') : Rel D (.call f a) (.call f (.snoc (.snoc .nil (.var 1)) a'))
  | prim (j) {a a'} (ha : Rel D a a') : Rel D (.prim j a) (.prim j a')

theorem rel_thr (D : ℕ) : ∀ e, Rel D e (thr e)
  | .var i => .var i
  | .nat k => .nat k
  | .arith op a b => .arith op (rel_thr D a) (rel_thr D b)
  | .nil => .nil
  | .snoc l e => .snoc (rel_thr D l) (rel_thr D e)
  | .length l => .length (rel_thr D l)
  | .get l i => .get (rel_thr D l) (rel_thr D i)
  | .isNat e => .isNat (rel_thr D e)
  | .ite c t e => .ite (rel_thr D c) (rel_thr D t) (rel_thr D e)
  | .letE e b => .letE (rel_thr D e) (rel_thr D b)
  | .call f a => .call f (rel_thr D a)
  | .prim j a => .prim j (rel_thr D a)

/-- `P'` is the program `P` with the degree in the environment. -/
structure ProgRel (D : ℕ) (P P' : Program) : Prop where
  prims : P'.prims = P.prims
  funs : ∀ (f : ℕ) (body : Expr), P.funs[f]? = some body →
    ∃ e, Rel D body e ∧ P'.funs[f]? = some (thrBody e)

/-- What a result sets aside for the work on it later. -/
def threadR (D : ℕ) (v : Val) : ℕ := 100 * (v.wt + (Val.nat D).wt + 20)

/-- The factor between the costs. -/
def threadM (D : ℕ) : ℕ := 200 * ((Val.nat D).wt + 30)

/-- The condition of `EvalAll.thread` on a result. -/
def ThreadQ (D : ℕ) (Q : Val → ℕ → Prop) : Val → ℕ → Prop :=
  fun v c' => ∃ c, Q v c ∧ c' + threadR D v ≤ threadM D * c

section

variable {D : ℕ} {P P' : Program}

theorem threadM_local (D w : ℕ) : w + 1 + 3 * (w + 1) +
    100 * (w + (Val.nat D).wt + 20) ≤ threadM D * (w + 1) := by
  unfold threadM
  generalize (Val.nat D).wt = W
  nlinarith

private theorem aux_one {c w W X R : ℕ} (h1 : w + 1 + 3 * (w + 1) + 100 * (w + W + 20) ≤ X)
    (h : c ≤ w + 1) (e : R = 100 * (w + W + 20)) : c + R ≤ X := by omega

private theorem aux_two {a' b' w W Y Z X R T : ℕ} (h1 : w + 1 + 3 * (w + 1) + 100 * (w + W + 20) ≤ X)
    (ha : a' ≤ Y) (hb : b' ≤ Z) (e : R = 100 * (w + W + 20)) (eT : T = Y + Z + X) :
    a' + b' + w + 1 + R ≤ T := by omega

theorem thread_one {D c w : ℕ} {v : Val} (hc : w = v.wt) (h : c ≤ w + 1) :
    c + threadR D v ≤ threadM D * (w + 1) :=
  aux_one (threadM_local D w) h (by rw [threadR, hc])

theorem thread_two {D a b a' b' w : ℕ} {v : Val} (hw : w = v.wt) (ha : a' ≤ threadM D * a)
    (hb : b' ≤ threadM D * b) : a' + b' + w + 1 + threadR D v ≤ threadM D * (a + b + w + 1) :=
  aux_two (threadM_local D w) ha hb (by rw [threadR, hw]) (by ring)

theorem le_of_threadR {D c m : ℕ} {v : Val} (h : c + threadR D v ≤ m) : c ≤ m := by omega

theorem threadM_pos (D : ℕ) : 1 ≤ threadM D := by unfold threadM; omega

/-- The start of a function that takes `[D, v]`. -/
theorem thrBody_all {P : Program} {D : ℕ} {v : Val} {e : Expr} {Q : Val → ℕ → Prop}
    (h : EvalAll P [.list [.nat D, v], .nat D, v] e Q) :
    EvalAll P [.list [.nat D, v]] (thrBody e) fun w c => ∃ c₀, Q w c₀ ∧
      c ≤ c₀ + 2 * (w.wt + 1) + 6 * ((Val.nat D).wt + v.wt) + 40 := by
  set H := Val.list [.nat D, v] with hH
  have hw : H.wt ≤ 2 * ((Val.nat D).wt + v.wt) + 6 := wt_list2_le (.nat D) v
  have w0 : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
  have w1 : (Val.nat 1).wt ≤ 3 := wt_nat_le 1
  refine .letE (Ra := fun x c => x = .nat D ∧ c ≤ H.wt + 1 + (2 + 1) + (Val.nat D).wt + 1)
    (.get (Ra := fun x c => x = H ∧ c = H.wt + 1) (Rb := fun x c => x = .nat 0 ∧ c = (Val.nat 0).wt + 1)
      (.var (by simp) ⟨rfl, rfl⟩) (.nat ⟨rfl, rfl⟩) ?_) ?_
  · rintro _ ca _ cb ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    exact ⟨[.nat D, v], 0, rfl, rfl, by simp, rfl, by simp; omega⟩
  rintro _ c1 ⟨rfl, hc1⟩
  refine .letE (Ra := fun x c => x = v ∧ c ≤ H.wt + 1 + (3 + 1) + v.wt + 1)
    (.get (Ra := fun x c => x = H ∧ c = H.wt + 1) (Rb := fun x c => x = .nat 1 ∧ c = (Val.nat 1).wt + 1)
      (.var (by simp) ⟨rfl, rfl⟩) (.nat ⟨rfl, rfl⟩) ?_) ?_
  · rintro _ ca _ cb ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    exact ⟨[.nat D, v], 1, rfl, rfl, by simp, rfl, by simp; omega⟩
  rintro _ c2 ⟨rfl, hc2⟩
  exact h.mono fun w c hQ => ⟨c, hQ, by omega⟩

private theorem aux_call {ca' c₀ c2 cb w W V Y Z X T c Rv Rw : ℕ}
    (hl : w + 1 + 3 * (w + 1) + 100 * (w + W + 20) ≤ X) (h4 : ca' + Rv ≤ Y) (h7 : c₀ + Rw ≤ Z)
    (h5 : c2 ≤ ca' + 6 * (W + V) + 40) (h8 : c ≤ c₀ + 2 * (w + 1) + 6 * (W + V) + 40)
    (eV : Rv = 100 * (V + W + 20)) (eW : Rw = 100 * (w + W + 20)) (ec : cb = c2 + c + w + 1)
    (eT : T = Y + Z + X) : cb + Rw ≤ T := by omega

/-- **`P'` does what `P` does.** Here the environment of `e'` holds the input `[D, v₀]`, then `D` and
`v₀`, then the rest. -/
theorem EvalAll.thread (hP : ProgRel D P P') {env : List Val} {e : Expr} {Q : Val → ℕ → Prop}
    (h : EvalAll P env e Q) :
    ∀ e', Rel D e e' → ∀ (v₀ : Val) (rest : List Val), env = v₀ :: rest →
      EvalAll P' (.list [.nat D, v₀] :: .nat D :: v₀ :: rest) e' (ThreadQ D Q) := by
  induction h with
  | @var env i Q h hq =>
    intro e' hr v₀ rest henv
    cases hr
    subst henv
    exact .var (by simp at h ⊢; omega) ⟨_, hq, thread_one rfl le_rfl⟩
  | @nat env k Q hq =>
    intro e' hr v₀ rest henv
    cases hr with
    | nat => exact .nat ⟨_, hq, thread_one rfl le_rfl⟩
    | degree => exact .var (by simp) ⟨_, hq, thread_one rfl le_rfl⟩
  | arith ha hb hq iha ihb =>
    intro e' hr v₀ rest henv
    cases hr with
    | arith op h1 h2 =>
      refine .arith (iha _ h1 v₀ rest henv) (ihb _ h2 v₀ rest henv) ?_
      rintro va ca' vb cb' ⟨ca, h3, h4⟩ ⟨cb, h5, h6⟩
      obtain ⟨x, y, rfl, rfl, h7⟩ := hq _ _ _ _ h3 h5
      exact ⟨x, y, rfl, rfl, _, h7, thread_two rfl (le_of_threadR h4) (le_of_threadR h6)⟩
  | nil hq =>
    intro e' hr v₀ rest henv
    cases hr
    exact .nil ⟨_, hq, thread_one rfl le_rfl⟩
  | snoc ha hb hq iha ihb =>
    intro e' hr v₀ rest henv
    cases hr with
    | snoc h1 h2 =>
      refine .snoc (iha _ h1 v₀ rest henv) (ihb _ h2 v₀ rest henv) ?_
      rintro va ca' vb cb' ⟨ca, h3, h4⟩ ⟨cb, h5, h6⟩
      obtain ⟨vs, rfl, h7⟩ := hq _ _ _ _ h3 h5
      exact ⟨vs, rfl, _, h7, thread_two rfl (le_of_threadR h4) (le_of_threadR h6)⟩
  | length ha hq iha =>
    intro e' hr v₀ rest henv
    cases hr with
    | length h1 =>
      refine .length (iha _ h1 v₀ rest henv) ?_
      rintro va ca' ⟨ca, h3, h4⟩
      obtain ⟨vs, rfl, h7⟩ := hq _ _ h3
      exact ⟨vs, rfl, _, h7, by
        simpa using thread_two (b := 0) (b' := 0) rfl (le_of_threadR h4) (by simp)⟩
  | get ha hb hq iha ihb =>
    intro e' hr v₀ rest henv
    cases hr with
    | get h1 h2 =>
      refine .get (iha _ h1 v₀ rest henv) (ihb _ h2 v₀ rest henv) ?_
      rintro va ca' vb cb' ⟨ca, h3, h4⟩ ⟨cb, h5, h6⟩
      obtain ⟨vs, x, rfl, rfl, hx, h7⟩ := hq _ _ _ _ h3 h5
      exact ⟨vs, x, rfl, rfl, hx, _, h7, thread_two rfl (le_of_threadR h4) (le_of_threadR h6)⟩
  | isNat ha hq iha =>
    intro e' hr v₀ rest henv
    cases hr with
    | isNat h1 =>
      refine .isNat (iha _ h1 v₀ rest henv) ?_
      rintro va ca' ⟨ca, h3, h4⟩
      exact ⟨_, hq _ _ h3, by
        simpa using thread_two (b := 0) (b' := 0) rfl (le_of_threadR h4) (by simp)⟩
  | @ite env c t e Q Rc hc hn hb ihc ihb =>
    intro e' hr v₀ rest henv
    cases hr with
    | ite h1 h2 h3 =>
      refine .ite (Rc := ThreadQ D Rc) (ihc _ h1 v₀ rest henv)
        (fun vc cc ⟨c0, h4, _⟩ => hn vc c0 h4) ?_
      rintro x cc' ⟨cc, h4, h5⟩
      have hi := ihb x cc h4
      split_ifs at hi ⊢
      · refine (hi _ h3 v₀ rest henv).mono ?_
        rintro w cb' ⟨cb, h6, h7⟩
        exact ⟨_, h6, thread_two rfl (le_of_threadR h5) (le_of_threadR h7)⟩
      · refine (hi _ h2 v₀ rest henv).mono ?_
        rintro w cb' ⟨cb, h6, h7⟩
        exact ⟨_, h6, thread_two rfl (le_of_threadR h5) (le_of_threadR h7)⟩
  | letE ha hb iha ihb =>
    intro e' hr v₀ rest henv
    cases hr with
    | letE h1 h2 =>
      subst henv
      refine .letE (Ra := ThreadQ D _) (iha _ h1 v₀ rest rfl) ?_
      rintro v ca' ⟨ca, h3, h4⟩
      refine (ihb v ca h3 _ h2 v₀ (rest ++ [v]) rfl).mono ?_
      rintro w cb' ⟨cb, h6, h7⟩
      exact ⟨_, h6, thread_two rfl (le_of_threadR h4) (le_of_threadR h7)⟩
  | @call env f a body Q Ra hf ha hb iha ihb =>
    intro e' hr v₀ rest henv
    cases hr with
    | call f h1 =>
      obtain ⟨e₀, hrel, hf'⟩ := hP.funs _ _ hf
      refine .call (Ra := fun v2 c2 => ∃ v ca ca', Ra v ca ∧ v2 = .list [.nat D, v] ∧
        ca' + threadR D v ≤ threadM D * ca ∧ c2 ≤ ca' + 6 * ((Val.nat D).wt + v.wt) + 40) hf'
        (.snoc (Ra := fun x c => x = .list [.nat D] ∧ c ≤ 3 * (Val.nat D).wt + 20)
          (Rb := ThreadQ D Ra)
          (.snoc (Ra := fun x c => x = .list [] ∧ c = (Val.list []).wt + 1)
            (Rb := fun x c => x = .nat D ∧ c = (Val.nat D).wt + 1) (.nil ⟨rfl, rfl⟩)
            (.var (by simp) ⟨rfl, rfl⟩) ?_) (iha _ h1 v₀ rest henv) ?_) ?_
      · rintro _ ca _ cb ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
        refine ⟨[], rfl, rfl, ?_⟩
        have := wt_list_le [Val.nat D]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
          List.length_nil] at this
        have e0 : (Val.list []).wt = 4 := rfl
        simp only [List.nil_append]
        omega
      · rintro _ c1 v c2 ⟨rfl, hc1⟩ ⟨ca, h3, h4⟩
        refine ⟨[.nat D], rfl, v, ca, c2, h3, rfl, h4, ?_⟩
        have := wt_list2_le (.nat D) v
        simp only [List.cons_append, List.nil_append]
        omega
      · rintro _ c2 ⟨v, ca, ca', h3, rfl, h4, h5⟩
        refine (thrBody_all (ihb v ca h3 _ hrel v [] rfl)).mono ?_
        rintro w cb' ⟨c₀, ⟨cb, h6, h7⟩, h8⟩
        refine ⟨_, h6, ?_⟩
        have hl := threadM_local D w.wt
        have e : threadM D * (ca + cb + w.wt + 1) =
            threadM D * ca + threadM D * cb + threadM D * (w.wt + 1) := by ring
        exact aux_call hl h4 h7 h5 h8 rfl rfl rfl e
  | @prim env j a p Q Ra hj ha hb iha =>
    intro e' hr v₀ rest henv
    cases hr with
    | prim j h1 =>
      refine .prim (p := p) (Ra := ThreadQ D Ra) (by rw [hP.prims]; exact hj)
        (iha _ h1 v₀ rest henv) ?_
      rintro v ca' ⟨ca, h3, h4⟩
      refine ⟨(hb v ca h3).1, fun w hw => ⟨_, (hb v ca h3).2 w hw, ?_⟩⟩
      refine thread_two rfl (le_of_threadR h4) ?_
      exact Nat.le_mul_of_pos_left _ (threadM_pos D)

private theorem aux_body {c₁ c w W V M R : ℕ} (h2 : c₁ + R ≤ M)
    (h3 : c ≤ c₁ + 2 * (w + 1) + 6 * (W + V) + 40) (e : R = 100 * (w + W + 20)) :
    c ≤ M + 6 * (W + V) + 40 := by omega

/-- **The form for calls.** -/
theorem FunAll.thread (hP : ProgRel D P P') {f : ℕ} {v : Val} {Q : Val → ℕ → Prop}
    (h : FunAll P f v Q) :
    FunAll P' f (.list [.nat D, v]) fun w c => ∃ c₀, Q w c₀ ∧
      c ≤ threadM D * c₀ + 6 * ((Val.nat D).wt + v.wt) + 40 := by
  obtain ⟨body, hb, h⟩ := h
  obtain ⟨e₀, hrel, hf'⟩ := hP.funs _ _ hb
  refine ⟨_, hf', (thrBody_all (EvalAll.thread hP h _ hrel v [] rfl)).mono ?_⟩
  rintro w c ⟨c₁, ⟨c₀, h1, h2⟩, h3⟩
  refine ⟨c₀, h1, ?_⟩
  have h5 := aux_body (R := threadR D w) h2 h3 (by rw [threadR])
  exact h5

end

end GI.Degree
