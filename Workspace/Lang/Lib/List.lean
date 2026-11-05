/-
List combinators, each a loop module (`loopFuns`) of three functions at a base index `b`.

Each specification gives the result in terms of Lean lists, and a cost bound of the form
"the sum of the costs of the calls of the user function, plus `C * (n + 1) * (a.wt + w.wt + 1)`",
where `n` is the number of steps, `a` the argument and `w` the result. A user function is
described by `FunAll` on each element; its cost bound `B x` may depend on the element.
-/
module

public import Workspace.Lang.Lib.Loop
public import Mathlib.Data.List.Forall2

@[expose] public section

namespace GI.Lang

open GI.Machine (BinOp len len_le_self)
open GI.Cited (Val)

/-! ### Map -/

/-- The step of `map`: with `a = [c, xs]`, add `f [c, xs[i]]` to the accumulator. -/
def mapStep (f : ℕ) : Expr :=
  .snoc (arg 2) (.call f (mk2 (.get (arg 0) (.nat 0)) (.get (.get (arg 0) (.nat 1)) (arg 1))))

/-- `map f`, at base `b`: on `[c, xs]`, the list of `f [c, x]` for `x` in `xs`. -/
def mapFuns (b f : ℕ) : List Expr :=
  loopFuns b (.length (.get (.var 0) (.nat 1))) .nil (mapStep f)

/-- The constant of the cost bound of `map`. -/
def mapK : ℕ := 1000

/-- **Map.** If `f` on `[c, x]` gives a result related to `x` by `R`, at cost at most `B x`,
for every `x` in `xs`, then `map f` on `[c, xs]` gives a list related to `xs` entrywise by
`R`. Its cost is at most `∑ B x` plus `mapK * (n + 1) * (a.wt + w.wt + 1)`. -/
theorem map_spec {P : Program} {b f : ℕ} (h : P.HasAt b (mapFuns b f)) {c : Val}
    {xs : List Val} {R : Val → Val → Prop} {B : Val → ℕ}
    (hf : ∀ x ∈ xs, FunAll P f (.list [c, x]) (fun w cost => R x w ∧ cost ≤ B x)) :
    FunAll P b (.list [c, .list xs]) (fun w cost => ∃ ws, w = .list ws ∧ List.Forall₂ R xs ws ∧
      cost ≤ (xs.map B).sum +
        mapK * (xs.length + 1) * ((Val.list [c, .list xs]).wt + w.wt + 1)) := by
  set a := Val.list [c, .list xs] with ha
  have hk : Det P [a] (.length (.get (.var 0) (.nat 1))) (.nat xs.length) _ :=
    Det.length (Det.get' (Det.var' rfl) (Det.nat 1) rfl)
  have hca : c.wt < a.wt := wt_le_wt_list (by simp)
  have hxa : (Val.list xs).wt < a.wt := wt_le_wt_list (by simp)
  have hnx := length_lt_wt_list xs
  refine (loopFuns_spec h hk Det.nil
    (Inv := fun i acc => ∃ ws, acc = .list ws ∧ List.Forall₂ R (xs.take i) ws)
    (Step := fun i acc acc' cb => acc.wt ≤ acc'.wt ∧
      cb ≤ B (xs.getD i (.nat 0)) + 100 * (a.wt + 1) + 100 * acc'.wt)
    ⟨[], rfl, by simp⟩ ?_).mono ?_
  · rintro i acc hi ⟨ws, rfl, hws⟩
    have hx : xs[i]? = some xs[i] := List.getElem?_eq_getElem hi
    have hxi : xs[i].wt < (Val.list xs).wt := wt_getElem_lt xs i hi
    have hc := Det.get' (P := P) (Det.arg' (rest := []) (vs := [a, .nat i, .list ws]) (j := 0) rfl) (Det.nat 0)
      (show [c, Val.list xs][0]? = some c from rfl)
    have hxv := Det.get' (P := P) (Det.get' (Det.arg' (rest := []) (vs := [a, .nat i, .list ws]) (j := 0) rfl)
      (Det.nat 1) (show [c, Val.list xs][1]? = some (.list xs) from rfl))
      (Det.arg' (rest := []) (vs := [a, .nat i, .list ws]) (j := 1) rfl) hx
    obtain ⟨CA, hCA, hCAle⟩ : ∃ CA, Det P [.list [a, .nat i, .list ws]]
        (mk2 (.get (arg 0) (.nat 0)) (.get (.get (arg 0) (.nat 1)) (arg 1)))
        (.list [c, xs[i]]) CA ∧ CA ≤ 8 * (Val.list [a, .nat i, .list ws]).wt + 3 * a.wt +
          2 * (Val.list [c, xs[i]]).wt + 40 := ⟨_, Det.mk2 hc hxv, by omega⟩
    have hcall := EvalAll.call_funAll (f := f) hCA
      (Q := fun w cw => R xs[i] w ∧ cw ≤ CA + B xs[i] + w.wt + 1) fun v ca hv => by
        obtain ⟨rfl, hca⟩ := hv
        exact (hf _ (List.getElem_mem hi)).mono fun w cb hw => ⟨hw.1, by omega⟩
    refine (EvalAll.snoc_det (Det.arg' (rest := []) (vs := [a, .nat i, .list ws]) (j := 2) rfl) hcall).mono ?_
    rintro v cv ⟨w, cw, ⟨hR, hcw⟩, rfl, hcv⟩
    have hpre := wt_list_mono (show ws <+: ws ++ [w] from List.prefix_append _ _)
    have hw : w.wt < (Val.list (ws ++ [w])).wt := wt_le_wt_list (by simp)
    have hW := wt_list3_le a (.nat i) (.list ws)
    have := wt_nat_le i
    have hcx := wt_list2_le c xs[i]
    have hgetD : xs.getD i (.nat 0) = xs[i] := by simp [hx]
    refine ⟨⟨ws ++ [w], rfl, ?_⟩, hpre, ?_⟩
    · rw [List.take_add_one, hx]
      exact List.rel_append hws (List.Forall₂.cons hR List.Forall₂.nil)
    · rw [hgetD]; omega
  · rintro w cost ⟨cl, hl, hcost⟩
    obtain ⟨⟨ws, rfl, hws⟩, hcl⟩ := hl.le_mono (fun i a a' cb _ _ hs => hs)
    rw [List.take_length] at hws
    refine ⟨ws, rfl, hws, ?_⟩
    rw [sum_range_getD] at hcl
    have h4 := wt_list4_le a (.nat xs.length) (.nat 0) (.list [])
    have := wt_nat_le xs.length
    have hb := collect_bound (k := xs.length) (X := a.wt + (Val.list ws).wt + 1)
      (Y := 100 * (a.wt + 1) + 100 * (Val.list ws).wt + loopK * (a.wt + xs.length +
        (Val.list ws).wt + 1)) (K := 900) (K' := 100) (Z := 100 * (a.wt + (Val.list ws).wt + 1))
      (by simp only [loopK]; omega) (by omega)
    have hj : (Val.list [c, .list xs]).wt = a.wt := rfl
    have := wt_nat_le 0
    simp only [show (900 : ℕ) + 100 = mapK from rfl] at hb
    simp only [wt_list_nil] at h4
    omega

end GI.Lang

namespace GI.Lang

open GI.Machine (BinOp len len_le_self)
open GI.Cited (Val)

/-! ### Range -/

/-- `range`, at base `b`: on `n`, the list `[0, …, n - 1]`. -/
def rangeFuns (b : ℕ) : List Expr := loopFuns b (.var 0) .nil (.snoc (arg 2) (arg 1))

/-- The value of a list of numbers. -/
def natList (l : List ℕ) : Val := .list (l.map .nat)

/-- **Range.** `range` on `n` gives `[0, …, n - 1]`. -/
theorem range_spec {P : Program} {b : ℕ} (h : P.HasAt b (rangeFuns b)) (n : ℕ) :
    FunAll P b (.nat n) (fun w cost => w = natList (List.range n) ∧
      cost ≤ loopModK * (n + 1) * ((Val.nat n).wt + n + w.wt + 1)) := by
  have hk : Det P [.nat n] (.var 0) (.nat n) _ := Det.var' rfl
  refine (loopMono_spec h hk Det.nil (by have := wt_nat_le n; omega) (by simp)
    (Inv := fun i acc => acc = natList (List.range i)) rfl (D := fun _ => 0) ?_).mono ?_
  · rintro i acc hi rfl
    refine (Det.snoc (Det.arg' (rest := []) (vs := [.nat n, .nat i, natList (List.range i)]) (j := 2) rfl)
      (Det.arg' (rest := []) (vs := [.nat n, .nat i, natList (List.range i)]) (j := 1) rfl)).post
      fun c hc => ?_
    have hr : natList (List.range (i + 1)) = .list ((List.range i).map .nat ++ [.nat i]) := by
      simp [natList, List.range_succ]
    refine ⟨hr.symm, ?_, ?_⟩
    · rw [← hr]; exact wt_list_mono (by simp [List.range_succ])
    · have := wt_stepArg_le (.nat n) i (natList (List.range i))
      have h1 := wt_list_mono (show (List.range i).map Val.nat <+: (List.range i).map .nat ++
        [.nat i] from List.prefix_append _ _)
      have h2 : (Val.nat i).wt < (Val.list ((List.range i).map .nat ++ [.nat i])).wt :=
        wt_le_wt_list (by simp)
      simp only [natList] at *
      omega
  · rintro w cost ⟨rfl, hc⟩
    simpa using hc

/-! ### Replicate -/

/-- `replicate`, at base `b`: on `[n, v]`, the list of `n` copies of `v`. -/
def replicateFuns (b : ℕ) : List Expr :=
  loopFuns b (.get (.var 0) (.nat 0)) .nil (.snoc (arg 2) (.get (arg 0) (.nat 1)))

/-- **Replicate.** -/
theorem replicate_spec {P : Program} {b : ℕ} (h : P.HasAt b (replicateFuns b)) (n : ℕ)
    (v : Val) :
    FunAll P b (.list [.nat n, v]) (fun w cost => w = .list (List.replicate n v) ∧
      cost ≤ loopModK * (n + 1) * ((Val.list [.nat n, v]).wt + n + w.wt + 1)) := by
  set a := Val.list [.nat n, v]
  have ha' : (Val.list [.nat n, v]).wt = a.wt := rfl
  have hk : Det P [a] (.get (.var 0) (.nat 0)) (.nat n) _ := Det.get' (Det.var' rfl) (Det.nat 0) rfl
  have hva : v.wt < a.wt := wt_le_wt_list (by simp)
  have hna : (Val.nat n).wt < a.wt := wt_le_wt_list (by simp)
  refine (loopMono_spec h hk Det.nil (by have := wt_nat_le n; omega) (by simp)
    (Inv := fun i acc => acc = .list (List.replicate i v)) rfl (D := fun _ => 0) ?_).mono ?_
  · rintro i acc hi rfl
    refine (Det.snoc (Det.arg' (rest := []) (vs := [a, .nat i, .list (List.replicate i v)]) (j := 2) rfl)
      (Det.get' (Det.arg' (rest := []) (vs := [a, .nat i, .list (List.replicate i v)]) (j := 0) rfl)
        (Det.nat 1) (show [Val.nat n, v][1]? = some v from rfl))).post fun c hc => ?_
    have hr : List.replicate (i + 1) v = List.replicate i v ++ [v] := List.replicate_succ' ..
    refine ⟨by beta_reduce; rw [hr], wt_list_mono (List.prefix_append _ _), ?_⟩
    · have := wt_stepArg_le a i (.list (List.replicate i v))
      have h1 := wt_list_mono (List.prefix_append (List.replicate i v) [v])
      omega
  · rintro w cost ⟨rfl, hc⟩
    simpa using hc

/-! ### Append -/

/-- `append`, at base `b`: on `[xs, ys]`, the list `xs ++ ys`. -/
def appendFuns (b : ℕ) : List Expr :=
  loopFuns b (.length (.get (.var 0) (.nat 1))) (.get (.var 0) (.nat 0))
    (.snoc (arg 2) (.get (.get (arg 0) (.nat 1)) (arg 1)))

/-- **Append.** -/
theorem append_spec {P : Program} {b : ℕ} (h : P.HasAt b (appendFuns b)) (xs ys : List Val) :
    FunAll P b (.list [.list xs, .list ys]) (fun w cost => w = .list (xs ++ ys) ∧
      cost ≤ loopModK * (ys.length + 1) *
        ((Val.list [.list xs, .list ys]).wt + ys.length + w.wt + 1)) := by
  set a := Val.list [.list xs, .list ys]
  have ha' : (Val.list [.list xs, .list ys]).wt = a.wt := rfl
  have hk : Det P [a] (.length (.get (.var 0) (.nat 1))) (.nat ys.length) _ :=
    Det.length (Det.get' (Det.var' rfl) (Det.nat 1) rfl)
  have hacc : Det P [a] (.get (.var 0) (.nat 0)) (.list xs) _ :=
    Det.get' (Det.var' rfl) (Det.nat 0) rfl
  have hxa : (Val.list xs).wt < a.wt := wt_le_wt_list (by simp)
  have hya : (Val.list ys).wt < a.wt := wt_le_wt_list (by simp)
  refine (loopMono_spec h hk hacc (by omega) (by omega)
    (Inv := fun i acc => acc = .list (xs ++ ys.take i)) (by simp) (D := fun _ => 0) ?_).mono ?_
  · rintro i acc hi rfl
    have hy : ys[i]? = some ys[i] := List.getElem?_eq_getElem hi
    refine (Det.snoc (Det.arg' (rest := []) (vs := [a, .nat i, .list (xs ++ ys.take i)]) (j := 2) rfl)
      (Det.get' (Det.get' (Det.arg' (rest := []) (vs := [a, .nat i, .list (xs ++ ys.take i)]) (j := 0) rfl)
        (Det.nat 1) (show [Val.list xs, .list ys][1]? = some (.list ys) from rfl))
        (Det.arg' (rest := []) (vs := [a, .nat i, .list (xs ++ ys.take i)]) (j := 1) rfl) hy)).post
      fun c hc => ?_
    have hr : xs ++ ys.take (i + 1) = xs ++ ys.take i ++ [ys[i]] := by
      rw [List.take_add_one, hy]; simp
    have hyi := wt_getElem_lt ys i hi
    refine ⟨by beta_reduce; rw [hr], wt_list_mono (List.prefix_append _ _), ?_⟩
    · have := wt_stepArg_le a i (.list (xs ++ ys.take i))
      have h1 := wt_list_mono (List.prefix_append (xs ++ ys.take i) [ys[i]])
      omega
  · rintro w cost ⟨rfl, hc⟩
    simpa using hc

end GI.Lang
