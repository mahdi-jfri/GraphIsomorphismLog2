/-
Folds and iteration: `foldl g` over a list, `iterate g` a given number of times, and the
functional update `set` of a list.

The user function `g` of `foldl` takes `[c, acc, x]`; that of `iterate` takes `[c, i, acc]`.
Both may be nondeterministic: they are described by an invariant `Inv i acc` that bounds the
weight of the accumulators by `M`. The cost is the sum of the bounds `B i` of the calls plus
`loopModK * (n + 1) * (a.wt + n + M + 1)`.
-/
module

public import Workspace.Lang.Lib.Search

@[expose] public section

namespace GI.Lang

open GI.Machine (BinOp len len_le_self)
open GI.Cited (Val)

/-! ### Foldl -/

/-- The step of `foldl g`: `acc := g [c, acc, xs[i]]`. -/
def foldlStep (g : ℕ) : Expr := .call g (mk3 ctxE (arg 2) elemE)

/-- `foldl g`, at base `b`: on `[c, xs, acc0]`, fold `g` over `xs` from `acc0`. -/
def foldlFuns (b g : ℕ) : List Expr :=
  loopFuns b (.length (.get (.var 0) (.nat 1))) (.get (.var 0) (.nat 2)) (foldlStep g)

/-- **Foldl.** If `g [c, acc, xs[i]]` keeps the invariant at cost at most `B i`, then `foldl g`
on `[c, xs, acc0]` ends with an accumulator with `Inv n`. -/
theorem foldl_spec {P : Program} {b g : ℕ} (h : P.HasAt b (foldlFuns b g)) {c : Val}
    {xs : List Val} {acc0 : Val} {Inv : ℕ → Val → Prop} {M : ℕ} {B : ℕ → ℕ}
    (h0 : Inv 0 acc0) (hM : ∀ i acc, i ≤ xs.length → Inv i acc → acc.wt ≤ M)
    (hg : ∀ i acc (hi : i < xs.length), Inv i acc →
      FunAll P g (.list [c, acc, xs[i]]) (fun w cost => Inv (i + 1) w ∧ cost ≤ B i)) :
    FunAll P b (.list [c, .list xs, acc0]) (fun w cost => Inv xs.length w ∧
      cost ≤ ∑ i ∈ Finset.range xs.length, B i +
        loopModK * (xs.length + 1) * ((Val.list [c, .list xs, acc0]).wt + xs.length + M + 1)) := by
  set a := Val.list [c, .list xs, acc0] with ha
  have ha' : (Val.list [c, .list xs, acc0]).wt = a.wt := rfl
  have hk := Det.length (P := P) (env := [a]) (Det.get' (Det.var' (i := 0) rfl) (Det.nat 1)
    (show [c, Val.list xs, acc0][1]? = some (.list xs) from rfl))
  have hacc := Det.get' (P := P) (env := [a]) (Det.var' (i := 0) rfl) (Det.nat 2)
    (show [c, Val.list xs, acc0][2]? = some acc0 from rfl)
  have hxa : (Val.list xs).wt < a.wt := wt_le_wt_list (by simp)
  have h0a : acc0.wt < a.wt := wt_le_wt_list (by simp)
  have hnx := length_lt_wt_list xs
  refine loopBdd_spec h hk hacc (by omega) h0 hM fun i acc hi hinv => ?_
  obtain ⟨hW, hca, hxi, -, -, h2⟩ := step_wt_facts c xs [acc0] i acc hi
  have hacc' := hM i acc hi.le hinv
  have h3 := wt_list3_le c acc xs[i]
  have hm : (Val.list [.list [c, .list xs, acc0], .nat i, acc]).wt =
    (Val.list [a, .nat i, acc]).wt := rfl
  refine EvalAll.call_funAll (Det.mk3 Det.ctxE (Det.arg' (j := 2) rfl) (Det.elemE hi))
    fun v ca hv => ?_
  obtain ⟨rfl, hca'⟩ := hv
  refine ((hg i acc hi hinv).wt_lt).mono fun w cb hw => ⟨hw.1.1, ?_⟩
  have := hM (i + 1) w hi hw.1.1
  omega

/-- **Foldl with a function.** If `g` computes `G acc x`, then `foldl g` computes
`xs.foldl G acc0`. Here `M` bounds the weights of the partial folds. -/
theorem foldl_spec_fun {P : Program} {b g : ℕ} (h : P.HasAt b (foldlFuns b g)) {c : Val}
    {xs : List Val} {acc0 : Val} {G : Val → Val → Val} {M : ℕ} {B : ℕ → ℕ}
    (hM : ∀ i ≤ xs.length, ((xs.take i).foldl G acc0).wt ≤ M)
    (hg : ∀ i (hi : i < xs.length), FunDet P g (.list [c, (xs.take i).foldl G acc0, xs[i]])
      (G ((xs.take i).foldl G acc0) xs[i]) (B i)) :
    FunDet P b (.list [c, .list xs, acc0]) (xs.foldl G acc0)
      (∑ i ∈ Finset.range xs.length, B i +
        loopModK * (xs.length + 1) * ((Val.list [c, .list xs, acc0]).wt + xs.length + M + 1)) := by
  refine (foldl_spec h (acc0 := acc0) (B := B) (Inv := fun i acc => acc = (xs.take i).foldl G acc0)
    (by simp)
    (fun i acc hi h => h ▸ hM i hi) fun i acc hi hacc => ?_).mono fun w cost hw => ?_
  · subst hacc
    refine FunAll.mono (hg i hi) fun w cost hw => ⟨?_, hw.2⟩
    beta_reduce
    rw [hw.1, List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some,
      List.foldl_append]
    rfl
  · rw [List.take_length] at hw
    exact hw

/-! ### Iterate -/

/-- The step of `iterate g`: `acc := g [c, i, acc]`. -/
def iterStep (g : ℕ) : Expr := .call g (mk3 (.get (arg 0) (.nat 0)) (arg 1) (arg 2))

/-- `iterate g`, at base `b`: on `[c, k, acc0]`, run `acc := g [c, i, acc]` for `i < k`. -/
def iterFuns (b g : ℕ) : List Expr :=
  loopFuns b (.get (.var 0) (.nat 1)) (.get (.var 0) (.nat 2)) (iterStep g)

/-- **Iterate.** -/
theorem iter_spec {P : Program} {b g : ℕ} (h : P.HasAt b (iterFuns b g)) {c : Val} {k : ℕ}
    {acc0 : Val} {Inv : ℕ → Val → Prop} {M : ℕ} {B : ℕ → ℕ}
    (h0 : Inv 0 acc0) (hM : ∀ i acc, i ≤ k → Inv i acc → acc.wt ≤ M)
    (hg : ∀ i acc, i < k → Inv i acc →
      FunAll P g (.list [c, .nat i, acc]) (fun w cost => Inv (i + 1) w ∧ cost ≤ B i)) :
    FunAll P b (.list [c, .nat k, acc0]) (fun w cost => Inv k w ∧
      cost ≤ ∑ i ∈ Finset.range k, B i +
        loopModK * (k + 1) * ((Val.list [c, .nat k, acc0]).wt + k + M + 1)) := by
  set a := Val.list [c, .nat k, acc0] with ha
  have ha' : (Val.list [c, .nat k, acc0]).wt = a.wt := rfl
  have hk := Det.get' (P := P) (env := [a]) (Det.var' (i := 0) rfl) (Det.nat 1)
    (show [c, Val.nat k, acc0][1]? = some (.nat k) from rfl)
  have hacc := Det.get' (P := P) (env := [a]) (Det.var' (i := 0) rfl) (Det.nat 2)
    (show [c, Val.nat k, acc0][2]? = some acc0 from rfl)
  have hka : (Val.nat k).wt < a.wt := wt_le_wt_list (by simp)
  have hca : c.wt < a.wt := wt_le_wt_list (by simp)
  have h0a : acc0.wt < a.wt := wt_le_wt_list (by simp)
  have h2 := a.two_le_size
  have h2' := a.size_le_wt
  refine loopBdd_spec h hk hacc (by omega) h0 hM fun i acc hi hinv => ?_
  have hW := wt_stepArg_le a i acc
  have hacc' := hM i acc hi.le hinv
  have h3 := wt_list3_le c (.nat i) acc
  have := wt_nat_le i
  refine EvalAll.call_funAll (Det.mk3 (Det.get' (Det.arg' (j := 0) rfl) (Det.nat 0)
    (show [c, Val.nat k, acc0][0]? = some c from rfl)) (Det.arg' (j := 1) rfl)
    (Det.arg' (j := 2) rfl)) fun v ca hv => ?_
  obtain ⟨rfl, hca'⟩ := hv
  refine ((hg i acc hi hinv).wt_lt).mono fun w cb hw => ⟨hw.1.1, ?_⟩
  have := hM (i + 1) w hi hw.1.1
  omega

/-! ### Functional update -/

/-- The step of `set`: entry `i` of the result is `v` if `i = j`, else `xs[i]`. -/
def setStep : Expr :=
  .snoc (arg 2) (.ite (.arith .eq (arg 1) (.get (arg 0) (.nat 1))) (.get (arg 0) (.nat 2))
    (.get (.get (arg 0) (.nat 0)) (arg 1)))

/-- `set`, at base `b`: on `[xs, j, v]`, the list `xs` with entry `j` replaced by `v`. -/
def setFuns (b : ℕ) : List Expr := loopFuns b (.length (.get (.var 0) (.nat 0))) .nil setStep

/-- **Functional update.** -/
theorem set_spec {P : Program} {b : ℕ} (h : P.HasAt b (setFuns b)) (xs : List Val) (j : ℕ)
    (v : Val) :
    FunDet P b (.list [.list xs, .nat j, v]) (.list (xs.set j v))
      (loopModK * (xs.length + 1) *
        ((Val.list [.list xs, .nat j, v]).wt + xs.length + (Val.list (xs.set j v)).wt + 1)) := by
  set a := Val.list [.list xs, .nat j, v] with ha
  have ha' : (Val.list [.list xs, .nat j, v]).wt = a.wt := rfl
  have hk := Det.length (P := P) (env := [a]) (Det.get' (Det.var' (i := 0) rfl) (Det.nat 0)
    (show [Val.list xs, .nat j, v][0]? = some (.list xs) from rfl))
  have hxa : (Val.list xs).wt < a.wt := wt_le_wt_list (by simp)
  have hva : v.wt < a.wt := wt_le_wt_list (by simp)
  have hja : (Val.nat j).wt < a.wt := wt_le_wt_list (by simp)
  have hnx := length_lt_wt_list xs
  have hlen : (xs.set j v).length = xs.length := List.length_set ..
  refine (loopMono_spec h hk Det.nil (by omega) (by simp)
    (Inv := fun i acc => acc = .list ((xs.set j v).take i)) (by simp) (D := fun _ => 0) ?_).mono ?_
  · rintro i acc hi rfl
    have hW := wt_stepArg_le a i (.list ((xs.set j v).take i))
    have hxi := wt_getElem_lt xs i hi
    have hi' : i < (xs.set j v).length := hlen ▸ hi
    have hval : (xs.set j v)[i] = if j = i then v else xs[i] := List.getElem_set hi'
    have hc := Det.arith' (P := P) (env := [.list [a, .nat i, .list ((xs.set j v).take i)]])
      (op := .eq) (Det.arg' (j := 1) rfl) (Det.get' (Det.arg' (j := 0) rfl) (Det.nat 1)
        (show [Val.list xs, .nat j, v][1]? = some (.nat j) from rfl)) rfl
    have hite := Det.ite' hc (Det.get' (Det.arg' (j := 0) rfl) (Det.nat 2)
        (show [Val.list xs, .nat j, v][2]? = some v from rfl))
      (Det.get' (Det.get' (Det.arg' (j := 0) rfl) (Det.nat 0)
        (show [Val.list xs, .nat j, v][0]? = some (.list xs) from rfl)) (Det.arg' (j := 1) rfl)
        (List.getElem?_eq_getElem hi))
    have hv : (if BinOp.eval .eq i j = 0 then xs[i] else v) = (xs.set j v)[i] := by
      rw [hval]; simp only [BinOp.eval]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Ne.symm hij]
    rw [hv] at hite
    have htake : (xs.set j v).take (i + 1) = (xs.set j v).take i ++ [(xs.set j v)[i]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi']; rfl
    refine (Det.snoc (Det.arg' (j := 2) rfl) hite).post fun cost hc =>
      ⟨by beta_reduce; rw [htake], wt_list_mono (List.prefix_append _ _), ?_⟩
    · have h1 := wt_list_mono (List.prefix_append ((xs.set j v).take i) [(xs.set j v)[i]])
      have h2 : (xs.set j v)[i].wt < (Val.list ((xs.set j v).take i ++ [(xs.set j v)[i]])).wt :=
        wt_le_wt_list (List.mem_append_right _ (List.mem_singleton_self _))
      have h3 : BinOp.eval .eq i j ≤ 1 := by simp only [BinOp.eval]; split_ifs <;> omega
      omega
  · rintro w cost ⟨rfl, hc⟩
    have ht : (xs.set j v).take xs.length = xs.set j v := List.take_of_length_le (by rw [hlen])
    simp only [ht, Finset.sum_const_zero, Nat.zero_add] at hc
    exact ⟨congrArg Val.list ht, hc⟩

end GI.Lang
