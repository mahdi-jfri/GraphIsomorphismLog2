/-
Loops that test the entries of a list: `filter`, `all`, `any`, `findIdx` (the index of the
first entry that passes a test), and equality of lists of numbers.

A test is a user function `p` that, on `[c, x]`, returns `1` or `0` (`boolVal (q x)` for a
Lean predicate `q : Val → Bool`), at cost at most `B x`. Each combinator takes `[c, xs]`.
-/
import Workspace.Lang.Lib.List

namespace GI.Lang

open GI.Machine (BinOp len len_le_self)
open GI.Cited (Val)

/-! ### Reading the context and the current entry -/

/-- The context `c` of a step argument `[[c, xs], i, acc]`. -/
def ctxE : Expr := .get (arg 0) (.nat 0)

/-- The current entry `xs[i]` of a step argument `[[c, xs], i, acc]`. -/
def elemE : Expr := .get (.get (arg 0) (.nat 1)) (arg 1)

theorem Det.ctxE {P : Program} {rest : List Val} {c : Val} {xs more : List Val} {i : ℕ}
    {acc : Val} :
    Det P (.list [.list (c :: .list xs :: more), .nat i, acc] :: rest) GI.Lang.ctxE c
      (2 * (Val.list [.list (c :: .list xs :: more), .nat i, acc]).wt +
        (Val.list (c :: .list xs :: more)).wt + 9) :=
  (Det.get' (Det.arg' (j := 0) rfl) (Det.nat 0) rfl).mono (by
    have : c.wt < (Val.list (c :: .list xs :: more)).wt := wt_le_wt_list (by simp)
    omega)

theorem Det.elemE {P : Program} {rest : List Val} {c : Val} {xs more : List Val} {i : ℕ}
    {acc : Val} (hi : i < xs.length) :
    Det P (.list [.list (c :: .list xs :: more), .nat i, acc] :: rest) GI.Lang.elemE xs[i]
      (4 * (Val.list [.list (c :: .list xs :: more), .nat i, acc]).wt +
        2 * (Val.list (c :: .list xs :: more)).wt + 17) :=
  (Det.get' (Det.get' (Det.arg' (j := 0) rfl) (Det.nat 1) rfl) (Det.arg' (j := 1) rfl)
    (List.getElem?_eq_getElem hi)).mono (by
    have : (Val.list xs).wt < (Val.list (c :: .list xs :: more)).wt := wt_le_wt_list (by simp)
    have := wt_getElem_lt xs i hi
    omega)

/-- The facts about weights that the step proofs below use. -/
theorem step_wt_facts (c : Val) (xs more : List Val) (i : ℕ) (acc : Val) (hi : i < xs.length) :
    (Val.list [.list (c :: .list xs :: more), .nat i, acc]).wt ≤
        2 * ((Val.list (c :: .list xs :: more)).wt + i + acc.wt) + 11 ∧
      c.wt < (Val.list (c :: .list xs :: more)).wt ∧
      xs[i].wt < (Val.list (c :: .list xs :: more)).wt ∧
      (Val.list [c, xs[i]]).wt ≤ 4 * (Val.list (c :: .list xs :: more)).wt + 6 ∧
      xs.length < (Val.list (c :: .list xs :: more)).wt ∧
      2 ≤ (Val.list (c :: .list xs :: more)).wt := by
  have h1 : c.wt < (Val.list (c :: .list xs :: more)).wt := wt_le_wt_list (by simp)
  have h2 : (Val.list xs).wt < (Val.list (c :: .list xs :: more)).wt := wt_le_wt_list (by simp)
  have h3 := wt_getElem_lt xs i hi
  have h4 := wt_list2_le c xs[i]
  have h5 := length_lt_wt_list xs
  have h6 := (Val.list (c :: .list xs :: more)).two_le_size
  have h7 := (Val.list (c :: .list xs :: more)).size_le_wt
  exact ⟨wt_stepArg_le _ _ _, h1, by omega, by omega, by omega, by omega⟩

/-! ### Filter -/

/-- The step of `filter p`. -/
def filterStep (p : ℕ) : Expr :=
  .letE elemE (.ite (.call p (mk2 ctxE (.var 1))) (.snoc (arg 2) (.var 1)) (arg 2))

/-- `filter p`, at base `b`: on `[c, xs]`, the entries `x` of `xs` that pass `p [c, x]`. -/
def filterFuns (b p : ℕ) : List Expr :=
  loopFuns b (.length (.get (.var 0) (.nat 1))) .nil (filterStep p)

/-- **Filter.** -/
theorem filter_spec {P : Program} {b p : ℕ} (h : P.HasAt b (filterFuns b p)) {c : Val}
    {xs : List Val} {q : Val → Bool} {B : Val → ℕ}
    (hp : ∀ x ∈ xs, FunDet P p (.list [c, x]) (boolVal (q x)) (B x)) :
    FunAll P b (.list [c, .list xs]) (fun w cost => w = .list (xs.filter q) ∧
      cost ≤ (xs.map B).sum +
        loopModK * (xs.length + 1) * ((Val.list [c, .list xs]).wt + xs.length + w.wt + 1)) := by
  have hk : Det P [.list [c, .list xs]] (.length (.get (.var 0) (.nat 1))) (.nat xs.length) _ :=
    Det.length (Det.get' (Det.var' rfl) (Det.nat 1) rfl)
  have hnx := length_lt_wt_list xs
  have hxa : (Val.list xs).wt < (Val.list [c, .list xs]).wt := wt_le_wt_list (by simp)
  refine (loopMono_spec h hk Det.nil (by omega) (by simp)
    (Inv := fun i acc => acc = .list ((xs.take i).filter q))
    (D := fun i => B (xs.getD i (.nat 0))) (by simp) ?_).mono ?_
  · rintro i acc hi rfl
    obtain ⟨hW, hca, hxi, hcx, -, h2⟩ := step_wt_facts c xs [] i (.list ((xs.take i).filter q)) hi
    have hx : xs[i]? = some xs[i] := List.getElem?_eq_getElem hi
    have hbody := Det.ite' (P := P) (env := [.list [.list [c, .list xs], .nat i,
        .list ((xs.take i).filter q)], xs[i]])
      (Det.call (Det.mk2 Det.ctxE (Det.var' (i := 1) rfl)) (hp xs[i] (List.getElem_mem hi)))
      (Det.snoc (Det.arg' (j := 2) rfl) (Det.var' (i := 1) rfl)) (Det.arg' (j := 2) rfl)
    have hv : (if (q xs[i]).toNat = 0 then Val.list ((xs.take i).filter q) else
        .list ((xs.take i).filter q ++ [xs[i]])) = .list ((xs.take (i + 1)).filter q) := by
      rw [List.take_add_one, hx, Option.toList_some, List.filter_append, List.filter_singleton]
      cases hq : q xs[i] <;>
        simp only [cond_true, cond_false, Bool.toNat_true, Bool.toNat_false] <;> simp
    rw [hv] at hbody
    have hpre : (xs.take i).filter q <+: (xs.take (i + 1)).filter q := by
      rw [List.take_add_one, hx, Option.toList_some, List.filter_append]
      exact List.prefix_append _ _
    have h3 := wt_list_mono hpre
    refine (Det.letE (Det.elemE hi) hbody).post fun cost hc => ⟨rfl, h3, ?_⟩
    · have h5 := wt_list_snoc_le ((xs.take i).filter q) xs[i]
      have h4 : (Val.nat (q xs[i]).toNat).wt ≤ 3 := wt_boolVal_le _
      simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]
      omega
  · rintro w cost ⟨rfl, hc⟩
    rw [List.take_length] at *
    rw [sum_range_getD] at hc
    exact ⟨rfl, hc⟩

end GI.Lang

namespace GI.Lang

open GI.Machine (BinOp len len_le_self)
open GI.Cited (Val)

/-! ### All and any -/

/-- The step of `all p`. -/
def allStep (p : ℕ) : Expr :=
  .ite (arg 2) (.ite (.call p (mk2 ctxE elemE)) (.nat 1) (.nat 0)) (.nat 0)

/-- `all p`, at base `b`: on `[c, xs]`, 1 if every entry passes `p`, else 0. -/
def allFuns (b p : ℕ) : List Expr :=
  loopFuns b (.length (.get (.var 0) (.nat 1))) (.nat 1) (allStep p)

/-- The step of `any p`. -/
def anyStep (p : ℕ) : Expr :=
  .ite (arg 2) (.nat 1) (.ite (.call p (mk2 ctxE elemE)) (.nat 1) (.nat 0))

/-- `any p`, at base `b`: on `[c, xs]`, 1 if some entry passes `p`, else 0. -/
def anyFuns (b p : ℕ) : List Expr :=
  loopFuns b (.length (.get (.var 0) (.nat 1))) (.nat 0) (anyStep p)

/-- The bound of the loops with a small accumulator over `[c, xs]`. -/
theorem len_det {P : Program} {c : Val} {xs : List Val} :
    Det P [.list [c, .list xs]] (.length (.get (.var 0) (.nat 1))) (.nat xs.length)
      (3 * (Val.list [c, .list xs]).wt + 9) := by
  refine (Det.length (Det.get' (Det.var' rfl) (Det.nat 1) rfl)).mono ?_
  have hnx := length_lt_wt_list xs
  have hxa : (Val.list xs).wt < (Val.list [c, .list xs]).wt := wt_le_wt_list (by simp)
  omega

/-- **All.** -/
theorem all_spec {P : Program} {b p : ℕ} (h : P.HasAt b (allFuns b p)) {c : Val}
    {xs : List Val} {q : Val → Bool} {B : Val → ℕ}
    (hp : ∀ x ∈ xs, FunDet P p (.list [c, x]) (boolVal (q x)) (B x)) :
    FunAll P b (.list [c, .list xs]) (fun w cost => w = boolVal (xs.all q) ∧
      cost ≤ (xs.map B).sum +
        loopModK * (xs.length + 1) * ((Val.list [c, .list xs]).wt + xs.length + 4)) := by
  have h2 := (Val.list [c, .list xs]).two_le_size
  have h3 := (Val.list [c, .list xs]).size_le_wt
  refine (loopBdd_spec h len_det (Det.nat 1) (by omega) (M := 3)
    (Inv := fun i acc => acc = boolVal ((xs.take i).all q))
    (D := fun i => B (xs.getD i (.nat 0))) (by simp)
    (fun i acc _ h => h ▸ wt_boolVal_le _) ?_).mono ?_
  · rintro i acc hi rfl
    obtain ⟨hW, hca, hxi, hcx, -, -⟩ := step_wt_facts c xs [] i (boolVal ((xs.take i).all q)) hi
    have hx : xs[i]? = some xs[i] := List.getElem?_eq_getElem hi
    have hin := Det.ite' (P := P) (env := [.list [.list [c, .list xs], .nat i,
        boolVal ((xs.take i).all q)]])
      (Det.call (Det.mk2 Det.ctxE (Det.elemE hi)) (hp xs[i] (List.getElem_mem hi)))
      (Det.nat 1) (Det.nat 0)
    have hbody := Det.ite' (Det.arg' (j := 2) rfl) hin (Det.nat 0)
    have hv : (if ((xs.take i).all q).toNat = 0 then Val.nat 0 else
        (if (q xs[i]).toNat = 0 then Val.nat 0 else .nat 1)) =
        boolVal ((xs.take (i + 1)).all q) := by
      rw [List.take_add_one, hx, Option.toList_some, List.all_append]
      simp only [List.all_cons, List.all_nil, Bool.and_true]
      cases ((xs.take i).all q) <;> cases (q xs[i]) <;> rfl
    rw [hv] at hbody
    refine hbody.post fun cost hc => ⟨rfl, ?_⟩
    have h4 : (Val.nat (q xs[i]).toNat).wt ≤ 3 := wt_boolVal_le _
    have h5 : (boolVal ((xs.take (i + 1)).all q)).wt ≤ 3 := wt_boolVal_le _
    have h6 : (boolVal ((xs.take i).all q)).wt ≤ 3 := wt_boolVal_le _
    have h6' : (Val.nat ((xs.take i).all q).toNat).wt ≤ 3 := wt_boolVal_le _
    have h7 : (if (q xs[i]).toNat = 0 then Val.nat 0 else Val.nat 1).wt ≤ 3 := by
      split <;> simp [wt_nat, GI.Machine.len_zero]
    have := wt_nat_le 0
    have := wt_nat_le 1
    simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]
    omega
  · rintro w cost ⟨rfl, hc⟩
    rw [List.take_length, sum_range_getD] at *
    exact ⟨rfl, hc⟩

/-- **Any.** -/
theorem any_spec {P : Program} {b p : ℕ} (h : P.HasAt b (anyFuns b p)) {c : Val}
    {xs : List Val} {q : Val → Bool} {B : Val → ℕ}
    (hp : ∀ x ∈ xs, FunDet P p (.list [c, x]) (boolVal (q x)) (B x)) :
    FunAll P b (.list [c, .list xs]) (fun w cost => w = boolVal (xs.any q) ∧
      cost ≤ (xs.map B).sum +
        loopModK * (xs.length + 1) * ((Val.list [c, .list xs]).wt + xs.length + 4)) := by
  have h2 := (Val.list [c, .list xs]).two_le_size
  have h3 := (Val.list [c, .list xs]).size_le_wt
  refine (loopBdd_spec h len_det (Det.nat 0) (by omega) (M := 3)
    (Inv := fun i acc => acc = boolVal ((xs.take i).any q))
    (D := fun i => B (xs.getD i (.nat 0))) (by simp)
    (fun i acc _ h => h ▸ wt_boolVal_le _) ?_).mono ?_
  · rintro i acc hi rfl
    obtain ⟨hW, hca, hxi, hcx, -, -⟩ := step_wt_facts c xs [] i (boolVal ((xs.take i).any q)) hi
    have hx : xs[i]? = some xs[i] := List.getElem?_eq_getElem hi
    have hin := Det.ite' (P := P) (env := [.list [.list [c, .list xs], .nat i,
        boolVal ((xs.take i).any q)]])
      (Det.call (Det.mk2 Det.ctxE (Det.elemE hi)) (hp xs[i] (List.getElem_mem hi)))
      (Det.nat 1) (Det.nat 0)
    have hbody := Det.ite' (Det.arg' (j := 2) rfl) (Det.nat 1) hin
    have hv : (if ((xs.take i).any q).toNat = 0 then
        (if (q xs[i]).toNat = 0 then Val.nat 0 else .nat 1) else Val.nat 1) =
        boolVal ((xs.take (i + 1)).any q) := by
      rw [List.take_add_one, hx, Option.toList_some, List.any_append]
      simp only [List.any_cons, List.any_nil, Bool.or_false]
      cases ((xs.take i).any q) <;> cases (q xs[i]) <;> rfl
    rw [hv] at hbody
    refine hbody.post fun cost hc => ⟨rfl, ?_⟩
    have h4 : (Val.nat (q xs[i]).toNat).wt ≤ 3 := wt_boolVal_le _
    have h5 : (boolVal ((xs.take (i + 1)).any q)).wt ≤ 3 := wt_boolVal_le _
    have h6 : (boolVal ((xs.take i).any q)).wt ≤ 3 := wt_boolVal_le _
    have h6' : (Val.nat ((xs.take i).any q).toNat).wt ≤ 3 := wt_boolVal_le _
    have h7 : (if (q xs[i]).toNat = 0 then Val.nat 0 else Val.nat 1).wt ≤ 3 := by
      split <;> simp [wt_nat, GI.Machine.len_zero]
    have := wt_nat_le 0
    have := wt_nat_le 1
    simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]
    omega
  · rintro w cost ⟨rfl, hc⟩
    rw [List.take_length, sum_range_getD] at *
    exact ⟨rfl, hc⟩

end GI.Lang

namespace GI.Lang

open GI.Machine (BinOp len len_le_self)
open GI.Cited (Val)

/-! ### Index of the first entry that passes a test -/

/-- The step of `findIdx p`: the accumulator is the index found so far, or `i` if none. -/
def findStep (p : ℕ) : Expr :=
  .ite (.arith .lt (arg 2) (arg 1)) (arg 2)
    (.ite (.call p (mk2 ctxE elemE)) (arg 1) (.arith .add (arg 1) (.nat 1)))

/-- `findIdx p`, at base `b`: on `[c, xs]`, the index of the first entry that passes `p`, or
the length of `xs` if there is none. -/
def findFuns (b p : ℕ) : List Expr :=
  loopFuns b (.length (.get (.var 0) (.nat 1))) (.nat 0) (findStep p)

theorem findIdx_take_succ {α : Type} (xs : List α) (i : ℕ) (hi : i < xs.length) (q : α → Bool) :
    (if (if (xs.take i).findIdx q < i then 1 else 0) = 0 then
      (if (q xs[i]).toNat = 0 then i + 1 else i) else (xs.take i).findIdx q) =
      (xs.take (i + 1)).findIdx q := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.findIdx_append,
    List.length_take, Nat.min_eq_left hi.le]
  generalize (xs.take i).findIdx q = r
  by_cases h : r < i
  · simp only [h, if_true, one_ne_zero, if_false]
  · simp only [h, if_false, if_true, List.findIdx_cons, List.findIdx_nil]
    cases q xs[i] <;> simp <;> omega

/-- **Find.** -/
theorem find_spec {P : Program} {b p : ℕ} (h : P.HasAt b (findFuns b p)) {c : Val}
    {xs : List Val} {q : Val → Bool} {B : Val → ℕ}
    (hp : ∀ x ∈ xs, FunDet P p (.list [c, x]) (boolVal (q x)) (B x)) :
    FunAll P b (.list [c, .list xs]) (fun w cost => w = .nat (xs.findIdx q) ∧
      cost ≤ (xs.map B).sum +
        loopModK * (xs.length + 1) * ((Val.list [c, .list xs]).wt + 2 * xs.length + 3)) := by
  have h2 := (Val.list [c, .list xs]).two_le_size
  have h3 := (Val.list [c, .list xs]).size_le_wt
  have hle : ∀ i, (xs.take i).findIdx q ≤ xs.length := fun i =>
    List.findIdx_le_length.trans (List.length_take_le' _ _)
  refine (loopBdd_spec h len_det (Det.nat 0) (by omega) (M := xs.length + 2)
    (Inv := fun i acc => acc = .nat ((xs.take i).findIdx q))
    (D := fun i => B (xs.getD i (.nat 0))) (by simp)
    (fun i acc _ h => h ▸ (wt_nat_le _).trans (by have := hle i; omega)) ?_).mono ?_
  · rintro i acc hi rfl
    set r := (xs.take i).findIdx q with hr
    obtain ⟨hW, hca, hxi, hcx, hnx, -⟩ := step_wt_facts c xs [] i (.nat r) hi
    have hx : xs[i]? = some xs[i] := List.getElem?_eq_getElem hi
    have hin := Det.ite' (P := P) (env := [.list [.list [c, .list xs], .nat i, .nat r]])
      (Det.call (Det.mk2 Det.ctxE (Det.elemE hi)) (hp xs[i] (List.getElem_mem hi)))
      (Det.arg' (j := 1) rfl) (Det.arith' (op := .add) (Det.arg' (j := 1) rfl) (Det.nat 1) (z := i + 1) rfl)
    have hc := Det.arith' (P := P) (env := [.list [.list [c, .list xs], .nat i, .nat r]])
      (op := .lt) (Det.arg' (j := 2) rfl) (Det.arg' (j := 1) rfl) rfl
    have hbody := Det.ite' hc (Det.arg' (j := 2) rfl) hin
    have hv : (if BinOp.eval .lt r i = 0 then
        (if (q xs[i]).toNat = 0 then Val.nat (i + 1) else Val.nat i) else Val.nat r) =
        .nat ((xs.take (i + 1)).findIdx q) := by
      rw [← findIdx_take_succ xs i hi q, ← hr]
      simp only [BinOp.eval]
      split_ifs <;> rfl
    rw [hv] at hbody
    refine hbody.post fun cost hc => ⟨rfl, ?_⟩
    have h4 : (Val.nat (q xs[i]).toNat).wt ≤ 3 := wt_boolVal_le _
    have h5 := wt_nat_le r
    have h6 := wt_nat_le ((xs.take (i + 1)).findIdx q)
    have h7 := hle (i + 1)
    have h8 := hle i
    have := wt_nat_le i
    have := wt_nat_le (i + 1)
    have h9 : (if (q xs[i]).toNat = 0 then Val.nat (i + 1) else Val.nat i).wt ≤ i + 3 := by
      split <;> simp only [wt_nat] <;> have := len_le_self i <;> have := len_le_self (i + 1) <;>
        omega
    have h10 : BinOp.eval .lt r i ≤ 1 := by simp only [BinOp.eval]; split_ifs <;> omega
    simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]
    omega
  · rintro w cost ⟨rfl, hc⟩
    rw [List.take_length, sum_range_getD] at *
    exact ⟨rfl, hc.trans (le_of_eq (by ring))⟩

/-! ### Equality of lists of numbers -/

/-- The step of `eqNats`: while the lists agree so far, compare entry `i`. -/
def eqNatsStep : Expr :=
  .ite (arg 2) (.arith .eq (.get (.get (arg 0) (.nat 0)) (arg 1))
    (.get (.get (arg 0) (.nat 1)) (arg 1))) (.nat 0)

/-- `eqNats`, at base `b`: on `[xs, ys]`, two lists of numbers, 1 if they are equal, else 0. -/
def eqNatsFuns (b : ℕ) : List Expr :=
  loopFuns b (.length (.get (.var 0) (.nat 0)))
    (.arith .eq (.length (.get (.var 0) (.nat 0))) (.length (.get (.var 0) (.nat 1)))) eqNatsStep

/-- **Equality of lists of numbers.** -/
theorem eqNats_spec {P : Program} {b : ℕ} (h : P.HasAt b (eqNatsFuns b)) (xs ys : List ℕ) :
    FunDet P b (.list [natList xs, natList ys]) (boolVal (decide (xs = ys)))
      (loopModK * (xs.length + 1) * ((Val.list [natList xs, natList ys]).wt + xs.length + 4)) := by
  set a := Val.list [natList xs, natList ys] with ha
  have ha' : (Val.list [natList xs, natList ys]).wt = a.wt := rfl
  have h2 := a.two_le_size
  have h3 := a.size_le_wt
  have hxa : (natList xs).wt < a.wt := wt_le_wt_list (by simp)
  have hya : (natList ys).wt < a.wt := wt_le_wt_list (by simp)
  have hnx := length_lt_wt_list (xs.map Val.nat)
  have hny := length_lt_wt_list (ys.map Val.nat)
  simp only [List.length_map] at hnx hny
  have hlx := Det.length (P := P) (env := [a]) (Det.get' (Det.var' (i := 0) rfl) (Det.nat 0) (show [natList xs, natList ys][0]? =
      some (.list (xs.map .nat)) from rfl))
  have hly := Det.length (P := P) (env := [a]) (Det.get' (Det.var' (i := 0) rfl) (Det.nat 1) (show [natList xs, natList ys][1]? =
      some (.list (ys.map .nat)) from rfl))
  simp only [List.length_map] at hlx hly
  have hacc := Det.arith' (op := .eq) hlx hly
    (z := (decide (xs.length = ys.length ∧ xs.take 0 = ys.take 0)).toNat)
    (by simp only [BinOp.eval, List.take_zero, and_true]; split_ifs <;> simp_all)
  have hlen := wt_nat_le xs.length
  have hlen' := wt_nat_le ys.length
  have hex : (natList xs).wt = (Val.list (xs.map Val.nat)).wt := rfl
  have hey : (natList ys).wt = (Val.list (ys.map Val.nat)).wt := rfl
  have h4x : 4 ≤ (natList xs).wt := by rw [natList, wt_list_eq]; omega
  have h4y : 4 ≤ (natList ys).wt := by rw [natList, wt_list_eq]; omega
  have hsum := sum_wt_lt_wt_list [natList xs, natList ys]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hsum
  refine (loopBdd_spec h hlx hacc ?_ (M := 3)
    (Inv := fun i acc => acc = boolVal (decide (xs.length = ys.length ∧ xs.take i = ys.take i)))
    (D := fun _ => 0) rfl (fun i acc _ h => h ▸ wt_boolVal_le _) ?_).mono ?_
  · have := Bool.toNat_le (decide (xs.length = ys.length ∧ xs.take 0 = ys.take 0))
    omega
  · rintro i acc hi rfl
    set t := decide (xs.length = ys.length ∧ xs.take i = ys.take i) with ht
    have hW := wt_stepArg_le a i (boolVal t)
    have hbt := wt_boolVal_le t
    have hbt' := wt_boolVal_le (decide (xs.length = ys.length ∧ xs.take (i + 1) = ys.take (i + 1)))
    refine (Det.ite (P := P) (env := [.list [a, .nat i, boolVal t]]) (Det.arg' (j := 2) rfl)
      (v := boolVal (decide (xs.length = ys.length ∧ xs.take (i + 1) = ys.take (i + 1))))
      (ct := 10 * (Val.list [a, .nat i, boolVal t]).wt + 4 * a.wt + 30) (ce := 3)
      (fun hx => ?_) (fun hx => ?_)).post fun cost hc => ⟨rfl, by omega⟩
    · have hl : xs.length = ys.length ∧ xs.take i = ys.take i := by
        by_contra hn; rw [ht, decide_eq_false hn] at hx; exact hx rfl
      have hiy : i < ys.length := hl.1 ▸ hi
      have hxv : (xs.map Val.nat)[i]? = some (.nat xs[i]) := by simp [hi]
      have hyv : (ys.map Val.nat)[i]? = some (.nat ys[i]) := by simp [hiy]
      have hxi : (Val.nat xs[i]).wt < a.wt :=
        (wt_le_wt_list (by simp : Val.nat xs[i] ∈ xs.map Val.nat)).trans hxa
      have hyi : (Val.nat ys[i]).wt < a.wt :=
        (wt_le_wt_list (by simp : Val.nat ys[i] ∈ ys.map Val.nat)).trans hya
      refine (Det.arith' (op := .eq)
        (Det.get' (Det.get' (Det.arg' (j := 0) rfl) (Det.nat 0)
          (show [natList xs, natList ys][0]? = some (.list (xs.map .nat)) from rfl))
          (Det.arg' (j := 1) rfl) hxv)
        (Det.get' (Det.get' (Det.arg' (j := 0) rfl) (Det.nat 1)
          (show [natList xs, natList ys][1]? = some (.list (ys.map .nat)) from rfl))
          (Det.arg' (j := 1) rfl) hyv) ?_).mono ?_
      · have e1 : xs.take (i + 1) = xs.take i ++ [xs[i]] := by
          rw [List.take_add_one, List.getElem?_eq_getElem hi]; rfl
        have e2 : ys.take (i + 1) = ys.take i ++ [ys[i]] := by
          rw [List.take_add_one, List.getElem?_eq_getElem hiy]; rfl
        rw [e1, e2, hl.2]
        simp only [BinOp.eval, List.append_cancel_left_eq, List.cons.injEq, and_true, hl.1,
          true_and]
        by_cases he : xs[i] = ys[i] <;> simp [he]
      · have : (decide (xs.length = ys.length ∧ xs.take (i + 1) = ys.take (i + 1))).toNat ≤ 1 :=
          Bool.toNat_le _
        have := wt_nat_le 0
        have := wt_nat_le 1
        omega
    · have hn : ¬ (xs.length = ys.length ∧ xs.take i = ys.take i) := by
        intro hl; rw [ht, decide_eq_true hl] at hx; exact absurd hx (by decide)
      have hn' : ¬ (xs.length = ys.length ∧ xs.take (i + 1) = ys.take (i + 1)) := by
        rintro ⟨h1, h2⟩
        apply hn
        refine ⟨h1, ?_⟩
        have := congrArg (List.take i) h2
        simpa [List.take_take] using this
      rw [decide_eq_false hn']
      exact (Det.nat 0).mono (by omega)
  · rintro w cost ⟨rfl, hc⟩
    have hiff : (xs.length = ys.length ∧ xs.take xs.length = ys.take xs.length) ↔ xs = ys := by
      constructor
      · rintro ⟨h1, h2⟩; rwa [List.take_length, h1, List.take_length] at h2
      · rintro rfl; simp
    exact ⟨by simp only [hiff], by simpa using hc⟩

end GI.Lang
