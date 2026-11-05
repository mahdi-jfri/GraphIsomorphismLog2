module

public import Workspace.Impl.RowLift
public import Workspace.Impl.LabelLift
public import Workspace.Lang.Lib.SmallGroup

@[expose] public section

/-!
# Windows, their cycles and the points outside them, in `GI.Lang`

The first steps of a localized lift (`Workspace/Impl/RowLift.lean`) as programs:

* `winStepF`: on `[[x₁, b, s, M], i]`, entry `i` of a window (`winF`); a `map` over
  `0, …, k - 1` gives the window (`winTab_spec`);
* `cycStepF`: on `[t, x]`, the image of the row `x` under the cycle `formPerm t` of a window
  `t` without repeats: find `x` in `t` and return the next entry, or `x` if it is absent
  (`cycStep_spec`); a `map` over `0, …, q - 1` gives `encPerm (formPerm t)` (`cycTab_spec`);
* `outTestF`: on `[[rl, σ], i]`, whether position `i` lies in a row `r < q` that `σ` fixes
  (`outTest_spec`); a `filter` over `0, …, n - 1` gives the positions in the domain outside the
  rows of the window (`outList_spec`), when `rl` lists the row of every position (`q` off the
  domain) and `σ = formPerm t`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Machine (BinOp)
open GI.Cited (Val encPerm encGroup gens encPts)

/-- `if` on a known number, with the cost as a sum. -/
theorem Det.iteS {P : Program} {env : List Val} {c t e : Expr} {x : ℕ} {v1 v0 : Val}
    {cc ct ce : ℕ} (hc : Det P env c (.nat x) cc) (ht : Det P env t v1 ct)
    (he : Det P env e v0 ce) :
    Det P env (.ite c t e) (if x = 0 then v0 else v1) (cc + ct + ce + v1.wt + v0.wt + 1) :=
  (Det.ite' hc ht he).mono (by
    have := max_le_add_of_nonneg (Nat.zero_le ct) (Nat.zero_le ce)
    have := max_le_add_of_nonneg (Nat.zero_le v1.wt) (Nat.zero_le v0.wt)
    omega)

theorem wt_ite_le (p : Prop) [Decidable p] (a b : Val) : (if p then a else b).wt ≤ a.wt + b.wt := by
  split_ifs <;> omega

/-! ### The window -/

/-- On `[[x₁, b, s, M], i]`: `winF x₁ b s M i`. -/
def winStepF : Expr :=
  .ite (.arith .eq (arg 1) (.nat 0)) (.nat 0)
    (.ite (.arith .eq (arg 1) (.nat 1)) (.get (arg 0) (.nat 0))
      (.arith .add (.get (arg 0) (.nat 1))
        (.arith .mod (.arith .sub (.arith .add (.get (arg 0) (.nat 2)) (arg 1)) (.nat 2))
          (.get (arg 0) (.nat 3)))))

/-- The parameters of a window as a value. -/
def winPar (x1 base s M : ℕ) : Val := .list [.nat x1, .nat base, .nat s, .nat M]

theorem winF_le (x1 base s M i : ℕ) : winF x1 base s M i ≤ x1 + base + s + i := by
  unfold winF
  split_ifs
  · omega
  · omega
  · have := Nat.mod_le (s + i - 2) M; omega

theorem winStep_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some winStepF) (x1 base s M i : ℕ) :
    FunDet P f (.list [winPar x1 base s M, .nat i]) (.nat (winF x1 base s M i))
      (200 * (x1 + base + s + M + i + 10)) := by
  set c := winPar x1 base s M
  have g0 := Det.arg' (P := P) (vs := [c, .nat i]) (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := P) (vs := [c, .nat i]) (rest := []) (j := 1) rfl
  have dx1 := Det.get' g0 (Det.nat 0) (vs := [.nat x1, .nat base, .nat s, .nat M]) (v := .nat x1) rfl
  have db := Det.get' g0 (Det.nat 1) (vs := [.nat x1, .nat base, .nat s, .nat M]) (v := .nat base)
    rfl
  have ds := Det.get' g0 (Det.nat 2) (vs := [.nat x1, .nat base, .nat s, .nat M]) (v := .nat s) rfl
  have dM := Det.get' g0 (Det.nat 3) (vs := [.nat x1, .nat base, .nat s, .nat M]) (v := .nat M) rfl
  have da := Det.arith' (op := .add) ds g1 (z := s + i) rfl
  have db2 := Det.arith' (op := .sub) da (Det.nat 2) (z := s + i - 2) rfl
  have dm := Det.arith' (op := .mod) db2 dM (z := (s + i - 2) % M) rfl
  have dsum := Det.arith' (op := .add) db dm (z := base + (s + i - 2) % M) rfl
  have e1 := Det.arith' (op := .eq) g1 (Det.nat 1) (z := if i = 1 then 1 else 0) rfl
  have i1 := Det.iteS e1 dx1 dsum
  have e0 := Det.arith' (op := .eq) g1 (Det.nat 0) (z := if i = 0 then 1 else 0) rfl
  have i0 := Det.iteS e0 (Det.nat (P := P) (env := [.list [c, .nat i]]) 0) i1
  have hv : (if (if i = 0 then 1 else 0) = 0 then
      (if (if i = 1 then 1 else 0) = 0 then Val.nat (base + (s + i - 2) % M) else .nat x1)
      else .nat 0) = .nat (winF x1 base s M i) := by
    unfold winF; by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> simp [h0, h1] <;> omega
  rw [hv] at i0
  refine FunDet.intro hf (i0.mono ?_)
  -- the cost
  have hc : c.wt = (Val.list [.nat x1, .nat base, .nat s, .nat M]).wt := rfl
  have w0 := wt_list4_le (.nat x1) (.nat base) (.nat s) (.nat M)
  have w1 := wt_list2_le c (.nat i)
  have a1 := wt_nat_le x1
  have a2 := wt_nat_le base
  have a3 := wt_nat_le s
  have a4 := wt_nat_le M
  have a5 := wt_nat_le i
  have a6 := wt_nat_le (base + (s + i - 2) % M)
  have a7 := wt_nat_le (winF x1 base s M i)
  have a8 := wt_nat_le 0
  have b2 : (s + i - 2) % M ≤ s + i := (Nat.mod_le _ _).trans (by omega)
  have b3 := winF_le x1 base s M i
  have hi1 : (if i = 1 then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have hi0 : (if i = 0 then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have := wt_ite_le ((if i = 1 then 1 else 0) = 0) (Val.nat (base + (s + i - 2) % M)) (Val.nat x1)
  omega

/-! ### The cycle of a window -/

/-- On `[t, x]`: the entry after `x` in `t` (cyclically), or `x` if `x` is not in `t`. The
search `findEq` sits at `fd`. -/
def cycStepF (fd : ℕ) : Expr :=
  .letE (.call fd (mk2 (arg 1) (arg 0)))
    (.ite (.arith .lt (.var 1) (.length (arg 0)))
      (.get (arg 0) (.arith .mod (.arith .add (.var 1) (.nat 1)) (.length (arg 0))))
      (arg 1))

/-- The value of a list of rows. -/
def rowsV {q : ℕ} (t : List (Fin q)) : Val := natList (t.map Fin.val)

theorem wt_rowsV_le {q : ℕ} (t : List (Fin q)) (ht : t.length ≤ q) : (rowsV t).wt ≤ 5 * (q + 1) ^ 2 :=
  wt_natList_le_sq (by intro x hx; obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx; exact y.2.le)
    (by simpa using ht)

/-- The cost constant of the cycle step. -/
def cycK : ℕ := 1000000

/-- The image of `x` under the cycle of a list without repeats, by position. -/
theorem formPerm_val_eq {q : ℕ} (t : List (Fin q)) (hnd : t.Nodup) (x : Fin q) :
    ((t.formPerm x : Fin q) : ℕ) =
      if (t.map Fin.val).findIdx (fun y => decide (y = (x : ℕ))) < t.length then
        (t.map Fin.val).getD (((t.map Fin.val).findIdx (fun y => decide (y = (x : ℕ))) + 1) %
          t.length) 0
      else x := by
  set i := (t.map Fin.val).findIdx (fun y => decide (y = (x : ℕ)))
  by_cases hx : x ∈ t
  · have hlt : i < (t.map Fin.val).length :=
      List.findIdx_lt_length.2 ⟨x, List.mem_map_of_mem hx, by simp⟩
    rw [List.length_map] at hlt
    rw [if_pos hlt]
    have hi : t[i] = x := by
      have := List.findIdx_getElem (w := by rw [List.length_map]; exact hlt)
        (p := fun y => decide (y = (x : ℕ)))
        (xs := t.map Fin.val)
      simp only [List.getElem_map, decide_eq_true_eq] at this
      exact Fin.ext this
    have hpos : 0 < t.length := by omega
    rw [← hi, List.formPerm_apply_getElem _ hnd i hlt, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_eq_getElem (Nat.mod_lt _ hpos)]
    simp
  · have hge : ¬ i < t.length := by
      intro hlt
      rw [← List.length_map (f := Fin.val)] at hlt
      obtain ⟨y, hy, hyx⟩ := List.findIdx_lt_length.1 hlt
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
      simp only [decide_eq_true_eq] at hyx
      exact hx (Fin.ext hyx ▸ hz)
    rw [if_neg hge, List.formPerm_apply_of_notMem hx]

theorem cycStep_spec {P : Program} {f fd : ℕ} (hf : P.funs[f]? = some (cycStepF fd))
    (hfd : P.HasAt fd (findEqFuns fd)) {q : ℕ} (t : List (Fin q)) (hnd : t.Nodup)
    (ht : t.length ≤ q) (x : Fin q) :
    FunDet P f (.list [rowsV t, .nat x]) (.nat (t.formPerm x)) (cycK * (q + 1) ^ 3) := by
  set tv := rowsV t
  set inp := Val.list [tv, .nat x]
  set i := (t.map Fin.val).findIdx (fun y => decide (y = (x : ℕ))) with hi
  have hbnd : ∀ y ∈ t.map Fin.val, y ≤ q := by
    intro y hy; obtain ⟨z, -, rfl⟩ := List.mem_map.mp hy; exact z.2.le
  have g0 := Det.arg' (P := P) (vs := [tv, .nat x]) (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := P) (vs := [tv, .nat x]) (rest := []) (j := 1) rfl
  have dfind := Det.call (Det.mk2 g1 g0) (findEq_spec hfd hbnd x.2.le (by simpa using ht))
  have h0 := Det.arg' (P := P) (vs := [tv, .nat x]) (rest := [.nat i]) (j := 0) rfl
  have h1 := Det.arg' (P := P) (vs := [tv, .nat x]) (rest := [.nat i]) (j := 1) rfl
  have hv1 := Det.var' (P := P) (env := [inp, .nat i]) (i := 1) (v := .nat i) rfl
  have htv : tv = .list ((t.map Fin.val).map Val.nat) := rfl
  rw [htv] at h0
  have hlen := Det.length h0
  rw [List.length_map, List.length_map] at hlen
  have dlt := Det.arith' (op := .lt) hv1 hlen (z := if i < t.length then 1 else 0) rfl
  have dadd := Det.arith' (op := .add) hv1 (Det.nat 1) (z := i + 1) rfl
  have dmod := Det.arith' (op := .mod) dadd hlen (z := (i + 1) % t.length) rfl
  by_cases hlt : i < t.length
  · have hpos : 0 < t.length := by omega
    have hm : (i + 1) % t.length < t.length := Nat.mod_lt _ hpos
    have dget := Det.get' h0 dmod (v := .nat ((t.map Fin.val).getD ((i + 1) % t.length) 0)) (by
      rw [List.getElem?_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
        (by simpa using hm)]
      simp)
    have dite := Det.iteS dlt dget h1
    rw [if_pos hlt] at dite
    simp only [one_ne_zero, if_false] at dite
    have hval : ((t.formPerm x : Fin q) : ℕ) = (t.map Fin.val).getD ((i + 1) % t.length) 0 := by
      rw [formPerm_val_eq t hnd x, ← hi, if_pos hlt]
    rw [← hval] at dite
    refine FunDet.intro hf ((Det.letE dfind dite).mono ?_)
    -- the cost
    have w1 := wt_rowsV_le t ht
    have w2 := wt_list2_le tv (.nat x)
    have w3 := wt_list2_le (.nat x) tv
    have w4 := wt_nat_le x
    have w5 := wt_nat_le i
    have w6 := wt_nat_le ((t.formPerm x : Fin q) : ℕ)
    have w7 := wt_nat_le ((i + 1) % t.length)
    have w8 := wt_nat_le t.length
    have hx := x.2
    have hfx := (t.formPerm x).2
    have hq3 : (q + 1) ^ 2 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have hq1 : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    simp only [cycK, findEqK] at *
    have := wt_ite_le (i < t.length) (Val.nat 1) (Val.nat 0)
    have w9 := wt_list2_le (.nat x) (natList (t.map Fin.val))
    have w10 : (natList (t.map Fin.val)).wt ≤ 5 * (q + 1) ^ 2 := wt_rowsV_le t ht
    have e2 : (Val.list ((t.map Fin.val).map Val.nat)).wt = tv.wt := rfl
    have hil : i ≤ t.length := by
      have := List.findIdx_le_length (p := fun y => decide (y = (x : ℕ))) (xs := t.map Fin.val)
      rwa [List.length_map] at this
    have e3 : (Val.list [Val.list ((t.map Fin.val).map Val.nat), Val.nat x]).wt =
      (Val.list [tv, Val.nat x]).wt := rfl
    have e4 : (Val.nat ((t.map Fin.val).findIdx (fun y => decide (y = (x : ℕ))))).wt =
      (Val.nat i).wt := rfl
    have hm : (i + 1) % t.length ≤ i + 1 := Nat.mod_le _ _
    have w1' : tv.wt ≤ 5 * (q + 1) ^ 2 := w1
    omega
  · rw [if_neg hlt] at dlt
    have dite := Det.ite_zero (t := .get (arg 0) (.arith .mod (.arith .add (.var 1) (.nat 1))
      (.length (arg 0)))) dlt h1
    have hval : ((t.formPerm x : Fin q) : ℕ) = x := by
      rw [formPerm_val_eq t hnd x, ← hi, if_neg hlt]
    rw [hval]
    refine FunDet.intro hf ((Det.letE dfind dite).mono ?_)
    have w1 : tv.wt ≤ 5 * (q + 1) ^ 2 := wt_rowsV_le t ht
    have w2 := wt_list2_le tv (.nat x)
    have w3 := wt_list2_le (.nat x) tv
    have w4 := wt_nat_le x
    have w5 := wt_nat_le i
    have w6 := wt_nat_le ((t.formPerm x : Fin q) : ℕ)
    have w8 := wt_nat_le t.length
    have hx := x.2
    have hq3 : (q + 1) ^ 2 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have hq1 : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    simp only [cycK, findEqK] at *
    have w9 := wt_list2_le (.nat x) (natList (t.map Fin.val))
    have w10 : (natList (t.map Fin.val)).wt ≤ 5 * (q + 1) ^ 2 := wt_rowsV_le t ht
    have hil : i ≤ t.length := by
      have := List.findIdx_le_length (p := fun y => decide (y = (x : ℕ))) (xs := t.map Fin.val)
      rwa [List.length_map] at this
    have e3 : (Val.list [Val.list ((t.map Fin.val).map Val.nat), Val.nat x]).wt =
      (Val.list [tv, Val.nat x]).wt := rfl
    have e4 : (Val.nat ((t.map Fin.val).findIdx (fun y => decide (y = (x : ℕ))))).wt =
      (Val.nat i).wt := rfl
    omega

/-! ### Tables over `0, …, m - 1` -/

theorem natList_range_eq (m : ℕ) : natList (List.range m) = encFun fun i : Fin m => (i : ℕ) := by
  rw [range_eq_encPerm_one, encPerm_eq_encFun]; rfl

/-- The constant of the cycle table. -/
def cycTabK : ℕ := 2 * cycK + 100 * mapK

/-- **The cycle of a window, as a permutation value.** -/
theorem cycTab_spec {P : Program} {b f fd : ℕ} (hb : P.HasAt b (mapFuns b f))
    (hf : P.funs[f]? = some (cycStepF fd)) (hfd : P.HasAt fd (findEqFuns fd)) {q : ℕ}
    (t : List (Fin q)) (hnd : t.Nodup) (ht : t.length ≤ q) :
    FunDet P b (.list [rowsV t, natList (List.range q)]) (encPerm t.formPerm)
      (cycTabK * (q + 1) ^ 4) := by
  rw [natList_range_eq]
  refine (tabulate_spec hb (F := fun x : Fin q => .nat (t.formPerm x))
    (fun x => cycStep_spec hf hfd t hnd ht x)).mono ?_
  have e : Val.list ((List.finRange q).map fun x : Fin q => Val.nat (t.formPerm x)) =
    encPerm t.formPerm := rfl
  rw [e]
  have w1 := wt_rowsV_le t ht
  have w2 := wt_ids_le q
  have w3 := wt_encPerm_le t.formPerm
  have w4 := wt_list2_le (rowsV t) (encFun fun i : Fin q => (i : ℕ))
  have h1 : q * (cycK * (q + 1) ^ 3) ≤ 1000000 * (q + 1) ^ 4 := by
    have : q * (q + 1) ^ 3 ≤ (q + 1) ^ 4 := by
      calc q * (q + 1) ^ 3 ≤ (q + 1) * (q + 1) ^ 3 := Nat.mul_le_mul_right _ (by omega)
        _ = (q + 1) ^ 4 := by ring
    calc q * (cycK * (q + 1) ^ 3) = 1000000 * (q * (q + 1) ^ 3) := by simp only [cycK]; ring
      _ ≤ 1000000 * (q + 1) ^ 4 := Nat.mul_le_mul_left _ this
  have h2 : mapK * (q + 1) * ((Val.list [rowsV t, encFun fun i : Fin q => (i : ℕ)]).wt +
      (encPerm t.formPerm).wt + 1) ≤ mapK * (q + 1) * (100 * (q + 1) ^ 3) := by
    apply Nat.mul_le_mul_left
    have : (q + 1) ^ 2 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have h3 : mapK * (q + 1) * (100 * (q + 1) ^ 3) = 100000 * (q + 1) ^ 4 := by
    simp only [mapK]; ring
  have hK : cycTabK * (q + 1) ^ 4 = 2100000 * (q + 1) ^ 4 := by
    simp only [cycTabK, cycK, mapK]
  omega

/-! ### The positions outside the window -/

/-- Whether position `i` lies in a row `r < q` that `σ` fixes; `rl` lists the rows. -/
def outP {q : ℕ} (rl : List ℕ) (σ : Perm (Fin q)) (i : ℕ) : Bool :=
  if h : rl.getD i 0 < q then decide (((σ ⟨_, h⟩ : Fin q) : ℕ) = rl.getD i 0) else false

/-- On `[[rl, σ], i]`: `outP rl σ i`. -/
def outTestF : Expr :=
  .letE (.get (.get (arg 0) (.nat 0)) (arg 1))
    (.ite (.arith .lt (.var 1) (.length (.get (arg 0) (.nat 1))))
      (.arith .eq (.get (.get (arg 0) (.nat 1)) (.var 1)) (.var 1))
      (.nat 0))

/-- The cost constant of the test. -/
def outK : ℕ := 1000

theorem outTest_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some outTestF) {q : ℕ}
    (rl : List ℕ) (σ : Perm (Fin q)) (i : ℕ) (hi : i < rl.length) (hrl : ∀ r ∈ rl, r ≤ q) :
    FunDet P f (.list [.list [natList rl, encPerm σ], .nat i]) (boolVal (outP rl σ i))
      (outK * ((Val.list [.list [natList rl, encPerm σ], .nat i]).wt + q + 1)) := by
  set c := Val.list [natList rl, encPerm σ]
  set inp := Val.list [c, .nat i]
  set r := rl.getD i 0 with hr
  have hrq : r ≤ q := hrl r (by rw [hr, List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi)
  have g0 := Det.arg' (P := P) (vs := [c, .nat i]) (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := P) (vs := [c, .nat i]) (rest := []) (j := 1) rfl
  have dl := Det.get' g0 (Det.nat 0) (vs := [natList rl, encPerm σ]) (v := natList rl) rfl
  have dr := Det.get' dl g1 (vs := rl.map Val.nat) (v := .nat r) (by
    rw [List.getElem?_map, List.getElem?_eq_getElem hi, hr, List.getD_eq_getElem _ _ hi]; rfl)
  have h0 := Det.arg' (P := P) (vs := [c, .nat i]) (rest := [.nat r]) (j := 0) rfl
  have hs := Det.get' h0 (Det.nat 1) (vs := [natList rl, encPerm σ]) (v := encPerm σ) rfl
  have hv1 := Det.var' (P := P) (env := [inp, .nat r]) (i := 1) (v := .nat r) rfl
  have hsl : encPerm σ = .list ((List.finRange q).map fun j => Val.nat (σ j)) := rfl
  rw [hsl] at hs
  have hlen := Det.length hs
  rw [List.length_map, List.length_finRange] at hlen
  have dlt := Det.arith' (op := .lt) hv1 hlen (z := if r < q then 1 else 0) rfl
  by_cases hq : r < q
  · rw [if_pos hq] at dlt
    have dsr := Det.get' hs hv1 (v := .nat (σ ⟨r, hq⟩)) (by
      rw [List.getElem?_map, List.getElem?_eq_getElem (by simpa using hq)]; simp)
    have deq := Det.arith' (op := .eq) dsr hv1
      (z := if ((σ ⟨r, hq⟩ : Fin q) : ℕ) = r then 1 else 0) rfl
    have dite := Det.ite_pos (e := .nat 0) dlt one_ne_zero deq
    have hval : (Val.nat (if ((σ ⟨r, hq⟩ : Fin q) : ℕ) = r then 1 else 0)) =
        boolVal (outP rl σ i) := by
      unfold outP; rw [← hr, dif_pos hq]; by_cases h : ((σ ⟨r, hq⟩ : Fin q) : ℕ) = r <;> simp [h]
    rw [hval] at dite
    refine FunDet.intro hf ((Det.letE dr dite).mono ?_)
    have w1 := wt_list2_le c (.nat i)
    have w2 := wt_nat_le r
    have w3 := wt_nat_le ((σ ⟨r, hq⟩ : Fin q) : ℕ)
    have w4 := wt_boolVal_le (outP rl σ i)
    have w5 : c.wt < inp.wt := wt_le_wt_list (by simp)
    have w6 : (natList rl).wt < c.wt := wt_le_wt_list (by simp)
    have w7 : (encPerm σ).wt < c.wt := wt_le_wt_list (by simp)
    have e7 : (Val.list ((List.finRange q).map fun j => Val.nat (σ j))).wt = (encPerm σ).wt := rfl
    have hs1 := (σ ⟨r, hq⟩).2
    have hb : (if ((σ ⟨r, hq⟩ : Fin q) : ℕ) = r then 1 else 0) ≤ 1 := by split_ifs <;> omega
    have e8 : (Val.list (rl.map Val.nat)).wt = (natList rl).wt := rfl
    have e9 : (Val.list [c, Val.nat i]).wt = inp.wt := rfl
    unfold outK
    omega
  · rw [if_neg hq] at dlt
    have dite := Det.ite_zero (t := .arith .eq (.get (.get (arg 0) (.nat 1)) (.var 1)) (.var 1))
      dlt (Det.nat (P := P) (env := [inp, .nat r]) 0)
    have hval : (Val.nat 0) = boolVal (outP rl σ i) := by
      unfold outP; rw [← hr, dif_neg hq]; rfl
    rw [hval] at dite
    refine FunDet.intro hf ((Det.letE dr dite).mono ?_)
    have w1 := wt_list2_le c (.nat i)
    have w2 := wt_nat_le r
    have w4 := wt_boolVal_le (outP rl σ i)
    have w5 : c.wt < inp.wt := wt_le_wt_list (by simp)
    have w6 : (natList rl).wt < c.wt := wt_le_wt_list (by simp)
    have w7 : (encPerm σ).wt < c.wt := wt_le_wt_list (by simp)
    have e7 : (Val.list ((List.finRange q).map fun j => Val.nat (σ j))).wt = (encPerm σ).wt := rfl
    have e8 : (Val.list (rl.map Val.nat)).wt = (natList rl).wt := rfl
    have e9 : (Val.list [c, Val.nat i]).wt = inp.wt := rfl
    unfold outK
    omega

/-- The test on values. -/
def outQ {q : ℕ} (rl : List ℕ) (σ : Perm (Fin q)) : Val → Bool
  | .nat i => outP rl σ i
  | .list _ => false

/-- The positions in the domain outside the rows of a window. -/
def outPts {n q : ℕ} (rl : List ℕ) (σ : Perm (Fin q)) : List (Fin n) :=
  (List.finRange n).filter fun i => outP rl σ i

theorem natList_outPts {n q : ℕ} (rl : List ℕ) (σ : Perm (Fin q)) :
    natList ((List.range n).filter (outP rl σ)) = encPts (n := n) (outPts (n := n) rl σ) := by
  unfold natList encPts outPts
  congr 1
  rw [← List.map_coe_finRange_eq_range, List.filter_map, List.map_map]
  simp only [Function.comp_def]
  induction (List.filter (fun x : Fin n => outP rl σ ↑x) (List.finRange n)) with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons] at ih ⊢; rw [ih]; rfl

/-- The constant of the outside filter. -/
def outFK : ℕ := 10 ^ 4

/-- **The positions outside the window**, by a filter over `0, …, n - 1`. -/
theorem outList_spec {P : Program} {b f : ℕ} (hb : P.HasAt b (filterFuns b f))
    (hf : P.funs[f]? = some outTestF) {n q : ℕ} (rl : List ℕ) (hl : rl.length = n)
    (hrl : ∀ r ∈ rl, r ≤ q) (σ : Perm (Fin q)) :
    FunDet P b (.list [.list [natList rl, encPerm σ], natList (List.range n)])
      (encPts (n := n) (outPts (n := n) rl σ))
      (outFK * ((Val.list [.list [natList rl, encPerm σ], natList (List.range n)]).wt + q + 1) ^ 2) := by
  set c := Val.list [natList rl, encPerm σ]
  set A := (Val.list [c, natList (List.range n)]).wt
  have hxs : natList (List.range n) = .list ((List.range n).map Val.nat) := rfl
  have hcA : c.wt < A := wt_le_wt_list (by simp)
  have hnA : n < A := by
    have := length_lt_wt_list ((List.range n).map Val.nat)
    have e : (Val.list ((List.range n).map Val.nat)).wt = (natList (List.range n)).wt := rfl
    have : (natList (List.range n)).wt < A := wt_le_wt_list (by simp)
    simp only [List.length_map, List.length_range] at *
    omega
  have hF := filter_spec hb (c := c) (xs := (List.range n).map Val.nat) (q := outQ rl σ)
    (B := fun _ => outK * (2 * c.wt + 2 * A + q + 20)) (by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have hin : i < rl.length := by rw [hl]; exact List.mem_range.mp hi
      refine (outTest_spec hf rl σ i hin hrl).mono ?_
      have := wt_list2_le c (.nat i)
      have := wt_nat_le i
      have : i < n := List.mem_range.mp hi
      have e : (Val.list [Val.list [natList rl, encPerm σ], Val.nat i]).wt =
        (Val.list [c, Val.nat i]).wt := rfl
      unfold outK; omega)
  rw [← hxs] at hF
  refine hF.mono fun w cost ⟨hw, hc⟩ => ⟨?_, ?_⟩
  · rw [hw, ← natList_outPts, natList, List.filter_map]; rfl
  · rw [List.map_const', List.sum_replicate, smul_eq_mul, List.length_map, List.length_range] at hc
    have hww : w.wt ≤ A := by
      rw [hw]
      have h1 := wt_list_sublist (List.filter_sublist (p := outQ rl σ)
        (l := (List.range n).map Val.nat))
      have h2 : (natList (List.range n)).wt < A := wt_le_wt_list (by simp)
      have e : (Val.list ((List.range n).map Val.nat)).wt = (natList (List.range n)).wt := rfl
      omega
    have e : (Val.list [c, natList (List.range n)]).wt = A := rfl
    rw [e] at hc
    have h1 : n * (outK * (2 * c.wt + 2 * A + q + 20)) ≤ outK * (A * (4 * A + q + 20)) := by
      have : n * (2 * c.wt + 2 * A + q + 20) ≤ A * (4 * A + q + 20) :=
        Nat.mul_le_mul (by omega) (by omega)
      calc n * (outK * (2 * c.wt + 2 * A + q + 20)) = outK * (n * (2 * c.wt + 2 * A + q + 20)) := by
            ring
        _ ≤ _ := Nat.mul_le_mul_left _ this
    have h2 : loopModK * (n + 1) * (A + n + w.wt + 1) ≤ loopModK * (A + 1) * (4 * A + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have h3 : outK * (A * (4 * A + q + 20)) + loopModK * (A + 1) * (4 * A + 1) ≤
        outFK * (A + q + 1) ^ 2 := by
      simp only [outK, outFK, loopModK]
      have : 0 ≤ A * q := Nat.zero_le _
      ring_nf; nlinarith [Nat.zero_le q, Nat.zero_le A]
    omega

end GI.Impl
