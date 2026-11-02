/-
**Lists of numbers.** Small library functions on lists of numbers (`natList xs`), used by the
steps of the recursion (`Workspace/Impl/`).

* `eqTestF` (from `Workspace/Lang/Lib/Perm.lean`): on `[j, y]`, whether `y = j`.
* `countFuns`: on `[j, xs]`, the number of entries equal to `j`.
* `maxFuns`: on `xs`, the largest entry (`0` for the empty list).
* `findEqFuns`: on `[j, xs]`, the index of the first entry equal to `j`.
* `eqIndFuns`: on `[j, xs]`, the list of `[x = j]` (1 or 0) for the entries `x`.
* `gatherFuns`: on `[L, is]`, the list of the entries `L[i]` for `i` in `is`.

The cost bounds are stated with one number `B` that bounds the entries and the length of the
lists (or with the weight of the argument for `gatherFuns`).
-/
import Workspace.Lang.Lib.Tabulate

namespace GI.Lang

open GI.Machine (BinOp len len_le_self)
open GI.Cited (Val encPerm encPerms)

/-! ### Weights of lists of numbers -/

theorem wt_natList_le {xs : List ℕ} {B : ℕ} (h : ∀ x ∈ xs, x ≤ B) :
    (natList xs).wt ≤ xs.length * (2 * B + 5) + 4 := by
  have h1 := wt_list_le (xs.map Val.nat)
  have h2 : ((xs.map Val.nat).map Val.wt).sum ≤ xs.length * (B + 2) := by
    have := List.sum_le_card_nsmul ((xs.map Val.nat).map Val.wt) (B + 2) (by
      simp only [List.map_map, List.mem_map, Function.comp_apply, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intro x hx; have := wt_nat_le x; have := h x hx; omega)
    simpa using this
  simp only [List.length_map] at h1
  rw [natList]
  nlinarith

theorem wt_natList_le_sq {xs : List ℕ} {B : ℕ} (h : ∀ x ∈ xs, x ≤ B) (hl : xs.length ≤ B) :
    (natList xs).wt ≤ 5 * (B + 1) ^ 2 := by
  have := wt_natList_le h
  have : xs.length * (2 * B + 5) ≤ B * (2 * B + 5) := Nat.mul_le_mul_right _ hl
  nlinarith

theorem encFun_eq_natList {n : ℕ} (f : Fin n → ℕ) :
    encFun f = natList ((List.finRange n).map f) := by
  simp [encFun, natList, List.map_map, Function.comp_def]

/-! ### The equality test -/

theorem natEq_nat (j y : ℕ) : natEq j (.nat y) = decide (y = j) := by
  unfold natEq; by_cases h : y = j <;> simp [h]

theorem eqTest_det {P : Program} {f : ℕ} (hf : P.funs[f]? = some eqTestF) (j y : ℕ) :
    FunDet P f (.list [.nat j, .nat y]) (boolVal (natEq j (.nat y))) (10 * (j + y) + 100) := by
  refine FunDet.intro hf ((Det.arith' (Det.arg' (rest := []) (j := 1) rfl)
    (Det.arg' (j := 0) rfl) (z := (natEq j (.nat y)).toNat) ?_).mono ?_)
  · simp only [BinOp.eval, natEq_nat]
    by_cases hij : y = j <;> simp [hij]
  · have := wt_list2_le (.nat j) (.nat y)
    have := wt_nat_le j
    have := wt_nat_le y
    have : (natEq j (.nat y)).toNat ≤ 1 := Bool.toNat_le _
    omega

/-! ### Count -/

/-- The entry of `count`: the length of the filtered list. -/
def countEntry (fl : ℕ) : Expr := .length (.call fl (.var 0))

/-- `count`, at base `b` (five functions): on `[j, xs]`, the number of entries equal to `j`. -/
def countFuns (b : ℕ) : List Expr :=
  [countEntry (b + 1)] ++ filterFuns (b + 1) (b + 4) ++ [eqTestF]

def countK : ℕ := 100000

theorem filter_natEq (j : ℕ) (xs : List ℕ) :
    (xs.map Val.nat).filter (natEq j) = (xs.filter fun x => decide (x = j)).map Val.nat := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.filter_cons, natEq_nat]
    split_ifs <;> simp [ih]

theorem count_eq_filter (j : ℕ) (xs : List ℕ) :
    (xs.filter fun x => decide (x = j)).length = xs.count j := by
  rw [List.count_eq_length_filter]
  congr 1

/-- **Count.** -/
theorem count_spec {P : Program} {b : ℕ} (h : P.HasAt b (countFuns b)) {xs : List ℕ} {j B : ℕ}
    (hB : ∀ x ∈ xs, x ≤ B) (hj : j ≤ B) (hl : xs.length ≤ B) :
    FunDet P b (.list [.nat j, natList xs]) (.nat (xs.count j)) (countK * (B + 1) ^ 3) := by
  have hentry : P.funs[b]? = some (countEntry (b + 1)) := by
    simpa [countFuns] using h 0 (by simp [countFuns])
  have hfl : P.HasAt (b + 1) (filterFuns (b + 1) (b + 4)) := by
    simpa using h.left.right
  have htest : P.funs[b + 4]? = some eqTestF := by
    simpa [countFuns, filterFuns, loopFuns, Nat.add_assoc] using h 4 (by simp [countFuns,
      filterFuns, loopFuns])
  have hT : ∀ x ∈ xs.map Val.nat, FunDet P (b + 4) (.list [.nat j, x]) (boolVal (natEq j x))
      (20 * B + 100) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact (eqTest_det htest j y).mono (by have := hB y hy; omega)
  have hF := filter_spec hfl (c := .nat j) (xs := xs.map Val.nat) hT
  rw [filter_natEq] at hF
  have hfil : ∀ x ∈ xs.filter (fun x => decide (x = j)), x ≤ B := fun x hx =>
    hB x (List.mem_of_mem_filter hx)
  have hfl' : (xs.filter fun x => decide (x = j)).length ≤ B :=
    (List.length_filter_le _ _).trans hl
  have hw1 := wt_natList_le_sq hfil hfl'
  have hw2 := wt_natList_le_sq hB hl
  have hw3 := wt_list2_le (.nat j) (natList xs)
  have hw4 := wt_nat_le j
  have hcnt := count_eq_filter j xs
  have hF' : FunDet P (b + 1) (.list [.nat j, natList xs])
      (natList (xs.filter fun x => decide (x = j)))
      (((xs.map Val.nat).map fun _ => 20 * B + 100).sum + loopModK * ((xs.map Val.nat).length + 1) *
        ((Val.list [.nat j, natList xs]).wt + (xs.map Val.nat).length +
          (natList (xs.filter fun x => decide (x = j))).wt + 1)) :=
    hF.mono fun w c hw => ⟨hw.1, by obtain ⟨h1, h2⟩ := hw; subst h1; exact h2⟩
  refine FunDet.intro hentry ((Det.length (Det.call (Det.var' (P := P)
    (env := [.list [.nat j, natList xs]]) (i := 0) rfl) hF')).post fun c hc => ?_)
  have hlen : ((xs.filter fun x => decide (x = j)).map Val.nat).length = xs.count j := by
    rw [List.length_map, hcnt]
  have hlen' : (natList (xs.filter fun x => decide (x = j))) =
    .list ((xs.filter fun x => decide (x = j)).map Val.nat) := rfl
  refine ⟨by rw [hlen], ?_⟩
  rw [hlen'] at hc
  rw [hlen, ← hlen'] at hc
  simp only [List.map_map, List.length_map] at hc
  have hs : ((xs.map ((fun _ => 20 * B + 100) ∘ Val.nat))).sum = xs.length * (20 * B + 100) := by
    rw [show ((fun _ => 20 * B + 100) ∘ Val.nat) = fun _ => 20 * B + 100 from rfl,
      List.map_const', List.sum_replicate, smul_eq_mul]
  rw [hs] at hc
  have h1 : xs.length * (20 * B + 100) ≤ 100 * (B + 1) ^ 2 := by
    have := Nat.mul_le_mul_right (20 * B + 100) hl; nlinarith
  have h2 : loopModK * (xs.length + 1) * ((Val.list [.nat j, natList xs]).wt + xs.length +
      (natList (xs.filter fun x => decide (x = j))).wt + 1) ≤
      loopModK * (B + 1) * (60 * (B + 1) ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by nlinarith)
  have h3 : loopModK * (B + 1) * (60 * (B + 1) ^ 2) = 60000 * (B + 1) ^ 3 := by
    simp only [loopModK]; ring
  have h4 : (B + 1) ^ 2 ≤ (B + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have h5 : (Val.list [.nat j, natList xs]).wt + 1 ≤ 30 * (B + 1) ^ 2 := by nlinarith
  have h6 : xs.count j ≤ B := (List.count_le_length (a := j) (l := xs)).trans hl
  simp only [countK]
  nlinarith

/-! ### Maximum -/

/-- The step of `max`: on `[c, acc, x]`, the larger of `acc` and `x`. -/
def maxF : Expr := .ite (.arith .lt (arg 1) (arg 2)) (arg 2) (arg 1)

/-- `max`, at base `b` (five functions): on `xs`, the largest entry, or `0`. -/
def maxFuns (b : ℕ) : List Expr :=
  [.call (b + 1) (mk3 .nil (.var 0) (.nat 0))] ++ foldlFuns (b + 1) (b + 4) ++ [maxF]

def maxK : ℕ := 100000

/-- The step function of the fold. -/
def maxG : Val → Val → Val
  | .nat a, .nat x => .nat (max a x)
  | _, _ => .nat 0

theorem foldl_maxG (a : ℕ) (xs : List ℕ) :
    (xs.map Val.nat).foldl maxG (.nat a) = .nat (xs.foldl max a) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.foldl_cons, maxG, ih]

theorem foldl_max_le {xs : List ℕ} {a B : ℕ} (ha : a ≤ B) (h : ∀ x ∈ xs, x ≤ B) :
    xs.foldl max a ≤ B := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact ih (max_le ha (h x (by simp))) fun y hy => h y (by simp [hy])

theorem le_foldl_max (xs : List ℕ) (a : ℕ) : a ≤ xs.foldl max a ∧ ∀ x ∈ xs, x ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    obtain ⟨h1, h2⟩ := ih (max a x)
    exact ⟨(le_max_left a x).trans h1, (le_max_right a x).trans h1, h2⟩

theorem foldl_max_mem (xs : List ℕ) (a : ℕ) : xs.foldl max a = a ∨ xs.foldl max a ∈ xs := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rcases ih (max a x) with h | h
    · rw [h]
      rcases le_total a x with hax | hax
      · exact Or.inr (Or.inl (max_eq_right hax))
      · exact Or.inl (max_eq_left hax)
    · exact Or.inr (Or.inr h)

/-- **Maximum.** -/
theorem max_spec {P : Program} {b : ℕ} (h : P.HasAt b (maxFuns b)) {xs : List ℕ} {B : ℕ}
    (hB : ∀ x ∈ xs, x ≤ B) (hl : xs.length ≤ B) :
    FunDet P b (natList xs) (.nat (xs.foldl max 0)) (maxK * (B + 1) ^ 3) := by
  have hentry : P.funs[b]? = some (.call (b + 1) (mk3 .nil (.var 0) (.nat 0))) := by
    simpa [maxFuns] using h 0 (by simp [maxFuns])
  have hfold : P.HasAt (b + 1) (foldlFuns (b + 1) (b + 4)) := by
    simpa using h.left.right
  have hstep : P.funs[b + 4]? = some maxF := by
    simpa [maxFuns, foldlFuns, loopFuns, Nat.add_assoc] using h 4 (by simp [maxFuns,
      foldlFuns, loopFuns])
  have hpart : ∀ i, ((xs.map Val.nat).take i).foldl maxG (.nat 0) =
      .nat ((xs.take i).foldl max 0) := by
    intro i; rw [← List.map_take, foldl_maxG]
  have hle : ∀ i, (xs.take i).foldl max 0 ≤ B := fun i =>
    foldl_max_le (Nat.zero_le _) fun x hx => hB x (List.mem_of_mem_take hx)
  have hfd := foldl_spec_fun hfold (c := .list []) (xs := xs.map Val.nat) (acc0 := .nat 0)
    (G := maxG) (M := B + 2) (B := fun _ => 30 * B + 200)
    (fun i _ => by rw [hpart]; have := wt_nat_le ((xs.take i).foldl max 0); have := hle i; omega)
    (fun i hi => by
      rw [hpart]
      have hi' : i < xs.length := by simpa using hi
      have hxi : (xs.map Val.nat)[i] = .nat xs[i] := by simp
      rw [hxi]
      set a := (xs.take i).foldl max 0
      have ha := hle i
      have hx := hB xs[i] (List.getElem_mem hi')
      have hc := Det.arith' (P := P) (env := [.list [.list [], .nat a, .nat xs[i]]]) (op := .lt)
        (Det.arg' (rest := []) (j := 1) rfl) (Det.arg' (j := 2) rfl) rfl
      have hb := Det.ite' hc (Det.arg' (rest := []) (j := 2) rfl) (Det.arg' (j := 1) rfl)
      refine FunDet.intro hstep (hb.mono ?_ |>.post fun c hc => ⟨?_, hc⟩)
      · have := wt_list3_le (.list []) (.nat a) (.nat xs[i])
        have := wt_nat_le a
        have := wt_nat_le xs[i]
        have : BinOp.eval .lt a xs[i] ≤ 1 := by simp only [BinOp.eval]; split_ifs <;> omega
        have : (if BinOp.eval .lt a xs[i] = 0 then Val.nat a else Val.nat xs[i]).wt ≤ B + 2 := by
          split <;> simp only [wt_nat] <;> have := len_le_self a <;> have := len_le_self xs[i] <;>
            omega
        simp only [wt_list_nil] at *
        omega
      · simp only [maxG, BinOp.eval]
        split_ifs with h1 h2 <;> simp_all <;> omega)
  rw [foldl_maxG] at hfd
  refine FunDet.intro hentry ((Det.call (Det.mk3 Det.nil (Det.var' (P := P) (env := [natList xs])
    (i := 0) rfl) (Det.nat 0)) hfd).mono ?_)
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul, List.length_map]
  have hw := wt_natList_le_sq hB hl
  have h3 := wt_list3_le (.list []) (natList xs) (.nat 0)
  have h4 := wt_nat_le (xs.foldl max 0)
  have h5 : xs.foldl max 0 ≤ B := foldl_max_le (Nat.zero_le _) hB
  have h6 : (Val.list [.list [], .list (xs.map Val.nat), .nat 0]).wt =
    (Val.list [.list [], natList xs, .nat 0]).wt := rfl
  rw [h6]
  have hw0 : (Val.nat 0).wt = 2 := by simp [wt_nat, GI.Machine.len_zero]
  simp only [wt_list_nil, hw0] at h3
  have e1 : xs.length * (30 * B + 200) ≤ 200 * (B + 1) ^ 2 := by
    have := Nat.mul_le_mul_right (30 * B + 200) hl; nlinarith
  have e2 : loopModK * (xs.length + 1) * ((Val.list [.list [], natList xs, .nat 0]).wt +
      xs.length + (B + 2) + 1) ≤ loopModK * (B + 1) * (60 * (B + 1) ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by nlinarith)
  have e3 : loopModK * (B + 1) * (60 * (B + 1) ^ 2) = 60000 * (B + 1) ^ 3 := by
    simp only [loopModK]; ring
  have e4 : (B + 1) ^ 2 ≤ (B + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  simp only [maxK]
  nlinarith

/-! ### Find an entry -/

/-- `findEq`, at base `b` (four functions): on `[j, xs]`, the index of the first entry equal to
`j`, or the length of `xs`. -/
def findEqFuns (b : ℕ) : List Expr := findFuns b (b + 3) ++ [eqTestF]

def findEqK : ℕ := 100000

theorem findIdx_natEq (j : ℕ) (xs : List ℕ) :
    (xs.map Val.nat).findIdx (natEq j) = xs.findIdx fun x => decide (x = j) := by
  rw [List.findIdx_map]
  congr 1

/-- **Find an entry.** -/
theorem findEq_spec {P : Program} {b : ℕ} (h : P.HasAt b (findEqFuns b)) {xs : List ℕ}
    {j B : ℕ} (hB : ∀ x ∈ xs, x ≤ B) (hj : j ≤ B) (hl : xs.length ≤ B) :
    FunDet P b (.list [.nat j, natList xs]) (.nat (xs.findIdx fun x => decide (x = j)))
      (findEqK * (B + 1) ^ 3) := by
  have hfind : P.HasAt b (findFuns b (b + 3)) := h.left
  have htest : P.funs[b + 3]? = some eqTestF := by
    simpa [findEqFuns, findFuns, loopFuns] using h 3 (by simp [findEqFuns, findFuns, loopFuns])
  have hT : ∀ x ∈ xs.map Val.nat, FunDet P (b + 3) (.list [.nat j, x]) (boolVal (natEq j x))
      (20 * B + 100) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact (eqTest_det htest j y).mono (by have := hB y hy; omega)
  refine (find_spec hfind (c := .nat j) (xs := xs.map Val.nat) hT).mono fun w c hw => ⟨?_, ?_⟩
  · rw [hw.1, findIdx_natEq]
  · have hc := hw.2
    simp only [List.map_map, List.length_map] at hc
    have hs : ((xs.map ((fun _ => 20 * B + 100) ∘ Val.nat))).sum =
        xs.length * (20 * B + 100) := by
      rw [show ((fun _ => 20 * B + 100) ∘ Val.nat) = fun _ => 20 * B + 100 from rfl,
        List.map_const', List.sum_replicate, smul_eq_mul]
    have e1 : (Val.list [.nat j, .list (xs.map Val.nat)]).wt =
      (Val.list [.nat j, natList xs]).wt := rfl
    rw [hs, e1] at hc
    have hw2 := wt_natList_le_sq hB hl
    have hw3 := wt_list2_le (.nat j) (natList xs)
    have hw4 := wt_nat_le j
    have h1 : xs.length * (20 * B + 100) ≤ 100 * (B + 1) ^ 2 := by
      have := Nat.mul_le_mul_right (20 * B + 100) hl; nlinarith
    have h2 : loopModK * (xs.length + 1) * ((Val.list [.nat j, natList xs]).wt +
        2 * xs.length + 3) ≤ loopModK * (B + 1) * (60 * (B + 1) ^ 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by nlinarith)
    have h3 : loopModK * (B + 1) * (60 * (B + 1) ^ 2) = 60000 * (B + 1) ^ 3 := by
      simp only [loopModK]; ring
    have h4 : (B + 1) ^ 2 ≤ (B + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [findEqK]
    nlinarith

/-! ### Indicator of an entry -/

/-- `eqInd`, at base `b` (four functions): on `[j, xs]`, the list of `[x = j]`. -/
def eqIndFuns (b : ℕ) : List Expr := mapFuns b (b + 3) ++ [eqTestF]

def eqIndK : ℕ := 100000

/-- **The indicator of an entry.** -/
theorem eqInd_spec {P : Program} {b : ℕ} (h : P.HasAt b (eqIndFuns b)) {xs : List ℕ}
    {j B : ℕ} (hB : ∀ x ∈ xs, x ≤ B) (hj : j ≤ B) (hl : xs.length ≤ B) (hB1 : 1 ≤ B) :
    FunDet P b (.list [.nat j, natList xs])
      (natList (xs.map fun x => if x = j then 1 else 0)) (eqIndK * (B + 1) ^ 3) := by
  have hmap : P.HasAt b (mapFuns b (b + 3)) := h.left
  have htest : P.funs[b + 3]? = some eqTestF := by
    simpa [eqIndFuns, mapFuns, loopFuns] using h 3 (by simp [eqIndFuns, mapFuns, loopFuns])
  have hM := map_spec hmap (c := .nat j) (xs := xs.map Val.nat)
    (R := fun x w => ∀ y : ℕ, x = .nat y → w = .nat (if y = j then 1 else 0))
    (B := fun _ => 20 * B + 100) (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      refine FunAll.mono (eqTest_det htest j y) fun w c hw => ⟨fun z hz => ?_, ?_⟩
      · cases hz
        rw [hw.1, natEq_nat]
        by_cases hyj : y = j <;> simp [hyj]
      · have := hB y hy; beta_reduce; omega)
  refine FunAll.mono hM fun w cost hw => ?_
  obtain ⟨ws, rfl, hws, hc⟩ := hw
  have hws' : ws = (xs.map fun x => if x = j then 1 else 0).map Val.nat := by
    rw [List.map_map]
    exact forall₂_map_eq (h := hws) fun a _ w hw => hw a rfl
  subst hws'
  refine ⟨rfl, ?_⟩
  simp only [List.map_map, List.length_map] at hc
  have hs : ((xs.map ((fun _ => 20 * B + 100) ∘ Val.nat))).sum =
      xs.length * (20 * B + 100) := by
    rw [show ((fun _ => 20 * B + 100) ∘ Val.nat) = fun _ => 20 * B + 100 from rfl,
      List.map_const', List.sum_replicate, smul_eq_mul]
  have e1 : (Val.list [.nat j, .list (xs.map Val.nat)]).wt =
    (Val.list [.nat j, natList xs]).wt := rfl
  have e2 : (Val.list (xs.map (Val.nat ∘ fun x => if x = j then 1 else 0))).wt =
    (natList (xs.map fun x => if x = j then 1 else 0)).wt := by
    simp [natList, List.map_map]
  rw [hs, e1, e2] at hc
  have hw1 : (natList (xs.map fun x => if x = j then 1 else 0)).wt ≤ 5 * (B + 1) ^ 2 :=
    wt_natList_le_sq (by
      intro x hx
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
      have : 1 ≤ B + 1 := by omega
      split_ifs <;> omega) (by simp; omega)
  have hw2 := wt_natList_le_sq hB hl
  have hw3 := wt_list2_le (.nat j) (natList xs)
  have hw4 := wt_nat_le j
  have h1 : xs.length * (20 * B + 100) ≤ 100 * (B + 1) ^ 2 := by
    have := Nat.mul_le_mul_right (20 * B + 100) hl; nlinarith
  have h2 : mapK * (xs.length + 1) * ((Val.list [.nat j, natList xs]).wt +
      (natList (xs.map fun x => if x = j then 1 else 0)).wt + 1) ≤
      mapK * (B + 1) * (60 * (B + 1) ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by nlinarith)
  have h3 : mapK * (B + 1) * (60 * (B + 1) ^ 2) = 60000 * (B + 1) ^ 3 := by
    simp only [mapK]; ring
  have h4 : (B + 1) ^ 2 ≤ (B + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  simp only [eqIndK]
  nlinarith

/-! ### Gather -/

/-- `gather`, at base `b` (four functions): on `[L, is]`, the list of the entries `L[i]`. -/
def gatherFuns (b : ℕ) : List Expr := mapFuns b (b + 3) ++ [composeF]

def gatherK : ℕ := 100000

/-- **Gather.** The cost is polynomial in the weight `A` of the argument. -/
theorem gather_spec {P : Program} {b : ℕ} (h : P.HasAt b (gatherFuns b)) {L : List Val}
    {is : List ℕ} (hi : ∀ i ∈ is, i < L.length) :
    FunDet P b (.list [.list L, natList is]) (.list (is.map fun i => L.getD i (.nat 0)))
      (gatherK * ((Val.list [.list L, natList is]).wt + 1) ^ 3) := by
  have hmap : P.HasAt b (mapFuns b (b + 3)) := h.left
  have hf : P.funs[b + 3]? = some composeF := by
    simpa [gatherFuns, mapFuns, loopFuns] using h 3 (by simp [gatherFuns, mapFuns, loopFuns])
  set A := (Val.list [.list L, natList is]).wt with hA
  have hLA : (Val.list L).wt < A := wt_le_wt_list (by simp)
  have hIA : (natList is).wt < A := wt_le_wt_list (by simp)
  have hlen : is.length < A := by
    have := length_lt_wt_list (is.map Val.nat)
    simp only [List.length_map] at this
    have e : (Val.list (is.map Val.nat)).wt = (natList is).wt := rfl
    omega
  have hiw : ∀ i ∈ is, i < A := by
    intro i hiis
    have := hi i hiis
    have := length_lt_wt_list L
    omega
  have hM := map_spec hmap (c := .list L) (xs := is.map Val.nat)
    (R := fun x w => ∀ y : ℕ, x = .nat y → w = L.getD y (.nat 0))
    (B := fun _ => 20 * A + 50) (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have hyL := hi y hy
      refine FunAll.intro hf ((Det.get' (Det.arg' (rest := []) (j := 0) rfl)
        (Det.arg' (j := 1) rfl) (v := L[y]) (List.getElem?_eq_getElem hyL)).post
        fun c hc => ⟨fun z hz => ?_, ?_⟩)
      · cases hz; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hyL]
      · have := wt_list2_le (.list L) (.nat y)
        have := wt_nat_le y
        have := wt_getElem_lt L y hyL
        have := hiw y hy
        beta_reduce
        omega)
  refine FunAll.mono hM fun w cost hw => ?_
  obtain ⟨ws, rfl, hws, hc⟩ := hw
  have hws' : ws = is.map fun i => L.getD i (.nat 0) := by
    have := forall₂_map_eq (l := is) (f := Val.nat) (g := fun i => L.getD i (.nat 0))
      (h := hws) fun a _ w hw => hw a rfl
    exact this
  subst hws'
  refine ⟨rfl, ?_⟩
  simp only [List.map_map, List.length_map] at hc
  have hs : ((is.map ((fun _ => 20 * A + 50) ∘ Val.nat))).sum = is.length * (20 * A + 50) := by
    rw [show ((fun _ => 20 * A + 50) ∘ Val.nat) = fun _ => 20 * A + 50 from rfl,
      List.map_const', List.sum_replicate, smul_eq_mul]
  have e1 : (Val.list [.list L, .list (is.map Val.nat)]).wt = A := rfl
  rw [hs, e1] at hc
  -- The result weighs at most `3 A²`: each entry is lighter than `L`.
  have hres : (Val.list (is.map fun i => L.getD i (.nat 0))).wt ≤ 3 * A * A + 4 := by
    have h1 := wt_list_le (is.map fun i => L.getD i (.nat 0))
    have h2 : ((is.map fun i => L.getD i (.nat 0)).map Val.wt).sum ≤ is.length * A := by
      have := List.sum_le_card_nsmul ((is.map fun i => L.getD i (.nat 0)).map Val.wt) A (by
        simp only [List.map_map, List.mem_map, Function.comp_apply, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂]
        intro i hiis
        have hyL := hi i hiis
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hyL, Option.getD_some]
        have := wt_getElem_lt L i hyL
        omega)
      simpa using this
    simp only [List.length_map] at h1
    nlinarith
  have h1 : is.length * (20 * A + 50) ≤ 70 * (A + 1) ^ 2 := by nlinarith
  have h2 : mapK * (is.length + 1) * (A + (Val.list (is.map fun i => L.getD i (.nat 0))).wt + 1)
      ≤ mapK * (A + 1) * (5 * (A + 1) ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by nlinarith)
  have h3 : mapK * (A + 1) * (5 * (A + 1) ^ 2) = 5000 * (A + 1) ^ 3 := by
    simp only [mapK]; ring
  have h4 : (A + 1) ^ 2 ≤ (A + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  simp only [gatherK]
  nlinarith

end GI.Lang

namespace GI.Lang

/-! ### Blocks of a function table -/

theorem Program.HasAt.drop {P : Program} {b : ℕ} {fs : List Expr} (h : P.HasAt b fs) (i : ℕ) :
    P.HasAt (b + i) (fs.drop i) := by
  intro j hj
  rw [List.length_drop] at hj
  have := h (i + j) (by omega)
  rw [List.getElem_drop, ← this, Nat.add_assoc]

theorem Program.HasAt.take {P : Program} {b : ℕ} {fs : List Expr} (h : P.HasAt b fs) (n : ℕ) :
    P.HasAt b (fs.take n) := by
  intro j hj
  rw [List.length_take] at hj
  rw [List.getElem_take]
  exact h j (by omega)

/-- **A block of a function table**: the functions `gs` sit at `b + i` if they are the entries
`i, …, i + |gs| - 1` of `fs`. -/
theorem Program.HasAt.block {P : Program} {b : ℕ} {fs gs : List Expr} (h : P.HasAt b fs) (i : ℕ)
    (hg : (fs.drop i).take gs.length = gs) : P.HasAt (b + i) gs :=
  hg ▸ (h.drop i).take gs.length

end GI.Lang
