module

public import Workspace.Impl.AggRectCertMath
public import Workspace.Impl.AggStructDC
public import Workspace.Impl.AggStructDesPair
public import Workspace.Impl.GenProdSq

@[expose] public section

/-!
# The certificate search as a program: the small tests

The search of `AggRectCertMath.lean` reads a table of numbers `ts` (rows of the pair colors),
held as the value `rcTV ts` (a list of `natList` rows). This file gives the small functions:

* `rcEqT` on `[[row, v], k]`: `1` if `row[k] = v` (the side tests and the matrix entries);
* `rcDiagT` on `[[T, j], y]`: `1` if `T[y][y] = j` (the fiber test);
* `rcGetT` on `[j, row]`: `row[j]` (a column of the matrix);
* `rcTwT` on `[Bm, ρ]`: `1` if at most half the rows of `Bm` equal `ρ` (the twin test).

Every comparison is an `.eq` of two numbers, whose cost is counted by the weight of its result,
so the costs are linear in a weight bound `W` of the argument, not in the size of the colors.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang
open GI.Cited (Val)
open GI.Machine (BinOp)

/-- The value of a table: its rows as `natList`s. -/
def rcTV (ts : List (List ℕ)) : Val := .list (ts.map natList)

theorem rc_natList_get {xs : List ℕ} {k : ℕ} (hk : k < xs.length) :
    (xs.map Val.nat)[k]? = some (.nat (xs.getD k 0)) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

theorem rc_tv_get {ts : List (List ℕ)} {k : ℕ} (hk : k < ts.length) :
    (ts.map natList)[k]? = some (natList (ts.getD k [])) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

theorem rc_wt_nat_lt {xs : List ℕ} {k : ℕ} (hk : k < xs.length) :
    (Val.nat (xs.getD k 0)).wt < (natList xs).wt := by
  have : Val.nat (xs.getD k 0) ∈ xs.map Val.nat := by
    rw [List.getD_eq_getElem _ _ hk]; exact List.mem_map_of_mem (List.getElem_mem hk)
  exact wt_le_wt_list this

theorem rc_wt_row_lt {ts : List (List ℕ)} {k : ℕ} (hk : k < ts.length) :
    (natList (ts.getD k [])).wt < (rcTV ts).wt := by
  have : natList (ts.getD k []) ∈ ts.map natList := by
    rw [List.getD_eq_getElem _ _ hk]; exact List.mem_map_of_mem (List.getElem_mem hk)
  exact wt_le_wt_list this

/-! ### `row[k] = v` -/

/-- On `[[row, v], k]`: `1` if `row[k] = v`. -/
def rcEqT : Expr := .arith .eq (.get (.get (arg 0) (.nat 0)) (arg 1)) (.get (arg 0) (.nat 1))

theorem rc_eqT_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some rcEqT) {xs : List ℕ} {v k : ℕ}
    (hk : k < xs.length) {W : ℕ} (hW : (Val.list [.list [natList xs, .nat v], .nat k]).wt ≤ W)
    (h20 : 20 ≤ W) :
    FunDet P f (.list [.list [natList xs, .nat v], .nat k])
      (boolVal (decide (xs.getD k 0 = v))) (20 * (W + 1)) := by
  have h1 : (Val.list [natList xs, .nat v]).wt < (Val.list [.list [natList xs, .nat v], .nat k]).wt :=
    wt_le_wt_list (by simp)
  have h2 : (Val.nat k).wt < (Val.list [.list [natList xs, .nat v], .nat k]).wt :=
    wt_le_wt_list (by simp)
  have h3 : (natList xs).wt < (Val.list [natList xs, .nat v]).wt := wt_le_wt_list (by simp)
  have h4 : (Val.nat v).wt < (Val.list [natList xs, .nat v]).wt := wt_le_wt_list (by simp)
  have h5 := rc_wt_nat_lt hk
  set vs : List Val := [.list [natList xs, .nat v], .nat k]
  have g0 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 0) rfl (W := W) hW (by omega)
    (by omega)
  have gk := StDC.arg (P := P) (rest := []) (vs := vs) (j := 1) rfl (W := W) hW (by omega)
    (by omega)
  have gX := StDC.get g0 (StDC.nat 0 (by omega)) (v := natList xs) rfl (by omega)
  have gx := StDC.get (vs := xs.map Val.nat) gX gk (rc_natList_get hk) (by omega)
  have gv := StDC.get g0 (StDC.nat 1 (by omega)) (v := .nat v) rfl (by omega)
  have ga := StDC.arith' (op := .eq) gx gv (st_eq_toNat _ _)
    (by have := Bool.toNat_le (decide (xs.getD k 0 = v)); omega)
  exact StDC.funDet hf ga (by omega)

/-! ### The fiber test `T[y][y] = j` -/

/-- On `[[T, j], y]`: `1` if `T[y][y] = j`. -/
def rcDiagT : Expr :=
  .arith .eq (.get (.get (.get (arg 0) (.nat 0)) (arg 1)) (arg 1)) (.get (arg 0) (.nat 1))

theorem rc_diagT_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some rcDiagT)
    {ts : List (List ℕ)} {j y : ℕ} (hy : y < ts.length) (hy' : y < (ts.getD y []).length) {W : ℕ}
    (hW : (Val.list [.list [rcTV ts, .nat j], .nat y]).wt ≤ W) (h20 : 20 ≤ W) :
    FunDet P f (.list [.list [rcTV ts, .nat j], .nat y])
      (boolVal (decide (rcAt ts y y = j))) (20 * (W + 1)) := by
  have h1 : (Val.list [rcTV ts, .nat j]).wt < (Val.list [.list [rcTV ts, .nat j], .nat y]).wt :=
    wt_le_wt_list (by simp)
  have h2 : (Val.nat y).wt < (Val.list [.list [rcTV ts, .nat j], .nat y]).wt :=
    wt_le_wt_list (by simp)
  have h3 : (rcTV ts).wt < (Val.list [rcTV ts, .nat j]).wt := wt_le_wt_list (by simp)
  have h4 : (Val.nat j).wt < (Val.list [rcTV ts, .nat j]).wt := wt_le_wt_list (by simp)
  have h5 := rc_wt_row_lt hy
  have h6 := rc_wt_nat_lt hy'
  set vs : List Val := [.list [rcTV ts, .nat j], .nat y]
  have g0 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 0) rfl (W := W) hW (by omega)
    (by omega)
  have gy := StDC.arg (P := P) (rest := []) (vs := vs) (j := 1) rfl (W := W) hW (by omega)
    (by omega)
  have gT := StDC.get g0 (StDC.nat 0 (by omega)) (v := rcTV ts) rfl (by omega)
  have gR := StDC.get (vs := ts.map natList) gT gy (rc_tv_get hy) (by omega)
  have gx := StDC.get (vs := (ts.getD y []).map Val.nat) gR gy (rc_natList_get hy') (by omega)
  have gv := StDC.get g0 (StDC.nat 1 (by omega)) (v := .nat j) rfl (by omega)
  have ga := StDC.arith' (op := .eq) gx gv (st_eq_toNat _ _)
    (by have := Bool.toNat_le (decide ((ts.getD y []).getD y 0 = j)); omega)
  exact StDC.funDet hf ga (by omega)

/-! ### An entry of a row -/

/-- On `[j, row]`: `row[j]`. -/
def rcGetT : Expr := .get (arg 1) (arg 0)

theorem rc_getT_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some rcGetT) {xs : List ℕ} {j : ℕ}
    (hj : j < xs.length) {W : ℕ} (hW : (Val.list [.nat j, natList xs]).wt ≤ W) (h20 : 20 ≤ W) :
    FunDet P f (.list [.nat j, natList xs]) (.nat (xs.getD j 0)) (10 * (W + 1)) := by
  have h1 : (Val.nat j).wt < (Val.list [.nat j, natList xs]).wt := wt_le_wt_list (by simp)
  have h2 : (natList xs).wt < (Val.list [.nat j, natList xs]).wt := wt_le_wt_list (by simp)
  have h5 := rc_wt_nat_lt hj
  set vs : List Val := [.nat j, natList xs]
  have g0 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 0) rfl (W := W) hW (by omega)
    (by omega)
  have g1 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 1) rfl (W := W) hW (by omega)
    (by omega)
  have gx := StDC.get (vs := xs.map Val.nat) g1 g0 (rc_natList_get hj) (by omega)
  exact StDC.funDet hf gx (by omega)

/-! ### The twin test -/

/-- On `[Bm, ρ]` (`fe`: filter with the list-equality test): `1` if at most half of the rows
of `Bm` are equal to `ρ`. -/
def rcTwT (fe : ℕ) : Expr :=
  .arith .lt (.arith .mul (.nat 2) (.length (.call fe (mk2 (arg 1) (arg 0)))))
    (.arith .add (.length (arg 0)) (.nat 1))

/-- The numbers of a list value. -/
def rcNats : Val → List ℕ
  | .list l => l.map fun v => match v with
    | .nat k => k
    | _ => 0
  | _ => []

theorem rcNats_natList (s : List ℕ) : rcNats (natList s) = s := by
  simp only [rcNats, natList, List.map_map]
  exact List.map_id'' (fun _ => rfl) s

/-- The list-equality test on values. -/
def rcNatEqV (r : List ℕ) : Val → Bool := fun v => decide (r = rcNats v)

theorem rc_filter_natEq (r : List ℕ) (bm : List (List ℕ)) :
    ((bm.map natList).filter (rcNatEqV r)).length = (bm.filter fun s => decide (r = s)).length := by
  rw [List.filter_map, List.length_map]
  congr 2
  funext s
  simp only [Function.comp_apply, rcNatEqV, rcNats_natList]

theorem rc_filter_natEq_wt (r : List ℕ) (bm : List (List ℕ)) :
    (Val.list ((bm.map natList).filter (rcNatEqV r))).wt ≤ (rcTV bm).wt :=
  wt_list_sublist List.filter_sublist

set_option maxHeartbeats 1000000 in
theorem rc_twT_spec {P : Program} {f fe en : ℕ} (hf : P.funs[f]? = some (rcTwT fe))
    (hfe : P.HasAt fe (filterFuns fe en)) (hen : P.HasAt en (eqNatsFuns en))
    (bm : List (List ℕ)) (r : List ℕ) {W : ℕ} (hW : (Val.list [rcTV bm, natList r]).wt ≤ W)
    (h20 : 20 ≤ W) :
    FunDet P f (.list [rcTV bm, natList r])
      (boolVal (rcTw bm r)) (10 ^ 6 * (W + 1) ^ 3) := by
  have h1 : (rcTV bm).wt < (Val.list [rcTV bm, natList r]).wt := wt_le_wt_list (by simp)
  have h2 : (natList r).wt < (Val.list [rcTV bm, natList r]).wt := wt_le_wt_list (by simp)
  have hrl : r.length < W := by
    have := length_lt_wt_list (r.map Val.nat)
    simp only [List.length_map] at this
    have e : (Val.list (r.map Val.nat)).wt = (natList r).wt := rfl
    omega
  have hbl : bm.length < W := by
    have := length_lt_wt_list (bm.map natList)
    simp only [List.length_map] at this
    have e : (Val.list (bm.map natList)).wt = (rcTV bm).wt := rfl
    omega
  have hc2 := wt_list2_le (natList r) (rcTV bm)
  set Z := 6 * W + 10 with hZ
  -- the filter
  have hF := filter_spec hfe (c := natList r) (xs := bm.map natList) (q := rcNatEqV r)
    (B := fun _ => loopModK * (W + 1) * (6 * W + 10)) (fun x hx => by
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
      have hsw : (natList s).wt < (rcTV bm).wt := wt_le_wt_list (List.mem_map_of_mem hs)
      have e : rcNatEqV r (natList s) = decide (r = s) := by
        simp only [rcNatEqV, rcNats_natList]
      rw [e]
      refine (eqNats_spec hen r s).mono ?_
      have := wt_list2_le (natList r) (natList s)
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega))
  set out := (bm.map natList).filter (rcNatEqV r)
  have how : (Val.list out).wt ≤ W := (rc_filter_natEq_wt r bm).trans (by omega)
  have hFd : FunDet P fe (.list [natList r, rcTV bm]) (.list out)
      (W * (loopModK * (W + 1) * (6 * W + 10)) + loopModK * (W + 1) * (8 * W + 10)) := by
    refine hF.mono fun w c ⟨h1', h2'⟩ => ⟨h1', ?_⟩
    subst h1'
    simp only [List.map_const', List.sum_replicate, List.length_map, smul_eq_mul] at h2'
    have hc : (Val.list [natList r, .list (bm.map natList)]).wt ≤ 4 * W + 6 := by
      show (Val.list [natList r, rcTV bm]).wt ≤ 4 * W + 6
      omega
    refine h2'.trans (Nat.add_le_add (Nat.mul_le_mul_right _ hbl.le)
      (Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)))
  set vs : List Val := [rcTV bm, natList r]
  have g0 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 0) rfl (W := Z) (by omega) (by omega)
    (by omega)
  have g1 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 1) rfl (W := Z) (by omega) (by omega)
    (by omega)
  have hlen : out.length = (bm.filter fun s => decide (r = s)).length := rc_filter_natEq r bm
  have hol : out.length ≤ bm.length := by
    rw [hlen]; exact List.length_filter_le _ _
  have gc := StDC.call (StDC.mk2 g1 g0 (by omega) (by omega)) hFd (by omega)
  have gl := StDC.length gc (by omega)
  have gm := StDC.arith' (op := .mul) (StDC.nat 2 (by omega)) gl rfl (by
    show 2 * out.length + 2 ≤ Z
    omega)
  have gb := StDC.length g0 (vs := bm.map natList) (by simp; omega)
  have ga := StDC.arith' (op := .add) gb (StDC.nat 1 (by omega)) rfl (by simp; omega)
  have gt := StDC.arith' (op := .lt) gm ga (z := (rcTw bm r).toNat) (by
    simp only [BinOp.eval, rcTw, ← hlen, List.length_map]
    by_cases h : 2 * out.length ≤ bm.length
    · rw [if_pos (by omega), decide_eq_true h]; rfl
    · rw [if_neg (by omega), decide_eq_false h]; rfl) (by
      have := Bool.toNat_le (rcTw bm r); omega)
  refine StDC.funDet hf gt ?_
  have hW1 : 1 ≤ W + 1 := by omega
  have e1 : W * (loopModK * (W + 1) * (6 * W + 10)) ≤ 10000 * (W + 1) ^ 3 := by
    unfold loopModK
    have : 6 * W + 10 ≤ 10 * (W + 1) := by omega
    calc W * (1000 * (W + 1) * (6 * W + 10)) ≤ (W + 1) * (1000 * (W + 1) * (10 * (W + 1))) :=
          Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ this)
      _ = 10000 * (W + 1) ^ 3 := by ring
  have e2 : loopModK * (W + 1) * (8 * W + 10) ≤ 10000 * (W + 1) ^ 3 := by
    unfold loopModK
    have : 8 * W + 10 ≤ 10 * (W + 1) := by omega
    have h3 : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    calc 1000 * (W + 1) * (8 * W + 10) ≤ 1000 * (W + 1) * (10 * (W + 1)) :=
          Nat.mul_le_mul_left _ this
      _ = 10000 * (W + 1) ^ 2 := by ring
      _ ≤ 10000 * (W + 1) ^ 3 := Nat.mul_le_mul_left _ h3
  have e3 : 100 * (Z + 1) ≤ 1000 * (W + 1) ^ 3 := by
    have : (W + 1) ≤ (W + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    omega
  nlinarith

/-! ### Maps over lists of numbers and over tables -/

/-- The number of a value. -/
def rcNatOf : Val → ℕ
  | .nat k => k
  | _ => 0

/-- **Map over a list of numbers.** -/
theorem rc_mapN {P : Program} {b f : ℕ} (h : P.HasAt b (mapFuns b f)) {c : Val} {xs : List ℕ}
    {g : ℕ → Val} {B : ℕ} (hf : ∀ x ∈ xs, FunDet P f (.list [c, .nat x]) (g x) B) :
    FunDet P b (.list [c, natList xs]) (.list (xs.map g))
      (xs.length * B + mapK * (xs.length + 1) * ((Val.list [c, natList xs]).wt +
        (Val.list (xs.map g)).wt + 1)) := by
  have hm := map_det h (c := c) (xs := xs.map Val.nat) (F := fun v => g (rcNatOf v)) (B := B)
    (fun v hv => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
      exact hf x hx)
  have e : (xs.map Val.nat).map (fun v => g (rcNatOf v)) = xs.map g := by
    rw [List.map_map]; rfl
  rw [e, List.length_map] at hm
  exact hm

/-- **Map over the rows of a table.** -/
theorem rc_mapL {P : Program} {b f : ℕ} (h : P.HasAt b (mapFuns b f)) {c : Val}
    {ts : List (List ℕ)} {g : List ℕ → Val} {B : ℕ}
    (hf : ∀ x ∈ ts, FunDet P f (.list [c, natList x]) (g x) B) :
    FunDet P b (.list [c, rcTV ts]) (.list (ts.map g))
      (ts.length * B + mapK * (ts.length + 1) * ((Val.list [c, rcTV ts]).wt +
        (Val.list (ts.map g)).wt + 1)) := by
  have hm := map_det h (c := c) (xs := ts.map natList) (F := fun v => g (rcNats v)) (B := B)
    (fun v hv => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
      simp only [rcNats_natList]
      exact hf x hx)
  have e : (ts.map natList).map (fun v => g (rcNats v)) = ts.map g := by
    rw [List.map_map]
    refine List.map_congr_left fun x _ => ?_
    simp [rcNats_natList]
  rw [e, List.length_map] at hm
  exact hm

theorem rc_wt_natList {xs : List ℕ} {B : ℕ} (h : ∀ x ∈ xs, x ≤ B) (hl : xs.length ≤ B) :
    (natList xs).wt ≤ 5 * (B + 1) ^ 2 := wt_natList_le_sq h hl

/-- A list of values of weight at most `c`. -/
theorem rc_wt_list {vs : List Val} {c L : ℕ} (h : ∀ v ∈ vs, v.wt ≤ c) (hl : vs.length ≤ L) :
    (Val.list vs).wt ≤ L * (2 * c + 1) + 4 := by
  have := wt_list_le_of vs h
  have : vs.length * (2 * c + 1) ≤ L * (2 * c + 1) := Nat.mul_le_mul_right _ hl
  omega

/-! ### A column degree -/

/-- On `[Bm, j]` (`cnt`: count; `mg`: map of `rcGetT`): the number of ones in column `j`. -/
def rcColDegF (cnt mg : ℕ) : Expr := .call cnt (mk2 (.nat 1) (.call mg (mk2 (arg 1) (arg 0))))

set_option maxHeartbeats 1000000 in
theorem rc_colDeg_spec {P : Program} {f cnt mg gt : ℕ} (hf : P.funs[f]? = some (rcColDegF cnt mg))
    (hcnt : P.HasAt cnt (countFuns cnt)) (hmg : P.HasAt mg (mapFuns mg gt))
    (hgt : P.funs[gt]? = some rcGetT) (bm : List (List ℕ)) (j : ℕ)
    (hj : ∀ row ∈ bm, j < row.length) (hb : ∀ row ∈ bm, ∀ x ∈ row, x ≤ 1) {W : ℕ}
    (hW : (Val.list [rcTV bm, .nat j]).wt ≤ W) (h20 : 20 ≤ W) :
    FunDet P f (.list [rcTV bm, .nat j]) (.nat ((rcCol bm j).count 1)) (10 ^ 6 * (W + 1) ^ 3) := by
  have h1 : (rcTV bm).wt < (Val.list [rcTV bm, .nat j]).wt := wt_le_wt_list (by simp)
  have h2 : (Val.nat j).wt < (Val.list [rcTV bm, .nat j]).wt := wt_le_wt_list (by simp)
  have hbl : bm.length < W := by
    have := length_lt_wt_list (bm.map natList)
    simp only [List.length_map] at this
    have e : (Val.list (bm.map natList)).wt = (rcTV bm).wt := rfl
    omega
  -- the column
  have hm := rc_mapL hmg (c := .nat j) (ts := bm) (g := fun row => .nat (row.getD j 0))
    (B := 10 * (5 * W + 7)) (fun row hrow => by
      have hrw : (natList row).wt < (rcTV bm).wt := wt_le_wt_list (List.mem_map_of_mem hrow)
      refine rc_getT_spec hgt (hj row hrow) (W := 5 * W + 6) ?_ (by omega)
      have := wt_list2_le (.nat j) (natList row)
      omega)
  have ecol : (bm.map fun row => Val.nat (row.getD j 0)) = (rcCol bm j).map Val.nat := by
    simp [rcCol, List.map_map]
  rw [ecol] at hm
  have hcb : ∀ x ∈ rcCol bm j, x ≤ 1 := by
    intro x hx
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.1 hx
    rw [List.getD_eq_getElem _ _ (hj row hrow)]
    exact hb row hrow _ (List.getElem_mem _)
  have hcl : (rcCol bm j).length = bm.length := by simp [rcCol]
  have hcw : (natList (rcCol bm j)).wt ≤ 5 * (W + 1) ^ 2 :=
    (rc_wt_natList (B := W) (fun x hx => (hcb x hx).trans (by omega)) (by omega)).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have hcnt' := count_spec hcnt (xs := rcCol bm j) (j := 1) (B := W)
    (fun x hx => (hcb x hx).trans (by omega)) (by omega) (by omega)
  set Z := 10 * (W + 1) ^ 2 + 20 with hZ
  have hW2 : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  set vs : List Val := [rcTV bm, .nat j]
  have g0 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 0) rfl (W := Z) (by omega)
    (by omega) (by omega)
  have g1 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 1) rfl (W := Z) (by omega)
    (by omega) (by omega)
  have hc2 := wt_list2_le (.nat j) (rcTV bm)
  have gm := StDC.call (StDC.mk2 g1 g0 (by omega) (by omega)) hm (by
    show (natList (rcCol bm j)).wt ≤ Z
    omega)
  have hc3 := wt_list2_le (.nat 1) (natList (rcCol bm j))
  have h1w := wt_nat_le 1
  have gc := StDC.call (StDC.mk2 (StDC.nat 1 (by omega)) gm (by
    show (Val.list [Val.nat 1, natList (rcCol bm j)]).wt ≤ Z
    omega) (by omega)) hcnt'
    (by have := wt_nat_le ((rcCol bm j).count 1)
        have := List.count_le_length (a := 1) (l := rcCol bm j)
        omega)
  refine StDC.funDet hf gc ?_
  -- the cost
  have hW3 : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have ew : (Val.list [Val.nat j, rcTV bm]).wt ≤ 4 * W + 6 := by omega
  have e1 : bm.length * (10 * (5 * W + 7)) ≤ 100 * (W + 1) ^ 2 := by
    have : bm.length * (10 * (5 * W + 7)) ≤ (W + 1) * (10 * (5 * (W + 1) + 7)) :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have e2 : mapK * (bm.length + 1) * ((Val.list [Val.nat j, rcTV bm]).wt +
      (Val.list ((rcCol bm j).map Val.nat)).wt + 1) ≤ 10000 * (W + 1) ^ 3 := by
    have e : (Val.list ((rcCol bm j).map Val.nat)).wt = (natList (rcCol bm j)).wt := rfl
    rw [e]
    unfold mapK
    have : 4 * W + 6 + 5 * (W + 1) ^ 2 + 1 ≤ 10 * (W + 1) ^ 2 := by nlinarith
    calc 1000 * (bm.length + 1) * ((Val.list [Val.nat j, rcTV bm]).wt +
        (natList (rcCol bm j)).wt + 1) ≤ 1000 * (W + 1) * (10 * (W + 1) ^ 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      _ = 10000 * (W + 1) ^ 3 := by ring
  have e3 : countK * (W + 1) ^ 3 = 100000 * (W + 1) ^ 3 := rfl
  have e4 : 20 * (Z + 1) ≤ 1000 * (W + 1) ^ 3 := by omega
  omega

/-! ### A row of the rectangle matrix -/

/-- On `[[D, vE, Rl], w]` (`mb`: map of `rcEqT`): the row of `w`, `[D w r = vE]` over `Rl`. -/
def rcBRowF (mb : ℕ) : Expr :=
  .call mb (mk2 (mk2 (.get (.get (arg 0) (.nat 0)) (arg 1)) (.get (arg 0) (.nat 1)))
    (.get (arg 0) (.nat 2)))

theorem rc_toNat_decide (p : Prop) [Decidable p] : (decide p).toNat = if p then 1 else 0 := by
  by_cases h : p <;> simp [h]

set_option maxHeartbeats 1000000 in
theorem rc_bRow_spec {P : Program} {f mb et : ℕ} (hf : P.funs[f]? = some (rcBRowF mb))
    (hmb : P.HasAt mb (mapFuns mb et)) (het : P.funs[et]? = some rcEqT)
    (ds : List (List ℕ)) (vE : ℕ) (rl : List ℕ) (w : ℕ) (hw : w < ds.length)
    (hr : ∀ r ∈ rl, r < (ds.getD w []).length) {W : ℕ}
    (hW : (Val.list [.list [rcTV ds, .nat vE, natList rl], .nat w]).wt ≤ W) (h20 : 20 ≤ W) :
    FunDet P f (.list [.list [rcTV ds, .nat vE, natList rl], .nat w]) (natList (rcBits ds vE rl w))
      (10 ^ 6 * (W + 1) ^ 3) := by
  set A := Val.list [.list [rcTV ds, .nat vE, natList rl], .nat w]
  have h1 : (Val.list [rcTV ds, .nat vE, natList rl]).wt < A.wt := wt_le_wt_list (by simp)
  have h2 : (Val.nat w).wt < A.wt := wt_le_wt_list (by simp)
  have h3 : (rcTV ds).wt < (Val.list [rcTV ds, .nat vE, natList rl]).wt := wt_le_wt_list (by simp)
  have h4 : (Val.nat vE).wt < (Val.list [rcTV ds, .nat vE, natList rl]).wt :=
    wt_le_wt_list (by simp)
  have h5 : (natList rl).wt < (Val.list [rcTV ds, .nat vE, natList rl]).wt :=
    wt_le_wt_list (by simp)
  have h6 := rc_wt_row_lt hw
  have hrl : rl.length < W := by
    have := length_lt_wt_list (rl.map Val.nat)
    simp only [List.length_map] at this
    have e : (Val.list (rl.map Val.nat)).wt = (natList rl).wt := rfl
    omega
  set row := ds.getD w [] with hrowdef
  have hc2 := wt_list2_le (natList row) (.nat vE)
  -- the map
  have hm := rc_mapN hmb (c := .list [natList row, .nat vE]) (xs := rl)
    (g := fun r => boolVal (decide (row.getD r 0 = vE))) (B := 20 * (12 * W + 31)) (fun r hr' => by
      have hrr := hr r hr'
      have hlen := length_lt_wt_list (row.map Val.nat)
      simp only [List.length_map] at hlen
      have e : (Val.list (row.map Val.nat)).wt = (natList row).wt := rfl
      have hrW : r < W := by omega
      refine rc_eqT_spec het hrr (W := 12 * W + 30) ?_ (by omega)
      have := wt_list2_le (.list [natList row, .nat vE]) (.nat r)
      have := wt_nat_le r
      omega)
  have eout : (rl.map fun r => boolVal (decide (row.getD r 0 = vE))) =
      (rcBits ds vE rl w).map Val.nat := by
    simp only [rcBits, List.map_map]
    refine List.map_congr_left fun r _ => ?_
    simp only [Function.comp_apply, boolVal, rc_toNat_decide, rcAt]
    rfl
  rw [eout] at hm
  have hout : (natList (rcBits ds vE rl w)).wt ≤ 5 * (W + 1) ^ 2 :=
    (rc_wt_natList (B := W) (fun x hx => by
      obtain ⟨r, -, rfl⟩ := List.mem_map.1 hx
      split <;> omega) (by simp [rcBits]; omega)).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  set Z := 10 * (W + 1) ^ 2 + 20 with hZ
  have hW2 : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  set vs : List Val := [.list [rcTV ds, .nat vE, natList rl], .nat w]
  have eA : (Val.list vs).wt = A.wt := rfl
  have g0 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 0) rfl (W := Z) (by omega)
    (by omega) (by omega)
  have g1 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 1) rfl (W := Z) (by omega)
    (by omega) (by omega)
  have gD := StDC.get g0 (StDC.nat 0 (by omega)) (v := rcTV ds) rfl (by omega)
  have gR := StDC.get (vs := ds.map natList) gD g1 (rc_tv_get hw) (by rw [← hrowdef]; omega)
  rw [← hrowdef] at gR
  have gv := StDC.get g0 (StDC.nat 1 (by omega)) (v := .nat vE) rfl (by omega)
  have gl := StDC.get g0 (StDC.nat 2 (by omega)) (v := natList rl) rfl (by omega)
  have hc3 := wt_list2_le (.list [natList row, .nat vE]) (natList rl)
  have gc := StDC.call (StDC.mk2 (StDC.mk2 gR gv (by omega) (by omega)) gl (by omega)
    (by omega)) hm (by show (natList (rcBits ds vE rl w)).wt ≤ Z; omega)
  refine StDC.funDet hf gc ?_
  have hW3 : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have e1 : rl.length * (20 * (12 * W + 31)) ≤ 1000 * (W + 1) ^ 2 := by
    have : rl.length * (20 * (12 * W + 31)) ≤ (W + 1) * (20 * (12 * (W + 1) + 31)) :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have e2 : mapK * (rl.length + 1) * ((Val.list [.list [natList row, .nat vE], natList rl]).wt +
      (Val.list ((rcBits ds vE rl w).map Val.nat)).wt + 1) ≤ 20000 * (W + 1) ^ 3 := by
    have e : (Val.list ((rcBits ds vE rl w).map Val.nat)).wt = (natList (rcBits ds vE rl w)).wt :=
      rfl
    rw [e]
    unfold mapK
    have : (Val.list [.list [natList row, .nat vE], natList rl]).wt + 5 * (W + 1) ^ 2 + 1 ≤
        20 * (W + 1) ^ 2 := by nlinarith
    calc 1000 * (rl.length + 1) * ((Val.list [.list [natList row, .nat vE], natList rl]).wt +
        (natList (rcBits ds vE rl w)).wt + 1) ≤ 1000 * (W + 1) * (20 * (W + 1) ^ 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      _ = 20000 * (W + 1) ^ 3 := by ring
  have e4 : 30 * (Z + 1) ≤ 1000 * (W + 1) ^ 3 := by omega
  omega

/-! ### A row of the fiber table -/

/-- On `[[T, F], a]` (`gth`: gather): the entries `T[a][k]`, `k ∈ F`. -/
def rcDRowF (gth : ℕ) : Expr :=
  .call gth (mk2 (.get (.get (arg 0) (.nat 0)) (arg 1)) (.get (arg 0) (.nat 1)))

set_option maxHeartbeats 1000000 in
theorem rc_dRow_spec {P : Program} {f gth : ℕ} (hf : P.funs[f]? = some (rcDRowF gth))
    (hg : P.HasAt gth (gatherFuns gth)) (ts : List (List ℕ)) (fl : List ℕ) (a : ℕ)
    (ha : a < ts.length) (hk : ∀ k ∈ fl, k < (ts.getD a []).length) {W : ℕ}
    (hW : (Val.list [.list [rcTV ts, natList fl], .nat a]).wt ≤ W) (h20 : 20 ≤ W) :
    FunDet P f (.list [.list [rcTV ts, natList fl], .nat a]) (natList (fl.map (rcAt ts a)))
      (10 ^ 8 * (W + 1) ^ 3) := by
  set A := Val.list [.list [rcTV ts, natList fl], .nat a]
  have h1 : (Val.list [rcTV ts, natList fl]).wt < A.wt := wt_le_wt_list (by simp)
  have h2 : (Val.nat a).wt < A.wt := wt_le_wt_list (by simp)
  have h3 : (rcTV ts).wt < (Val.list [rcTV ts, natList fl]).wt := wt_le_wt_list (by simp)
  have h5 : (natList fl).wt < (Val.list [rcTV ts, natList fl]).wt := wt_le_wt_list (by simp)
  have h6 := rc_wt_row_lt ha
  set row := ts.getD a [] with hrowdef
  have hgs := gather_spec hg (L := row.map Val.nat) (is := fl) (fun i hi => by
    simpa using hk i hi)
  have eout : (fl.map fun i => (row.map Val.nat).getD i (.nat 0)) = (fl.map (rcAt ts a)).map Val.nat := by
    simp only [List.map_map]
    refine List.map_congr_left fun i hi => ?_
    simp only [Function.comp_apply, rcAt]
    rw [List.getD_eq_getElem _ _ (by simpa using hk i hi),
      List.getD_eq_getElem _ _ (hk i hi)]
    simp
  rw [eout] at hgs
  have hsub : (fl.map (rcAt ts a)).map Val.nat = (fl.map (rcAt ts a)).map Val.nat := rfl
  have hout : (natList (fl.map (rcAt ts a))).wt ≤ 3 * (W + 1) ^ 2 := by
    have := rc_wt_list (vs := (fl.map (rcAt ts a)).map Val.nat) (c := W) (L := W) (by
      intro v hv
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hv
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
      have := rc_wt_nat_lt (xs := row) (hk i hi)
      have e : rcAt ts a i = row.getD i 0 := rfl
      rw [e]; omega) (by
      have := length_lt_wt_list (fl.map Val.nat)
      simp only [List.length_map] at this ⊢
      have e : (Val.list (fl.map Val.nat)).wt = (natList fl).wt := rfl
      omega)
    have e : (Val.list ((fl.map (rcAt ts a)).map Val.nat)).wt = (natList (fl.map (rcAt ts a))).wt :=
      rfl
    nlinarith
  set Z := 10 * (W + 1) ^ 2 + 20 with hZ
  have hW2 : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  set vs : List Val := [.list [rcTV ts, natList fl], .nat a]
  have eA : (Val.list vs).wt = A.wt := rfl
  have g0 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 0) rfl (W := Z) (by omega)
    (by omega) (by omega)
  have g1 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 1) rfl (W := Z) (by omega)
    (by omega) (by omega)
  have gT := StDC.get g0 (StDC.nat 0 (by omega)) (v := rcTV ts) rfl (by omega)
  have gR := StDC.get (vs := ts.map natList) gT g1 (rc_tv_get ha) (by rw [← hrowdef]; omega)
  rw [← hrowdef] at gR
  have gF := StDC.get g0 (StDC.nat 1 (by omega)) (v := natList fl) rfl (by omega)
  have hc2 := wt_list2_le (natList row) (natList fl)
  have gc := StDC.call (StDC.mk2 gR gF (by omega) (by omega)) hgs (by
    show (natList (fl.map (rcAt ts a))).wt ≤ Z
    omega)
  refine StDC.funDet hf gc ?_
  have hW3 : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have e1 : gatherK * ((Val.list [Val.list (row.map Val.nat), natList fl]).wt + 1) ^ 3 ≤
      100000 * (4 * W + 7) ^ 3 := by
    have e : (Val.list [Val.list (row.map Val.nat), natList fl]).wt =
        (Val.list [natList row, natList fl]).wt := rfl
    rw [e]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  have e2 : (4 * W + 7) ^ 3 ≤ 343 * (W + 1) ^ 3 := by
    have : 4 * W + 7 ≤ 7 * (W + 1) := by omega
    calc (4 * W + 7) ^ 3 ≤ (7 * (W + 1)) ^ 3 := Nat.pow_le_pow_left this 3
      _ = 343 * (W + 1) ^ 3 := by ring
  have e4 : 20 * (Z + 1) ≤ 1000 * (W + 1) ^ 3 := by omega
  omega

end GI.Impl
