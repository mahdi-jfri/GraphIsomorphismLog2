module

public import Workspace.Impl.AggItemC1
public import Workspace.Impl.GenProdSq
public import Workspace.Impl.AggStructDC
public import Workspace.Impl.AggCaseProg
public import Workspace.Impl.AggStructDesV

@[expose] public section

/-!
# Case 1 as a program: the data of a labeling

From the orbit labels `encFun lab` (as `orbits_spec` returns them) the program of the Case 1
item first computes the data `itDatV lab = [labels, sizes, positions, inverse positions, range]`
of the labeling (`it_dat_spec`):

* the size of the block of each point: the number of points with its label (`count`);
* the position of each point (`itpPos`): the number of points with a smaller key, by a `filter`
  with the lexicographic test `itKeyB` on (size, label, point);
* the inverse of the positions (`inv_spec`), and the list `[0, …, q-1]`.

Every map runs over `[0, …, q-1]` (`it_tab`). No primitive is called.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm)

variable {q : ℕ}

/-! ### Tabulating a function of the points -/

/-- `natList (range q)` lists the points. -/
theorem it_range_eq : natList (List.range q) = .list ((List.finRange q).map fun i : Fin q => Val.nat i.val) := by
  show Val.list ((List.range q).map Val.nat) = _
  congr 1
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp

theorem it_range_wt : (natList (List.range q)).wt ≤ 5 * (q + 1) ^ 2 :=
  wt_natList_le_sq (fun x hx => (List.mem_range.1 hx).le) (by simp)

theorem it_encFun_wt (g : Fin q → ℕ) (hg : ∀ i, g i ≤ q) : (encFun g).wt ≤ 5 * (q + 1) ^ 2 := by
  have := wt_encFun_le g hg
  nlinarith

/-- The value of a tabulated function on a point value. -/
def itTabV (g : Fin q → ℕ) : Val → Val
  | .nat i => if hi : i < q then .nat (g ⟨i, hi⟩) else .nat 0
  | _ => .nat 0

theorem itTabV_nat (g : Fin q → ℕ) (i : Fin q) : itTabV g (.nat i) = .nat (g i) := by
  simp [itTabV, i.isLt]

/-- **Tabulating a function of the points**: a map over `[0, …, q-1]` whose body returns
`g i` on point `i`. -/
theorem it_tab {P : Program} {mp f : ℕ} (h : P.HasAt mp (mapFuns mp f)) {c : Val}
    (g : Fin q → ℕ) (hg : ∀ i, g i ≤ q) {B : ℕ}
    (hf : ∀ i : Fin q, FunDet P f (.list [c, .nat i]) (.nat (g i)) B) :
    FunDet P mp (.list [c, natList (List.range q)]) (encFun g)
      (q * B + mapK * (q + 1) * (2 * c.wt + 22 * (q + 1) ^ 2)) := by
  rw [it_range_eq]
  have hm := map_det h (c := c) (xs := (List.finRange q).map fun i : Fin q => Val.nat i.val)
    (F := itTabV g) (B := B) (fun x hx => by
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
        rw [itTabV_nat]
        exact hf i)
  have e : (((List.finRange q).map fun i : Fin q => Val.nat i.val).map (itTabV g)) =
      (List.finRange q).map fun i => .nat (g i) := by
    rw [List.map_map]
    refine List.map_congr_left fun i _ => ?_
    exact itTabV_nat g i
  rw [e] at hm
  refine hm.mono ?_
  have h1 := it_range_wt (q := q)
  rw [it_range_eq] at h1
  have h2 := it_encFun_wt g hg
  have h3 := wt_list2_le c (.list ((List.finRange q).map fun i : Fin q => Val.nat i.val))
  simp only [List.length_map, List.length_finRange]
  have : mapK * (q + 1) * ((Val.list [c, .list ((List.finRange q).map fun i : Fin q => Val.nat i.val)]).wt +
      (encFun g).wt + 1) ≤ mapK * (q + 1) * (2 * c.wt + 22 * (q + 1) ^ 2) := by
    refine Nat.mul_le_mul_left _ ?_
    have : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  exact Nat.add_le_add_left this _

/-! ### Block sizes -/

/-- The size of a block is the number of points with its label. -/
theorem itpSz_eq_count (lab : Fin q → ℕ) (b : Fin q) :
    itpSz lab b = (acpLabs lab).count (lab b) := by
  classical
  rw [itpSz, itpBlk, ac_card_filter, acpLabs, List.count, List.countP_map,
    List.countP_eq_length_filter]
  congr 1

/-- On `[encFun lab, b]`: the number of points with the label of `b`. -/
def itSzB (cnt : ℕ) : Expr := .call cnt (mk2 (.get (arg 0) (arg 1)) (arg 0))

theorem it_szB_spec {P : Program} {f cnt : ℕ} (hf : P.funs[f]? = some (itSzB cnt))
    (hcnt : P.HasAt cnt (countFuns cnt)) {lab : Fin q → ℕ} (hlt : ∀ x, lab x < q) (b : Fin q) :
    FunDet P f (.list [encFun lab, .nat b]) (.nat (itpSz lab b)) (countK * (q + 1) ^ 3 + 1000 * (q + 1) ^ 3) := by
  rw [itpSz_eq_count]
  set W := 50 * (q + 1) ^ 2
  have hL := it_encFun_wt lab fun x => (hlt x).le
  have hq1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqa : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hin := wt_list2_le (encFun lab) (.nat b)
  have hb := wt_nat_le (b : ℕ)
  have hlb := wt_nat_le (lab b)
  have hlb' := hlt b
  have hw2 := wt_list2_le (.nat (lab b)) (encFun lab)
  have hc : FunDet P cnt (.list [.nat (lab b), natList (acpLabs lab)])
      (.nat ((acpLabs lab).count (lab b))) (countK * (q + 1) ^ 3) :=
    count_spec hcnt (fun x hx => acp_labs_le hlt x hx) (hlt b).le (acp_labs_length lab).le
  rw [← acp_encFun] at hc
  set env : List Val := [.list [encFun lab, .nat b]]
  have g0 : StDC P env (arg 0) (encFun lab) 3 0 W := StDC.arg rfl (by omega) (by omega) (by omega)
  have g1 : StDC P env (arg 1) (.nat b) 3 0 W := StDC.arg rfl (by omega) (by omega) (by omega)
  have gl := StDC.get (vs := (List.finRange q).map fun i => Val.nat (lab i)) g0 g1
      (encFun_getElem? lab b) (by omega)
  have g2 := StDC.mk2 gl g0 (by omega) (by omega)
  have hcnt' : (acpLabs lab).count (lab b) ≤ q := acp_count_le lab (lab b)
  have g3 := StDC.call g2 hc (by have := wt_nat_le ((acpLabs lab).count (lab b)); omega)
  refine StDC.funDet hf g3 ?_
  have : (7 + 3 + 3 + 1) * (W + 1) ≤ 1000 * (q + 1) ^ 3 := by
    have : (q + 1) ^ 2 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  omega

/-! ### Positions -/

/-- On `[[L, Sz, x], y]` (labels, sizes, two points): `1` if the key of `y` is smaller than that
of `x`, else `0`. The key is (size, label, point), compared lexicographically. -/
def itKeyB : Expr :=
  let L := Expr.get (arg 0) (.nat 0)
  let Sz := Expr.get (arg 0) (.nat 1)
  let X := Expr.get (arg 0) (.nat 2)
  let Y := arg 1
  .arith .add (.arith .lt (.get Sz Y) (.get Sz X))
    (.arith .mul (.arith .eq (.get Sz Y) (.get Sz X))
      (.arith .add (.arith .lt (.get L Y) (.get L X))
        (.arith .mul (.arith .eq (.get L Y) (.get L X)) (.arith .lt Y X))))

/-- The key comparison as a test on point values. -/
noncomputable def itKeyQ (lab : Fin q → ℕ) (x : Fin q) : Val → Bool
  | .nat y => if h : y < q then decide (itpKey lab ⟨y, h⟩ < itpKey lab x) else false
  | _ => false

theorem itKey_arith (lab : Fin q → ℕ) (x y : Fin q) :
    (if itpSz lab y < itpSz lab x then 1 else 0) +
      (if itpSz lab y = itpSz lab x then 1 else 0) *
        ((if lab y < lab x then 1 else 0) +
          (if lab y = lab x then 1 else 0) * (if (y : ℕ) < x then 1 else 0)) =
      (decide (itpKey lab y < itpKey lab x)).toNat := by
  have h := itpKey_lt_iff (lab := lab) (a := y) (b := x)
  by_cases h1 : itpSz lab y < itpSz lab x
  · have : itpKey lab y < itpKey lab x := h.2 (Or.inl h1)
    simp [h1, this, Nat.ne_of_lt h1]
  by_cases h2 : itpSz lab y = itpSz lab x
  · by_cases h3 : lab y < lab x
    · have : itpKey lab y < itpKey lab x := h.2 (Or.inr ⟨h2, Or.inl h3⟩)
      simp [h2, h3, this, Nat.ne_of_lt h3]
    by_cases h4 : lab y = lab x
    · by_cases h5 : (y : ℕ) < x
      · have : itpKey lab y < itpKey lab x := h.2 (Or.inr ⟨h2, Or.inr ⟨h4, h5⟩⟩)
        simp [h2, h4, h5, this]
      · have : ¬ itpKey lab y < itpKey lab x := fun hk => by
          rcases h.1 hk with h' | ⟨-, h' | ⟨-, h'⟩⟩ <;> contradiction
        simp [h2, h4, h5, this]
    · have : ¬ itpKey lab y < itpKey lab x := fun hk => by
        rcases h.1 hk with h' | ⟨-, h' | ⟨h', -⟩⟩ <;> contradiction
      simp [h2, h3, h4, this]
  · have : ¬ itpKey lab y < itpKey lab x := fun hk => by
      rcases h.1 hk with h' | ⟨h', -⟩ <;> contradiction
    simp [h1, h2, this]

set_option maxHeartbeats 1000000 in
theorem it_keyB_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some itKeyB)
    {lab : Fin q → ℕ} (hlt : ∀ x, lab x < q) (x y : Fin q) :
    FunDet P f (.list [.list [encFun lab, encFun (itpSz lab), .nat x], .nat y])
      (boolVal (itKeyQ lab x (.nat y))) (10 ^ 4 * (q + 1) ^ 2) := by
  have hq1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqa : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hsz : ∀ i, itpSz lab i ≤ q := fun i => by
    have := Finset.card_le_univ (itpBlk lab i); simpa [itpSz] using this
  set W := 100 * (q + 1) ^ 2
  have hL := it_encFun_wt lab fun x => (hlt x).le
  have hS := it_encFun_wt (itpSz lab) hsz
  have hx := wt_nat_le (x : ℕ)
  have hy := wt_nat_le (y : ℕ)
  have hxq := x.isLt
  have hyq := y.isLt
  have hc := wt_list3_le (encFun lab) (encFun (itpSz lab)) (.nat x)
  have hin := wt_list2_le (.list [encFun lab, encFun (itpSz lab), .nat x]) (.nat y)
  set env : List Val := [.list [.list [encFun lab, encFun (itpSz lab), .nat x], .nat y]]
  have g0 := StDC.arg (P := P) (rest := []) (vs := [.list [encFun lab, encFun (itpSz lab), .nat x],
    .nat y]) (j := 0) rfl (W := W) (by omega) (by omega) (by omega)
  have gY := StDC.arg (P := P) (rest := []) (vs := [.list [encFun lab, encFun (itpSz lab), .nat x],
    .nat y]) (j := 1) rfl (W := W) (by omega) (by omega) (by omega)
  have gL := StDC.get g0 (StDC.nat 0 (by omega)) (v := encFun lab) rfl (by omega)
  have gS := StDC.get g0 (StDC.nat 1 (by omega)) (v := encFun (itpSz lab)) rfl (by omega)
  have gX := StDC.get g0 (StDC.nat 2 (by omega)) (v := .nat x) rfl (by omega)
  have hsy := hsz y
  have hsx := hsz x
  have hly := hlt y
  have hlx := hlt x
  have sY := StDC.get (vs := (List.finRange q).map fun i => Val.nat (itpSz lab i)) gS gY
    (encFun_getElem? _ y) (by have := wt_nat_le (itpSz lab y); omega)
  have sX := StDC.get (vs := (List.finRange q).map fun i => Val.nat (itpSz lab i)) gS gX
    (encFun_getElem? _ x) (by have := wt_nat_le (itpSz lab x); omega)
  have lY := StDC.get (vs := (List.finRange q).map fun i => Val.nat (lab i)) gL gY
    (encFun_getElem? _ y) (by have := wt_nat_le (lab y); omega)
  have lX := StDC.get (vs := (List.finRange q).map fun i => Val.nat (lab i)) gL gX
    (encFun_getElem? _ x) (by have := wt_nat_le (lab x); omega)
  have a1 := StDC.arith' (op := .lt) sY sX rfl (by simp only [GI.Machine.BinOp.eval]; split_ifs <;> omega)
  have a2 := StDC.arith' (op := .eq) sY sX rfl (by simp only [GI.Machine.BinOp.eval]; split_ifs <;> omega)
  have a3 := StDC.arith' (op := .lt) lY lX rfl (by simp only [GI.Machine.BinOp.eval]; split_ifs <;> omega)
  have a4 := StDC.arith' (op := .eq) lY lX rfl (by simp only [GI.Machine.BinOp.eval]; split_ifs <;> omega)
  have a5 := StDC.arith' (op := .lt) gY gX rfl (by simp only [GI.Machine.BinOp.eval]; split_ifs <;> omega)
  have a6 := StDC.arith' (op := .mul) a4 a5 rfl (by simp only [GI.Machine.BinOp.eval]; split_ifs <;> omega)
  have a7 := StDC.arith' (op := .add) a3 a6 rfl (by simp only [GI.Machine.BinOp.eval]; split_ifs <;> omega)
  have a8 := StDC.arith' (op := .mul) a2 a7 rfl (by simp only [GI.Machine.BinOp.eval]; split_ifs <;> omega)
  have a9 := StDC.arith' (op := .add) a1 a8 rfl (by simp only [GI.Machine.BinOp.eval]; split_ifs <;> omega)
  have e : itKeyQ lab x (.nat y) = decide (itpKey lab y < itpKey lab x) := by
    simp [itKeyQ, y.isLt]
  rw [e, boolVal, ← itKey_arith]
  refine StDC.funDet hf a9 ?_
  omega

/-- The key test filters the points with a smaller key. -/
theorem it_filter_key (lab : Fin q → ℕ) (x : Fin q) :
    (((List.range q).map Val.nat).filter (itKeyQ lab x)).length = itpPos lab x := by
  classical
  have e1 : (List.range q).map Val.nat = (List.finRange q).map fun i : Fin q => Val.nat i.val := by
    have := it_range_eq (q := q); rw [natList] at this; exact Val.list.inj this
  rw [e1, List.filter_map, List.length_map, itpPos, ac_card_filter]
  congr 1
  refine List.filter_congr fun i _ => ?_
  simp [itKeyQ, i.isLt]

/-- On `[[L, Sz, R], x]` (labels, sizes, the points): the position of `x`. -/
def itPosB (flt : ℕ) : Expr :=
  .length (.call flt (mk2 (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (arg 1))
    (.get (arg 0) (.nat 2))))

set_option maxHeartbeats 1000000 in
theorem it_posB_spec {P : Program} {f flt kb : ℕ} (hf : P.funs[f]? = some (itPosB flt))
    (hflt : P.HasAt flt (filterFuns flt kb)) (hkb : P.funs[kb]? = some itKeyB)
    {lab : Fin q → ℕ} (hlt : ∀ x, lab x < q) (x : Fin q) :
    FunDet P f (.list [.list [encFun lab, encFun (itpSz lab), natList (List.range q)], .nat x])
      (.nat (itpPos lab x)) (10 ^ 6 * (q + 1) ^ 3) := by
  have hq1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqa : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hq3 : (q + 1) ^ 2 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hsz : ∀ i, itpSz lab i ≤ q := fun i => by
    have := Finset.card_le_univ (itpBlk lab i); simpa [itpSz] using this
  set W := 100 * (q + 1) ^ 2
  have hL := it_encFun_wt lab fun x => (hlt x).le
  have hS := it_encFun_wt (itpSz lab) hsz
  have hR := it_range_wt (q := q)
  have hx := wt_nat_le (x : ℕ)
  have hxq := x.isLt
  have hc := wt_list3_le (encFun lab) (encFun (itpSz lab)) (natList (List.range q))
  have hin := wt_list2_le (.list [encFun lab, encFun (itpSz lab), natList (List.range q)]) (.nat x)
  have hc3 := wt_list3_le (encFun lab) (encFun (itpSz lab)) (.nat x)
  have hfi := wt_list2_le (.list [encFun lab, encFun (itpSz lab), .nat x]) (natList (List.range q))
  set vs : List Val := [.list [encFun lab, encFun (itpSz lab), natList (List.range q)], .nat x]
  have g0 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 0) rfl (W := W) (by omega) (by omega)
    (by omega)
  have gX := StDC.arg (P := P) (rest := []) (vs := vs) (j := 1) rfl (W := W) (by omega) (by omega)
    (by omega)
  have gL := StDC.get g0 (StDC.nat 0 (by omega)) (v := encFun lab) rfl (by omega)
  have gS := StDC.get g0 (StDC.nat 1 (by omega)) (v := encFun (itpSz lab)) rfl (by omega)
  have gR := StDC.get g0 (StDC.nat 2 (by omega)) (v := natList (List.range q)) rfl (by omega)
  have m3 := StDC.mk3 gL gS gX (by omega) (by omega)
  have m2 := StDC.mk2 m3 gR (by omega) (by omega)
  -- the filter
  have hF := filter_spec hflt (c := .list [encFun lab, encFun (itpSz lab), .nat x])
    (xs := (List.range q).map Val.nat) (q := itKeyQ lab x) (B := fun _ => 10 ^ 4 * (q + 1) ^ 2)
    (fun v hv => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hv
      exact it_keyB_spec hkb hlt x ⟨y, List.mem_range.1 hy⟩)
  set out := ((List.range q).map Val.nat).filter (itKeyQ lab x)
  have hlen : ((List.range q).map Val.nat).length = q := by simp
  have hol : out.length ≤ q := (List.length_filter_le _ _).trans hlen.le
  have howt : (Val.list out).wt ≤ 5 * (q + 1) ^ 2 := by
    have h1 := wt_list_le_of out (c := q + 2) (fun v hv => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (List.mem_of_mem_filter hv)
      have := wt_nat_le y; have := List.mem_range.1 hy; omega)
    have h2 : out.length * (2 * (q + 2) + 1) ≤ q * (2 * (q + 2) + 1) := Nat.mul_le_mul_right _ hol
    nlinarith
  have hFd : FunDet P flt (.list [.list [encFun lab, encFun (itpSz lab), .nat x],
      natList (List.range q)]) (.list out) (q * (10 ^ 4 * (q + 1) ^ 2) +
        loopModK * (q + 1) * (W + q + 5 * (q + 1) ^ 2 + 1)) := by
    refine hF.mono fun w c ⟨h1, h2⟩ => ⟨h1, ?_⟩
    subst h1
    have hsum : (((List.range q).map Val.nat).map fun _ => 10 ^ 4 * (q + 1) ^ 2).sum =
        q * (10 ^ 4 * (q + 1) ^ 2) := by
      simp [Function.comp_def, List.map_const', List.sum_replicate]
    rw [hsum, hlen] at h2
    refine h2.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _)
    have : (Val.list [.list [encFun lab, encFun (itpSz lab), .nat x],
        .list ((List.range q).map Val.nat)]).wt ≤ W := by
      show (Val.list [.list [encFun lab, encFun (itpSz lab), .nat x], natList (List.range q)]).wt ≤ W
      omega
    omega
  have c1 := StDC.call m2 hFd (by omega)
  have c2 := StDC.length c1 (by omega)
  rw [← it_filter_key lab x]
  refine StDC.funDet hf c2 ?_
  have : loopModK * (q + 1) * (W + q + 5 * (q + 1) ^ 2 + 1) ≤ 2 * 10 ^ 5 * (q + 1) ^ 3 := by
    have : W + q + 5 * (q + 1) ^ 2 + 1 ≤ 200 * (q + 1) ^ 2 := by omega
    calc loopModK * (q + 1) * (W + q + 5 * (q + 1) ^ 2 + 1)
        ≤ 1000 * (q + 1) * (200 * (q + 1) ^ 2) := Nat.mul_le_mul_left _ this
      _ = 2 * 10 ^ 5 * (q + 1) ^ 3 := by ring
  have : q * (10 ^ 4 * (q + 1) ^ 2) ≤ 10 ^ 4 * (q + 1) ^ 3 := by
    calc q * (10 ^ 4 * (q + 1) ^ 2) ≤ (q + 1) * (10 ^ 4 * (q + 1) ^ 2) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 10 ^ 4 * (q + 1) ^ 3 := by ring
  omega

/-! ### The data of a labeling -/

/-- On `encFun lab`: `[labels, sizes, positions, inverse positions, [0, …, q-1]]`. -/
def itDatF (rng mpS mpP inv : ℕ) : Expr :=
  .letE (.call rng (.length (.var 0)))
    (.letE (.call mpS (mk2 (.var 0) (.var 1)))
      (.letE (.call mpP (mk2 (mk3 (.var 0) (.var 2) (.var 1)) (.var 1)))
        (.letE (.call inv (.var 3))
          (.snoc (mk4 (.var 0) (.var 2) (.var 3) (.var 4)) (.var 1)))))

/-- The data of a labeling. -/
noncomputable def itDatV (lab : Fin q → ℕ) : Val :=
  .list [encFun lab, encFun (itpSz lab), encPerm (itpPosE lab), encPerm (itpPosE lab)⁻¹,
    natList (List.range q)]

/-- The cost bound of `itDatF`. -/
def itDatC (q : ℕ) : ℕ := 10 ^ 7 * (q + 1) ^ 4

theorem itpSz_le (lab : Fin q → ℕ) (i : Fin q) : itpSz lab i ≤ q := by
  have := Finset.card_le_univ (itpBlk lab i); simpa [itpSz] using this

theorem it_datV_wt (lab : Fin q → ℕ) (hlt : ∀ x, lab x < q) :
    (itDatV lab).wt ≤ 60 * (q + 1) ^ 2 := by
  have hq1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h := wt_list_le_of [encFun lab, encFun (itpSz lab), encPerm (itpPosE lab),
    encPerm (itpPosE lab)⁻¹, natList (List.range q)] (c := 5 * (q + 1) ^ 2) (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      · exact it_encFun_wt lab fun x => (hlt x).le
      · exact it_encFun_wt _ (itpSz_le lab)
      · have := wt_encPerm_le (itpPosE lab); omega
      · have := wt_encPerm_le (itpPosE lab)⁻¹; omega
      · exact it_range_wt)
  simp only [List.length_cons, List.length_nil] at h
  rw [itDatV]; omega

set_option maxHeartbeats 2000000 in
/-- **The data of a labeling, as a program.** -/
theorem it_dat_spec {P : Program} {f rng mpS sz cnt mpP pb flt kb inv : ℕ}
    (hf : P.funs[f]? = some (itDatF rng mpS mpP inv)) (hrng : P.HasAt rng (rangeFuns rng))
    (hmpS : P.HasAt mpS (mapFuns mpS sz)) (hsz : P.funs[sz]? = some (itSzB cnt))
    (hcnt : P.HasAt cnt (countFuns cnt)) (hmpP : P.HasAt mpP (mapFuns mpP pb))
    (hpb : P.funs[pb]? = some (itPosB flt)) (hflt : P.HasAt flt (filterFuns flt kb))
    (hkb : P.funs[kb]? = some itKeyB) (hinv : P.HasAt inv (invFuns inv))
    {lab : Fin q → ℕ} (hlt : ∀ x, lab x < q) :
    FunDet P f (encFun lab) (itDatV lab) (itDatC q) := by
  have hq1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqa : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hq3 : (q + 1) ^ 2 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hq4 : (q + 1) ^ 3 ≤ (q + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  set W := 100 * (q + 1) ^ 2
  have hL := it_encFun_wt lab fun x => (hlt x).le
  have hS := it_encFun_wt (itpSz lab) (itpSz_le lab)
  have hR := it_range_wt (q := q)
  have hP := wt_encPerm_le (itpPosE lab)
  have hI := wt_encPerm_le (itpPosE lab)⁻¹
  have hD := it_datV_wt lab hlt
  have hlen : (encFun lab) = .list ((List.finRange q).map fun i => Val.nat (lab i)) := rfl
  -- the calls
  have cR : FunDet P rng (.nat q) (natList (List.range q)) (10000 * (q + 1) ^ 3) :=
    st_range_det hrng q
  have cS := it_tab hmpS (c := encFun lab) (itpSz lab) (itpSz_le lab)
    (fun i => it_szB_spec hsz hcnt hlt i)
  have cP := it_tab hmpP (c := .list [encFun lab, encFun (itpSz lab), natList (List.range q)])
    (itpPos lab) (fun i => (itpPos_lt i).le) (fun i => it_posB_spec hpb hflt hkb hlt i)
  have cI := inv_spec hinv (itpPosE lab)
  have e1 : encFun (itpPos lab) = encPerm (itpPosE lab) := rfl
  rw [e1] at cP
  -- the body
  have d0 : StDC P [encFun lab] (.var 0) (encFun lab) 1 0 W := StDC.var' rfl (by omega)
  have dl := StDC.length (vs := (List.finRange q).map fun i => Val.nat (lab i)) d0
    (by simp; omega)
  simp only [List.length_map, List.length_finRange] at dl
  have d1 := StDC.call dl cR (by omega)
  set E1 : List Val := [encFun lab, natList (List.range q)]
  have v0 : StDC P E1 (.var 0) (encFun lab) 1 0 W := StDC.var' rfl (by omega)
  have v1 : StDC P E1 (.var 1) (natList (List.range q)) 1 0 W := StDC.var' rfl (by omega)
  have hw1 := wt_list2_le (encFun lab) (natList (List.range q))
  have d2 := StDC.call (StDC.mk2 v0 v1 (by omega) (by omega)) cS (by omega)
  set E2 : List Val := [encFun lab, natList (List.range q), encFun (itpSz lab)]
  have u0 : StDC P E2 (.var 0) (encFun lab) 1 0 W := StDC.var' rfl (by omega)
  have u1 : StDC P E2 (.var 1) (natList (List.range q)) 1 0 W := StDC.var' rfl (by omega)
  have u2 : StDC P E2 (.var 2) (encFun (itpSz lab)) 1 0 W := StDC.var' rfl (by omega)
  have hw3 := wt_list3_le (encFun lab) (encFun (itpSz lab)) (natList (List.range q))
  have hw4 := wt_list2_le (.list [encFun lab, encFun (itpSz lab), natList (List.range q)])
    (natList (List.range q))
  have d3 := StDC.call (StDC.mk2 (StDC.mk3 u0 u2 u1 (by omega) (by omega)) u1 (by omega)
    (by omega)) cP (by omega)
  set E3 : List Val := [encFun lab, natList (List.range q), encFun (itpSz lab),
    encPerm (itpPosE lab)]
  have t3 : StDC P E3 (.var 3) (encPerm (itpPosE lab)) 1 0 W := StDC.var' rfl (by omega)
  have d4 := StDC.call t3 cI (by omega)
  set E4 : List Val := [encFun lab, natList (List.range q), encFun (itpSz lab),
    encPerm (itpPosE lab), encPerm (itpPosE lab)⁻¹]
  have s0 : StDC P E4 (.var 0) (encFun lab) 1 0 W := StDC.var' rfl (by omega)
  have s1 : StDC P E4 (.var 1) (natList (List.range q)) 1 0 W := StDC.var' rfl (by omega)
  have s2 : StDC P E4 (.var 2) (encFun (itpSz lab)) 1 0 W := StDC.var' rfl (by omega)
  have s3 : StDC P E4 (.var 3) (encPerm (itpPosE lab)) 1 0 W := StDC.var' rfl (by omega)
  have s4 : StDC P E4 (.var 4) (encPerm (itpPosE lab)⁻¹) 1 0 W := StDC.var' rfl (by omega)
  have hw5 := wt_list4_le (encFun lab) (encFun (itpSz lab)) (encPerm (itpPosE lab))
    (encPerm (itpPosE lab)⁻¹)
  have hD' : (Val.list ([encFun lab, encFun (itpSz lab), encPerm (itpPosE lab),
      encPerm (itpPosE lab)⁻¹] ++ [natList (List.range q)])).wt ≤ W := by
    show (itDatV lab).wt ≤ W; omega
  have d5 := StDC.snoc (StDC.mk4 s0 s2 s3 s4 (by omega) (by omega)) s1 hD'
  have dall := StDC.letE d1 (StDC.letE d2 (StDC.letE d3 (StDC.letE d4 d5 (by omega))
    (by omega)) (by omega)) (by omega)
  refine StDC.funDet hf dall ?_
  -- the cost
  have hc1 : q * (countK * (q + 1) ^ 3 + 1000 * (q + 1) ^ 3) ≤ 101000 * (q + 1) ^ 4 := by
    calc q * (countK * (q + 1) ^ 3 + 1000 * (q + 1) ^ 3)
        ≤ (q + 1) * (101000 * (q + 1) ^ 3) := by
          simp only [countK]; exact Nat.mul_le_mul (by omega) (by omega)
      _ = 101000 * (q + 1) ^ 4 := by ring
  have hc2 : q * (10 ^ 6 * (q + 1) ^ 3) ≤ 10 ^ 6 * (q + 1) ^ 4 := by
    calc q * (10 ^ 6 * (q + 1) ^ 3) ≤ (q + 1) * (10 ^ 6 * (q + 1) ^ 3) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 10 ^ 6 * (q + 1) ^ 4 := by ring
  have hm1 : mapK * (q + 1) * (2 * (encFun lab).wt + 22 * (q + 1) ^ 2) ≤ 32000 * (q + 1) ^ 3 := by
    calc mapK * (q + 1) * (2 * (encFun lab).wt + 22 * (q + 1) ^ 2)
        ≤ 1000 * (q + 1) * (32 * (q + 1) ^ 2) := Nat.mul_le_mul_left _ (by omega)
      _ = 32000 * (q + 1) ^ 3 := by ring
  have hm2 : mapK * (q + 1) *
      (2 * (Val.list [encFun lab, encFun (itpSz lab), natList (List.range q)]).wt +
        22 * (q + 1) ^ 2) ≤ 200000 * (q + 1) ^ 3 := by
    calc mapK * (q + 1) *
          (2 * (Val.list [encFun lab, encFun (itpSz lab), natList (List.range q)]).wt +
            22 * (q + 1) ^ 2)
        ≤ 1000 * (q + 1) * (200 * (q + 1) ^ 2) := Nat.mul_le_mul_left _ (by omega)
      _ = 200000 * (q + 1) ^ 3 := by ring
  have hiv : invK * (q + 1) ^ 4 = 100000 * (q + 1) ^ 4 := rfl
  unfold itDatC
  omega

end GI.Impl
