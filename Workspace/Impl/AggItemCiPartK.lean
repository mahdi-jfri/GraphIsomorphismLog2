import Workspace.Impl.AggItemCiPart
import Workspace.Impl.AggItemC1Top

/-!
# The colored-partition item as a program: positions and centers

The program of `AggItemCiPart.lean` reads a coloring `f` as `encFun f`. Its values are colors,
which may be larger than `q`, so the costs here are bounded by the weight `M` of `encFun f`
(with `q ≤ M`), not by `q`.

* `itci_keyB_spec`: the key test of Case 1, `itKeyB`, on `[[F, F, x], y]` compares `y` and `x`
  in the order by (color, point), since the size list is `F` itself.
* `itci_posB_spec`, `itci_pos_tab`: the position of a point, and the table `encPerm (itciPosE f)`.
* `itci_eqT_spec`, `itci_cB_spec`, `itci_c_tab`: the center of a point (the first point of the
  same color, by `find`), and the table `encFun (itciCN f)`.
* `itci_chkT_spec`, `itci_chk_spec`: whether a permutation maps `fX` to `fY`, by `all`.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens)

variable {q : ℕ}

theorem itci_fwt (f : Fin q → ℕ) (i : Fin q) : (Val.nat (f i)).wt < (encFun f).wt :=
  wt_le_wt_list (List.mem_map_of_mem (List.mem_finRange i))

theorem itci_q_le_wt (f : Fin q → ℕ) : q ≤ (encFun f).wt := by
  have := length_lt_wt_list ((List.finRange q).map fun i => Val.nat (f i))
  simp only [List.length_map, List.length_finRange] at this
  exact this.le

theorem itci_bool_toNat (b : Bool) : b.toNat + 2 ≤ 3 := by cases b <;> decide

/-! ### The key test and the positions -/

/-- The key test as a test on point values. -/
def itciKQ (f : Fin q → ℕ) (x : Fin q) : Val → Bool
  | .nat y => if h : y < q then
      decide (f ⟨y, h⟩ < f x ∨ (f ⟨y, h⟩ = f x ∧ (⟨y, h⟩ : Fin q) < x)) else false
  | _ => false

theorem itci_key_arith (f : Fin q → ℕ) (x y : Fin q) :
    (if f y < f x then 1 else 0) + (if f y = f x then 1 else 0) *
        ((if f y < f x then 1 else 0) +
          (if f y = f x then 1 else 0) * (if (y : ℕ) < x then 1 else 0)) =
      (decide (f y < f x ∨ (f y = f x ∧ y < x))).toNat := by
  by_cases h1 : f y < f x
  · simp [h1, Nat.ne_of_lt h1]
  · by_cases h2 : f y = f x
    · by_cases h3 : (y : ℕ) < x
      · have h3' : y < x := h3
        simp [h2, h3, h3']
      · have h3' : ¬ y < x := h3
        simp [h2, h3, h3']
    · simp [h1, h2]

/-- The cost of one key test. -/
def itciKC (M : ℕ) : ℕ := 10 ^ 4 * (M + 2)

set_option maxHeartbeats 1000000 in
/-- **The key test**: `itKeyB` on `[[F, F, x], y]`. -/
theorem itci_keyB_spec {P : Program} {kb : ℕ} (hkb : P.funs[kb]? = some itKeyB)
    (f : Fin q → ℕ) {M : ℕ} (hM : (encFun f).wt ≤ M) (x y : Fin q) :
    FunDet P kb (.list [.list [encFun f, encFun f, .nat x], .nat y])
      (boolVal (itciKQ f x (.nat y))) (itciKC M) := by
  have hqM := (itci_q_le_wt f).trans hM
  set W := 20 * (M + 2)
  have hx := wt_nat_le (x : ℕ)
  have hy := wt_nat_le (y : ℕ)
  have hxq := x.isLt
  have hyq := y.isLt
  have hc := wt_list3_le (encFun f) (encFun f) (.nat x)
  have hin := wt_list2_le (.list [encFun f, encFun f, .nat x]) (.nat y)
  have hfy := itci_fwt f y
  have hfx := itci_fwt f x
  set vs : List Val := [.list [encFun f, encFun f, .nat x], .nat y]
  have g0 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 0) rfl (W := W) (by omega)
    (by omega) (by omega)
  have gY := StDC.arg (P := P) (rest := []) (vs := vs) (j := 1) rfl (W := W) (by omega)
    (by omega) (by omega)
  have gL := StDC.get g0 (StDC.nat 0 (by omega)) (v := encFun f) rfl (by omega)
  have gS := StDC.get g0 (StDC.nat 1 (by omega)) (v := encFun f) rfl (by omega)
  have gX := StDC.get g0 (StDC.nat 2 (by omega)) (v := .nat x) rfl (by omega)
  have sY := StDC.get (vs := (List.finRange q).map fun i => Val.nat (f i)) gS gY
    (encFun_getElem? _ y) (by omega)
  have sX := StDC.get (vs := (List.finRange q).map fun i => Val.nat (f i)) gS gX
    (encFun_getElem? _ x) (by omega)
  have lY := StDC.get (vs := (List.finRange q).map fun i => Val.nat (f i)) gL gY
    (encFun_getElem? _ y) (by omega)
  have lX := StDC.get (vs := (List.finRange q).map fun i => Val.nat (f i)) gL gX
    (encFun_getElem? _ x) (by omega)
  have hw01 : ∀ z, z ≤ 1 → (Val.nat z).wt ≤ W := fun z hz => by
    have := wt_nat_le z; omega
  have a1 := StDC.arith (op := .lt) sY sX rfl (hw01 _ (by
    simp only [GI.Machine.BinOp.eval]; split_ifs <;> omega))
  have a2 := StDC.arith (op := .eq) sY sX rfl (hw01 _ (by
    simp only [GI.Machine.BinOp.eval]; split_ifs <;> omega))
  have a3 := StDC.arith (op := .lt) lY lX rfl (hw01 _ (by
    simp only [GI.Machine.BinOp.eval]; split_ifs <;> omega))
  have a4 := StDC.arith (op := .eq) lY lX rfl (hw01 _ (by
    simp only [GI.Machine.BinOp.eval]; split_ifs <;> omega))
  have a5 := StDC.arith (op := .lt) gY gX rfl (hw01 _ (by
    simp only [GI.Machine.BinOp.eval]; split_ifs <;> omega))
  have a6 := StDC.arith (op := .mul) a4 a5 rfl (hw01 _ (by
    simp only [GI.Machine.BinOp.eval]; split_ifs <;> omega))
  have a7 := StDC.arith (op := .add) a3 a6 rfl (hw01 _ (by
    simp only [GI.Machine.BinOp.eval]; split_ifs <;> simp_all))
  have a8 := StDC.arith (op := .mul) a2 a7 rfl (hw01 _ (by
    simp only [GI.Machine.BinOp.eval]; split_ifs <;> simp_all))
  have a9 := StDC.arith (op := .add) a1 a8 rfl (hw01 _ (by
    simp only [GI.Machine.BinOp.eval]; split_ifs <;> simp_all))
  have e : itciKQ f x (.nat y) = decide (f y < f x ∨ (f y = f x ∧ y < x)) := by
    simp [itciKQ, y.isLt]
  rw [e, boolVal, ← itci_key_arith]
  refine StDC.funDet (P := P) hkb a9 ?_
  unfold itciKC
  omega

/-- The key test filters the points before `x`. -/
theorem itci_filter_key (f : Fin q → ℕ) (x : Fin q) :
    (((List.range q).map Val.nat).filter (itciKQ f x)).length = itciPos f x := by
  classical
  have e1 : (List.range q).map Val.nat = (List.finRange q).map fun i : Fin q => Val.nat i.val := by
    have := it_range_eq (q := q); rw [natList] at this; exact Val.list.inj this
  rw [e1, List.filter_map, List.length_map, itciPos, ac_card_filter]
  congr 1
  refine List.filter_congr fun i _ => ?_
  simp [itciKQ, i.isLt]

/-- The cost of one position. -/
def itciPC (M : ℕ) : ℕ := 10 ^ 7 * (M + 2) ^ 3

set_option maxHeartbeats 1000000 in
/-- **The position of a point**: `itPosB` on `[[F, F, R], x]`. -/
theorem itci_posB_spec {P : Program} {pb flt kb : ℕ} (hpb : P.funs[pb]? = some (itPosB flt))
    (hflt : P.HasAt flt (filterFuns flt kb)) (hkb : P.funs[kb]? = some itKeyB)
    (f : Fin q → ℕ) {M : ℕ} (hM : (encFun f).wt ≤ M) (x : Fin q) :
    FunDet P pb (.list [.list [encFun f, encFun f, natList (List.range q)], .nat x])
      (.nat (itciPos f x)) (itciPC M) := by
  have hqM := (itci_q_le_wt f).trans hM
  have hR := it_range_wt (q := q)
  have hq1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqM2 : (q + 1) ^ 2 ≤ (M + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  set W := 100 * (M + 2) ^ 2
  have hM2 : M + 2 ≤ (M + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hx := wt_nat_le (x : ℕ)
  have hxq := x.isLt
  have hc := wt_list3_le (encFun f) (encFun f) (natList (List.range q))
  have hin := wt_list2_le (.list [encFun f, encFun f, natList (List.range q)]) (.nat x)
  have hc3 := wt_list3_le (encFun f) (encFun f) (.nat x)
  have hfi := wt_list2_le (.list [encFun f, encFun f, .nat x]) (natList (List.range q))
  set vs : List Val := [.list [encFun f, encFun f, natList (List.range q)], .nat x]
  have g0 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 0) rfl (W := W) (by omega) (by omega)
    (by omega)
  have gX := StDC.arg (P := P) (rest := []) (vs := vs) (j := 1) rfl (W := W) (by omega) (by omega)
    (by omega)
  have gL := StDC.get g0 (StDC.nat 0 (by omega)) (v := encFun f) rfl (by omega)
  have gS := StDC.get g0 (StDC.nat 1 (by omega)) (v := encFun f) rfl (by omega)
  have gR := StDC.get g0 (StDC.nat 2 (by omega)) (v := natList (List.range q)) rfl (by omega)
  have m3 := StDC.mk3 gL gS gX (by omega) (by omega)
  have m2 := StDC.mk2 m3 gR (by omega) (by omega)
  have hF := filter_spec hflt (c := .list [encFun f, encFun f, .nat x])
    (xs := (List.range q).map Val.nat) (q := itciKQ f x) (B := fun _ => itciKC M)
    (fun v hv => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hv
      exact itci_keyB_spec hkb f hM x ⟨y, List.mem_range.1 hy⟩)
  set out := ((List.range q).map Val.nat).filter (itciKQ f x)
  have hlen : ((List.range q).map Val.nat).length = q := by simp
  have hol : out.length ≤ q := (List.length_filter_le _ _).trans hlen.le
  have howt : (Val.list out).wt ≤ 5 * (q + 1) ^ 2 := by
    have h1 := wt_list_le_of out (c := q + 2) (fun v hv => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (List.mem_of_mem_filter hv)
      have := wt_nat_le y; have := List.mem_range.1 hy; omega)
    have h2 : out.length * (2 * (q + 2) + 1) ≤ q * (2 * (q + 2) + 1) := Nat.mul_le_mul_right _ hol
    nlinarith
  have hFd : FunDet P flt (.list [.list [encFun f, encFun f, .nat x],
      natList (List.range q)]) (.list out) (q * itciKC M +
        loopModK * (q + 1) * (W + q + 5 * (q + 1) ^ 2 + 1)) := by
    refine hF.mono fun w c ⟨h1, h2⟩ => ⟨h1, ?_⟩
    subst h1
    have hsum : (((List.range q).map Val.nat).map fun _ => itciKC M).sum = q * itciKC M := by
      simp [Function.comp_def, List.map_const', List.sum_replicate]
    rw [hsum, hlen] at h2
    refine h2.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _)
    have : (Val.list [.list [encFun f, encFun f, .nat x],
        .list ((List.range q).map Val.nat)]).wt ≤ W := by
      show (Val.list [.list [encFun f, encFun f, .nat x], natList (List.range q)]).wt ≤ W
      omega
    omega
  have c1 := StDC.call m2 hFd (by omega)
  have c2 := StDC.length c1 (by omega)
  rw [← itci_filter_key f x]
  refine StDC.funDet hpb c2 ?_
  unfold itciKC itciPC
  have hM3 : (M + 2) ^ 2 ≤ (M + 2) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : loopModK * (q + 1) * (W + q + 5 * (q + 1) ^ 2 + 1) ≤ 2 * 10 ^ 5 * (M + 2) ^ 3 := by
    have : W + q + 5 * (q + 1) ^ 2 + 1 ≤ 200 * (M + 2) ^ 2 := by omega
    calc loopModK * (q + 1) * (W + q + 5 * (q + 1) ^ 2 + 1)
        ≤ 1000 * (M + 2) * (200 * (M + 2) ^ 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) this
      _ = 2 * 10 ^ 5 * (M + 2) ^ 3 := by ring
  have h2 : q * (10 ^ 4 * (M + 2)) ≤ 10 ^ 4 * (M + 2) ^ 3 := by
    calc q * (10 ^ 4 * (M + 2)) ≤ (M + 2) * (10 ^ 4 * (M + 2)) := Nat.mul_le_mul_right _ (by omega)
      _ = 10 ^ 4 * (M + 2) ^ 2 := by ring
      _ ≤ 10 ^ 4 * (M + 2) ^ 3 := Nat.mul_le_mul_left _ hM3
  omega

/-- The cost of a table of positions. -/
def itciTC (M : ℕ) : ℕ := 10 ^ 9 * (M + 2) ^ 4

/-- **The table of positions**: `encPerm (itciPosE f)`. -/
theorem itci_pos_tab {P : Program} {mp pb flt kb : ℕ} (hmp : P.HasAt mp (mapFuns mp pb))
    (hpb : P.funs[pb]? = some (itPosB flt))
    (hflt : P.HasAt flt (filterFuns flt kb)) (hkb : P.funs[kb]? = some itKeyB)
    (f : Fin q → ℕ) {M : ℕ} (hM : (encFun f).wt ≤ M) :
    FunDet P mp (.list [.list [encFun f, encFun f, natList (List.range q)],
      natList (List.range q)]) (encPerm (itciPosE f)) (itciTC M) := by
  have hqM := (itci_q_le_wt f).trans hM
  have h := it_tab hmp (c := .list [encFun f, encFun f, natList (List.range q)]) (itciPos f)
    (fun i => (itciPos_lt i).le) (fun i => itci_posB_spec hpb hflt hkb f hM i)
  refine h.mono ?_
  have hR := it_range_wt (q := q)
  have hc := wt_list3_le (encFun f) (encFun f) (natList (List.range q))
  have hq1 : (q + 1) ^ 2 ≤ (M + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hM2 : M + 2 ≤ (M + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hM3 : (M + 2) ^ 3 ≤ (M + 2) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hM23 : (M + 2) ^ 2 ≤ (M + 2) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : q * itciPC M ≤ 10 ^ 7 * (M + 2) ^ 4 := by
    unfold itciPC
    calc q * (10 ^ 7 * (M + 2) ^ 3) ≤ (M + 2) * (10 ^ 7 * (M + 2) ^ 3) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 10 ^ 7 * (M + 2) ^ 4 := by ring
  have h2 : mapK * (q + 1) * (2 * (Val.list [encFun f, encFun f, natList (List.range q)]).wt +
      22 * (q + 1) ^ 2) ≤ 10 ^ 5 * (M + 2) ^ 3 := by
    calc mapK * (q + 1) * (2 * (Val.list [encFun f, encFun f, natList (List.range q)]).wt +
          22 * (q + 1) ^ 2) ≤ 1000 * (M + 2) * (100 * (M + 2) ^ 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      _ = 10 ^ 5 * (M + 2) ^ 3 := by ring
  unfold itciTC
  omega

/-! ### Centers -/

/-- On `[[F, x], y]`: whether `y` has the color of `x`. -/
def itciEqT : Expr :=
  .arith .eq (.get (.get (arg 0) (.nat 0)) (arg 1))
    (.get (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)))

/-- The test of `itciEqT` on values. -/
def itciEQ (f : Fin q → ℕ) (x : Fin q) : Val → Bool
  | .nat y => if h : y < q then decide (f ⟨y, h⟩ = f x) else false
  | _ => false

set_option maxHeartbeats 1000000 in
theorem itci_eqT_spec {P : Program} {t : ℕ} (ht : P.funs[t]? = some itciEqT)
    (f : Fin q → ℕ) {M : ℕ} (hM : (encFun f).wt ≤ M) (x y : Fin q) :
    FunDet P t (.list [.list [encFun f, .nat x], .nat y]) (boolVal (itciEQ f x (.nat y)))
      (itciKC M) := by
  have hqM := (itci_q_le_wt f).trans hM
  set W := 20 * (M + 2)
  have hx := wt_nat_le (x : ℕ)
  have hy := wt_nat_le (y : ℕ)
  have hxq := x.isLt
  have hyq := y.isLt
  have hc := wt_list2_le (encFun f) (.nat x)
  have hin := wt_list2_le (.list [encFun f, .nat x]) (.nat y)
  have hfy := itci_fwt f y
  have hfx := itci_fwt f x
  set vs : List Val := [.list [encFun f, .nat x], .nat y]
  have g0 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 0) rfl (W := W) (by omega)
    (by omega) (by omega)
  have gY := StDC.arg (P := P) (rest := []) (vs := vs) (j := 1) rfl (W := W) (by omega)
    (by omega) (by omega)
  have gL := StDC.get g0 (StDC.nat 0 (by omega)) (v := encFun f) rfl (by omega)
  have gX := StDC.get g0 (StDC.nat 1 (by omega)) (v := .nat x) rfl (by omega)
  have lY := StDC.get (vs := (List.finRange q).map fun i => Val.nat (f i)) gL gY
    (encFun_getElem? _ y) (by omega)
  have lX := StDC.get (vs := (List.finRange q).map fun i => Val.nat (f i)) gL gX
    (encFun_getElem? _ x) (by omega)
  have a1 := StDC.arith (op := .eq) lY lX rfl (by
    have := wt_nat_le (GI.Machine.BinOp.eval .eq (f y) (f x))
    simp only [GI.Machine.BinOp.eval] at this ⊢; split_ifs at this ⊢ <;> omega)
  have e : (GI.Machine.BinOp.eval .eq (f y) (f x)) = (itciEQ f x (.nat y)).toNat := by
    simp only [GI.Machine.BinOp.eval, itciEQ, y.isLt, dif_pos]
    by_cases h : f y = f x <;> simp [h]
  rw [boolVal, ← e]
  refine StDC.funDet (P := P) ht a1 ?_
  unfold itciKC
  omega

/-- The first point of the color of `x` is its center. -/
theorem itci_findIdx (f : Fin q → ℕ) (x : Fin q) :
    ((List.range q).map Val.nat).findIdx (itciEQ f x) = (itciC f x : ℕ) := by
  have hl : (itciC f x : ℕ) < ((List.range q).map Val.nat).length := by simp
  rw [List.findIdx_eq hl]
  constructor
  · simp [itciEQ, itciC_f]
  · intro j hj
    have hjq : j < q := lt_trans hj (itciC f x).isLt
    simp only [List.getElem_map, List.getElem_range, itciEQ, hjq, dif_pos, decide_eq_false_iff_not]
    intro he
    have := itciC_le (f := f) (a := x) (y := ⟨j, hjq⟩) he.symm
    rw [Fin.le_def] at this
    simp at this
    omega

/-- On `[[F, R], x]`: the center of `x`, by `find` over `R`. -/
def itciCB (fnd : ℕ) : Expr :=
  .call fnd (mk2 (mk2 (.get (arg 0) (.nat 0)) (arg 1)) (.get (arg 0) (.nat 1)))

/-- The cost of one center. -/
def itciCC (M : ℕ) : ℕ := 10 ^ 7 * (M + 2) ^ 3

set_option maxHeartbeats 1000000 in
theorem itci_cB_spec {P : Program} {cb fnd t : ℕ} (hcb : P.funs[cb]? = some (itciCB fnd))
    (hfnd : P.HasAt fnd (findFuns fnd t)) (ht : P.funs[t]? = some itciEqT)
    (f : Fin q → ℕ) {M : ℕ} (hM : (encFun f).wt ≤ M) (x : Fin q) :
    FunDet P cb (.list [.list [encFun f, natList (List.range q)], .nat x])
      (.nat (itciCN f x)) (itciCC M) := by
  have hqM := (itci_q_le_wt f).trans hM
  have hR := it_range_wt (q := q)
  have hq1 : (q + 1) ^ 2 ≤ (M + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  set W := 100 * (M + 2) ^ 2
  have hM2 : M + 2 ≤ (M + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hM23 : (M + 2) ^ 2 ≤ (M + 2) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hx := wt_nat_le (x : ℕ)
  have hxq := x.isLt
  have hc := wt_list2_le (encFun f) (natList (List.range q))
  have hin := wt_list2_le (.list [encFun f, natList (List.range q)]) (.nat x)
  have hc2 := wt_list2_le (encFun f) (.nat x)
  have hfi := wt_list2_le (.list [encFun f, .nat x]) (natList (List.range q))
  set vs : List Val := [.list [encFun f, natList (List.range q)], .nat x]
  have g0 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 0) rfl (W := W) (by omega) (by omega)
    (by omega)
  have gX := StDC.arg (P := P) (rest := []) (vs := vs) (j := 1) rfl (W := W) (by omega) (by omega)
    (by omega)
  have gL := StDC.get g0 (StDC.nat 0 (by omega)) (v := encFun f) rfl (by omega)
  have gR := StDC.get g0 (StDC.nat 1 (by omega)) (v := natList (List.range q)) rfl (by omega)
  have m2 := StDC.mk2 (StDC.mk2 gL gX (by omega) (by omega)) gR (by omega) (by omega)
  have hF := find_spec hfnd (c := .list [encFun f, .nat x])
    (xs := (List.range q).map Val.nat) (q := itciEQ f x) (B := fun _ => itciKC M)
    (fun v hv => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hv
      exact itci_eqT_spec ht f hM x ⟨y, List.mem_range.1 hy⟩)
  have hlen : ((List.range q).map Val.nat).length = q := by simp
  have hFd : FunDet P fnd (.list [.list [encFun f, .nat x], natList (List.range q)])
      (.nat (itciCN f x)) (q * itciKC M + loopModK * (q + 1) * (W + 2 * q + 3)) := by
    refine hF.mono fun w c ⟨h1, h2⟩ => ⟨by rw [h1, itci_findIdx]; rfl, ?_⟩
    have hsum : (((List.range q).map Val.nat).map fun _ => itciKC M).sum = q * itciKC M := by
      simp [Function.comp_def, List.map_const', List.sum_replicate]
    rw [hsum, hlen] at h2
    refine h2.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _)
    have : (Val.list [.list [encFun f, .nat x], .list ((List.range q).map Val.nat)]).wt ≤ W := by
      show (Val.list [.list [encFun f, .nat x], natList (List.range q)]).wt ≤ W
      omega
    omega
  have hcw : (Val.nat (itciCN f x)).wt ≤ W := by
    have := wt_nat_le (itciCN f x); have : itciCN f x < q := (itciC f x).isLt; omega
  have c1 := StDC.call m2 hFd hcw
  refine StDC.funDet hcb c1 ?_
  unfold itciKC itciCC
  have h1 : loopModK * (q + 1) * (W + 2 * q + 3) ≤ 2 * 10 ^ 5 * (M + 2) ^ 3 := by
    calc loopModK * (q + 1) * (W + 2 * q + 3) ≤ 1000 * (M + 2) * (200 * (M + 2) ^ 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      _ = 2 * 10 ^ 5 * (M + 2) ^ 3 := by ring
  have h2 : q * (10 ^ 4 * (M + 2)) ≤ 10 ^ 4 * (M + 2) ^ 3 := by
    calc q * (10 ^ 4 * (M + 2)) ≤ (M + 2) * (10 ^ 4 * (M + 2)) := Nat.mul_le_mul_right _ (by omega)
      _ = 10 ^ 4 * (M + 2) ^ 2 := by ring
      _ ≤ 10 ^ 4 * (M + 2) ^ 3 := Nat.mul_le_mul_left _ hM23
  omega

/-- **The table of centers**: `encFun (itciCN f)`. -/
theorem itci_c_tab {P : Program} {mp cb fnd t : ℕ} (hmp : P.HasAt mp (mapFuns mp cb))
    (hcb : P.funs[cb]? = some (itciCB fnd))
    (hfnd : P.HasAt fnd (findFuns fnd t)) (ht : P.funs[t]? = some itciEqT)
    (f : Fin q → ℕ) {M : ℕ} (hM : (encFun f).wt ≤ M) :
    FunDet P mp (.list [.list [encFun f, natList (List.range q)], natList (List.range q)])
      (encFun (itciCN f)) (itciTC M) := by
  have hqM := (itci_q_le_wt f).trans hM
  have h := it_tab hmp (c := .list [encFun f, natList (List.range q)]) (itciCN f)
    (fun i => (itciC f i).isLt.le) (fun i => itci_cB_spec hcb hfnd ht f hM i)
  refine h.mono ?_
  have hR := it_range_wt (q := q)
  have hc := wt_list2_le (encFun f) (natList (List.range q))
  have hq1 : (q + 1) ^ 2 ≤ (M + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hM2 : M + 2 ≤ (M + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hM3 : (M + 2) ^ 3 ≤ (M + 2) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : q * itciCC M ≤ 10 ^ 7 * (M + 2) ^ 4 := by
    unfold itciCC
    calc q * (10 ^ 7 * (M + 2) ^ 3) ≤ (M + 2) * (10 ^ 7 * (M + 2) ^ 3) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 10 ^ 7 * (M + 2) ^ 4 := by ring
  have h2 : mapK * (q + 1) * (2 * (Val.list [encFun f, natList (List.range q)]).wt +
      22 * (q + 1) ^ 2) ≤ 10 ^ 5 * (M + 2) ^ 3 := by
    calc mapK * (q + 1) * (2 * (Val.list [encFun f, natList (List.range q)]).wt +
          22 * (q + 1) ^ 2) ≤ 1000 * (M + 2) * (100 * (M + 2) ^ 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      _ = 10 ^ 5 * (M + 2) ^ 3 := by ring
  unfold itciTC
  omega

/-! ### The check -/

/-- On `[[FX, FY, Pσ], a]`: whether `fY (σ a) = fX a`. -/
def itciChkT : Expr :=
  .arith .eq (.get (.get (arg 0) (.nat 1)) (.get (.get (arg 0) (.nat 2)) (arg 1)))
    (.get (.get (arg 0) (.nat 0)) (arg 1))

/-- The test of `itciChkT` on values. -/
def itciChQ (fX fY : Fin q → ℕ) (σ : Perm (Fin q)) : Val → Bool
  | .nat a => if h : a < q then decide (fY (σ ⟨a, h⟩) = fX ⟨a, h⟩) else false
  | _ => false

set_option maxHeartbeats 1000000 in
theorem itci_chkT_spec {P : Program} {t : ℕ} (ht : P.funs[t]? = some itciChkT)
    (fX fY : Fin q → ℕ) (σ : Perm (Fin q)) {M : ℕ} (hMX : (encFun fX).wt ≤ M)
    (hMY : (encFun fY).wt ≤ M) (a : Fin q) :
    FunDet P t (.list [.list [encFun fX, encFun fY, encPerm σ], .nat a])
      (boolVal (itciChQ fX fY σ (.nat a))) (itciKC ((q + 1) ^ 2 + M)) := by
  have hqM := (itci_q_le_wt fX).trans hMX
  have hP := wt_encPerm_le σ
  set W := 20 * ((q + 1) ^ 2 + M + 2)
  have hx := wt_nat_le (a : ℕ)
  have hxq := a.isLt
  have hσa := wt_nat_le (σ a : ℕ)
  have hσq := (σ a).isLt
  have hc := wt_list3_le (encFun fX) (encFun fY) (encPerm σ)
  have hin := wt_list2_le (.list [encFun fX, encFun fY, encPerm σ]) (.nat a)
  have hfy := itci_fwt fY (σ a)
  have hfx := itci_fwt fX a
  set vs : List Val := [.list [encFun fX, encFun fY, encPerm σ], .nat a]
  have g0 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 0) rfl (W := W) (by omega)
    (by omega) (by omega)
  have gA := StDC.arg (P := P) (rest := []) (vs := vs) (j := 1) rfl (W := W) (by omega)
    (by omega) (by omega)
  have gX := StDC.get g0 (StDC.nat 0 (by omega)) (v := encFun fX) rfl (by omega)
  have gY := StDC.get g0 (StDC.nat 1 (by omega)) (v := encFun fY) rfl (by omega)
  have gP := StDC.get g0 (StDC.nat 2 (by omega)) (v := encPerm σ) rfl (by omega)
  have pA := StDC.get (vs := (List.finRange q).map fun i => Val.nat (σ i : ℕ)) gP gA
    (encFun_getElem? _ a) (by omega)
  have yA := StDC.get (vs := (List.finRange q).map fun i => Val.nat (fY i)) gY pA
    (encFun_getElem? _ (σ a)) (by omega)
  have xA := StDC.get (vs := (List.finRange q).map fun i => Val.nat (fX i)) gX gA
    (encFun_getElem? _ a) (by omega)
  have a1 := StDC.arith (op := .eq) yA xA rfl (by
    have := wt_nat_le (GI.Machine.BinOp.eval .eq (fY (σ a)) (fX a))
    simp only [GI.Machine.BinOp.eval] at this ⊢; split_ifs at this ⊢ <;> omega)
  have e : (GI.Machine.BinOp.eval .eq (fY (σ a)) (fX a)) = (itciChQ fX fY σ (.nat a)).toNat := by
    simp only [GI.Machine.BinOp.eval, itciChQ, a.isLt, dif_pos]
    by_cases h : fY (σ a) = fX a <;> simp [h]
  rw [boolVal, ← e]
  refine StDC.funDet (P := P) ht a1 ?_
  unfold itciKC
  omega

/-- The check over all points. -/
theorem itci_all_chk (fX fY : Fin q → ℕ) (σ : Perm (Fin q)) :
    ((List.range q).map Val.nat).all (itciChQ fX fY σ) = decide (∀ a, fY (σ a) = fX a) := by
  rw [Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_iff]
  constructor
  · intro h a
    have := h (.nat a) (List.mem_map.2 ⟨a, List.mem_range.2 a.isLt, rfl⟩)
    simpa [itciChQ, a.isLt] using this
  · intro h v hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hv
    have ha' := List.mem_range.1 ha
    simpa [itciChQ, ha'] using h ⟨a, ha'⟩

end GI.Impl
