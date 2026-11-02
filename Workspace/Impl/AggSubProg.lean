import Workspace.Impl.AggSubMath
import Workspace.Impl.AggCertWt

/-!
# The list of the test sets, as a program

`sbFuns b` (32 functions at `b`) on `[k, q, κ]` returns the list of the values `tsV k T` of the
`κ`-subsets `T` of the `q` labels, in the order `sbOrder q κ` (`sb_spec`). This is the list of
test sets that the program state of the certificate phase holds at its start.

The program runs over the numbers `j < q ^ κ`. For each `j` it reads the digits `d` of `j`
(`stDDec_spec`), lists the labels `c < q` that occur in `d` in increasing order (a filter over
`[0, …, q - 1]` with a count test), and keeps `j` when this list is `d` (`eqNats_spec`). For a
kept `j` it adds `[indicator of d, d shifted by k]` (`sbEntV`), which is `tsV k` of the set of `d`
(`sb_entV_eq`).

Its cost is at most `sbK (Y + 1) ^ 5` with `Y = q ^ κ + k + q + κ + 10`: there are `q ^ κ` steps,
each polynomial in `Y`. Since `κ` is a constant of the round, this is polynomial in the input of
the round.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang
open GI.Cited (Val)
open GI.Machine (BinOp)

/-! ### The count test -/

/-- On `[natList d, c]`: 1 if `c` occurs in `d`, else 0. It calls the count at `bc`. -/
def sbPredF (bc : ℕ) : Expr := .ite (.call bc (mk2 (arg 1) (arg 0))) (.nat 1) (.nat 0)

/-- The cost constant of the count test. -/
def sbPredK : ℕ := 10 ^ 7

theorem sbPred_spec {P : Program} {f bc : ℕ} (hf : P.funs[f]? = some (sbPredF bc))
    (hc : P.HasAt bc (countFuns bc)) {d : List ℕ} {c Y : ℕ} (hd : ∀ x ∈ d, x ≤ Y)
    (hl : d.length ≤ Y) (hcY : c ≤ Y) :
    FunDet P f (.list [natList d, .nat c]) (boolVal (decide (d.count c ≠ 0)))
      (sbPredK * (Y + 1) ^ 3) := by
  have hcnt := count_spec hc hd hcY hl
  have hdw := wt_natList_le_sq hd hl
  have hcw := wt_nat_le c
  have hY1 : Y + 1 ≤ (Y + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hY2 : (Y + 1) ^ 2 ≤ (Y + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  set W := 20 * (Y + 1) ^ 2 + 40 with hW
  have hvw : (Val.list [natList d, .nat c]).wt ≤ W := by
    have := wt_list2_le (natList d) (.nat c); omega
  have gd : StDC P [Val.list [natList d, .nat c]] (arg 0) (natList d) 3 0 W :=
    StDC.arg rfl hvw (by omega) (by omega)
  have gc : StDC P [Val.list [natList d, .nat c]] (arg 1) (.nat c) 3 0 W :=
    StDC.arg rfl hvw (by omega) (by omega)
  have gl := StDC.mk2 gc gd (by have := wt_list2_le (.nat c) (natList d); omega) (by omega)
  have hcd : d.count c ≤ Y := (List.count_le_length).trans hl
  have gcall := StDC.call gl hcnt (by have := wt_nat_le (d.count c); omega)
  have gite := StDC.ite (v := boolVal (decide (d.count c ≠ 0))) gcall
    (fun hx => by
      rw [show boolVal (decide (d.count c ≠ 0)) = .nat 1 by simp [hx]]
      exact StDC.nat 1 (by omega))
    (fun hx => by
      rw [show boolVal (decide (d.count c ≠ 0)) = .nat 0 by simp [hx]]
      exact StDC.nat 0 (by omega))
    (by have := wt_boolVal_le (decide (d.count c ≠ 0)); omega)
  refine StDC.funDet hf gite ?_
  unfold sbPredK countK
  omega

/-! ### The increasing list of the labels of `d`, and the indicator -/

/-- The cost constant of the list of labels and of the indicator. -/
def sbSrtK : ℕ := 10 ^ 9

/-- The test of `filter_spec`, on values. -/
def sbPV (d : List ℕ) : Val → Bool
  | .nat c => decide (d.count c ≠ 0)
  | .list _ => false

theorem sb_wt_range (q Y : ℕ) (hq : q ≤ Y) : (natList (List.range q)).wt ≤ 5 * (Y + 1) ^ 2 :=
  wt_natList_le_sq (fun x hx => by have := List.mem_range.1 hx; omega) (by simp; omega)

/-- **The labels of `d`, in increasing order**, by a filter over `[0, …, q - 1]`. -/
theorem sbSrt_spec {P : Program} {bF p bc : ℕ} (hb : P.HasAt bF (filterFuns bF p))
    (hp : P.funs[p]? = some (sbPredF bc)) (hc : P.HasAt bc (countFuns bc)) {d : List ℕ}
    {q Y : ℕ} (hd : ∀ x ∈ d, x ≤ Y) (hl : d.length ≤ Y) (hq : q ≤ Y) :
    FunDet P bF (.list [natList d, natList (List.range q)]) (natList (sbSrt q d))
      (sbSrtK * (Y + 1) ^ 4) := by
  have hF := filter_spec hb (c := natList d) (xs := (List.range q).map Val.nat) (q := sbPV d)
    (B := fun _ => sbPredK * (Y + 1) ^ 3) (by
      intro x hx
      obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hx
      exact sbPred_spec hp hc hd hl (by have := List.mem_range.1 hc'; omega))
  have hout : Val.list (((List.range q).map Val.nat).filter (sbPV d)) = natList (sbSrt q d) := by
    rw [List.filter_map, natList, sbSrt]
    rfl
  refine hF.mono fun w cost ⟨hw, hcost⟩ => ⟨hw.trans hout, ?_⟩
  have hs : (((List.range q).map Val.nat).map fun _ => sbPredK * (Y + 1) ^ 3).sum =
      q * (sbPredK * (Y + 1) ^ 3) := by simp [Function.comp_def, List.map_const']
  have hlen : ((List.range q).map Val.nat).length = q := by simp
  have hA : (Val.list [natList d, .list ((List.range q).map Val.nat)]).wt =
      (Val.list [natList d, natList (List.range q)]).wt := rfl
  rw [hs, hlen, hA, hw, hout] at hcost
  have h1 := sb_wt_range q Y hq
  have h2 : (natList d).wt ≤ 5 * (Y + 1) ^ 2 := wt_natList_le_sq hd hl
  have h3 : (natList (sbSrt q d)).wt ≤ 5 * (Y + 1) ^ 2 :=
    wt_natList_le_sq (fun x hx => by have := (sb_mem_srt.1 hx).1; omega)
      ((List.length_filter_le _ _).trans (by simp; omega))
  have h4 := wt_list2_le (natList d) (natList (List.range q))
  have hY1 : Y + 1 ≤ (Y + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hY2 : (Y + 1) ^ 2 ≤ (Y + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hY3 : (Y + 1) * (Y + 1) ^ 3 = (Y + 1) ^ 4 := by ring
  have e1 : q * (sbPredK * (Y + 1) ^ 3) ≤ sbPredK * (Y + 1) ^ 4 := by
    rw [← hY3, mul_left_comm]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
  have e2 : loopModK * (q + 1) * ((Val.list [natList d, natList (List.range q)]).wt +
      q + (natList (sbSrt q d)).wt + 1) ≤ loopModK * (Y + 1) * (40 * (Y + 1) ^ 2) := by
    refine Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e3 : (Y + 1) * (40 * (Y + 1) ^ 2) ≤ 40 * (Y + 1) ^ 4 := by
    have : (Y + 1) * (Y + 1) ^ 2 = (Y + 1) ^ 3 := by ring
    have h34 : (Y + 1) ^ 3 ≤ (Y + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    nlinarith
  have e4 : loopModK * (Y + 1) * (40 * (Y + 1) ^ 2) ≤ loopModK * (40 * (Y + 1) ^ 4) := by
    rw [mul_assoc]; exact Nat.mul_le_mul_left _ e3
  unfold sbSrtK sbPredK loopModK at *
  omega

/-- **The indicator of the labels of `d`**, by a map over `[0, …, q - 1]`. -/
theorem sbInd_spec {P : Program} {bM p bc : ℕ} (hb : P.HasAt bM (mapFuns bM p))
    (hp : P.funs[p]? = some (sbPredF bc)) (hc : P.HasAt bc (countFuns bc)) {d : List ℕ}
    {q Y : ℕ} (hd : ∀ x ∈ d, x ≤ Y) (hl : d.length ≤ Y) (hq : q ≤ Y) (hY : 1 ≤ Y) :
    FunDet P bM (.list [natList d, natList (List.range q)]) (natList (sbInd q d))
      (sbSrtK * (Y + 1) ^ 4) := by
  have hM := map_spec hb (c := natList d) (xs := (List.range q).map Val.nat)
    (R := fun x w => ∀ c : ℕ, x = .nat c → w = boolVal (decide (d.count c ≠ 0)))
    (B := fun _ => sbPredK * (Y + 1) ^ 3) (by
      intro x hx
      obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hx
      refine FunAll.mono (sbPred_spec hp hc hd hl (by have := List.mem_range.1 hc'; omega))
        fun w cw hw => ⟨fun c' hc'' => ?_, hw.2⟩
      cases hc''
      exact hw.1)
  refine hM.mono fun w cost ⟨ws, hw, hR, hcost⟩ => ?_
  have hws : ws = (List.range q).map fun c => boolVal (decide (d.count c ≠ 0)) :=
    forall₂_map_eq (fun c _ w h => h c rfl) hR
  have hout : w = natList (sbInd q d) := by
    rw [hw, hws, natList, sbInd, List.map_map]; rfl
  refine ⟨hout, ?_⟩
  have hs : (((List.range q).map Val.nat).map fun _ => sbPredK * (Y + 1) ^ 3).sum =
      q * (sbPredK * (Y + 1) ^ 3) := by simp [Function.comp_def, List.map_const']
  have hlen : ((List.range q).map Val.nat).length = q := by simp
  have hA : (Val.list [natList d, .list ((List.range q).map Val.nat)]).wt =
      (Val.list [natList d, natList (List.range q)]).wt := rfl
  rw [hs, hlen, hA, hout] at hcost
  have h1 := sb_wt_range q Y hq
  have h2 : (natList d).wt ≤ 5 * (Y + 1) ^ 2 := wt_natList_le_sq hd hl
  have h3 : (natList (sbInd q d)).wt ≤ 5 * (Y + 1) ^ 2 :=
    wt_natList_le_sq (fun x hx => by
      obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
      have := Bool.toNat_le (decide (d.count c ≠ 0)); omega) (by simp [sbInd]; omega)
  have h4 := wt_list2_le (natList d) (natList (List.range q))
  have hY1 : Y + 1 ≤ (Y + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hY2 : (Y + 1) ^ 2 ≤ (Y + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hY3 : (Y + 1) * (Y + 1) ^ 3 = (Y + 1) ^ 4 := by ring
  have e1 : q * (sbPredK * (Y + 1) ^ 3) ≤ sbPredK * (Y + 1) ^ 4 := by
    rw [← hY3, mul_left_comm]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
  have e2 : mapK * (q + 1) * ((Val.list [natList d, natList (List.range q)]).wt +
      (natList (sbInd q d)).wt + 1) ≤ mapK * (Y + 1) * (40 * (Y + 1) ^ 2) := by
    refine Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e3 : (Y + 1) * (40 * (Y + 1) ^ 2) ≤ 40 * (Y + 1) ^ 4 := by
    have : (Y + 1) * (Y + 1) ^ 2 = (Y + 1) ^ 3 := by ring
    have h34 : (Y + 1) ^ 3 ≤ (Y + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    nlinarith
  have e4 : mapK * (Y + 1) * (40 * (Y + 1) ^ 2) ≤ mapK * (40 * (Y + 1) ^ 4) := by
    rw [mul_assoc]; exact Nat.mul_le_mul_left _ e3
  unfold sbSrtK sbPredK mapK at *
  omega

/-! ### The shift by `k` -/

/-- On `[k, c]`: `k + c`. -/
def sbAddF : Expr := .arith .add (arg 0) (arg 1)

theorem sbAdd_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some sbAddF) {k c Y : ℕ}
    (h : k + c ≤ Y) : FunDet P f (.list [.nat k, .nat c]) (.nat (k + c)) (200 * (Y + 1)) := by
  set W := 4 * Y + 20 with hW
  have hvw : (Val.list [.nat k, .nat c]).wt ≤ W := by
    have := wt_list2_le (.nat k) (.nat c); have := wt_nat_le k; have := wt_nat_le c; omega
  have g0 : StDC P [Val.list [.nat k, .nat c]] (arg 0) (.nat k) 3 0 W :=
    StDC.arg rfl hvw (by omega) (by have := wt_nat_le k; omega)
  have g1 : StDC P [Val.list [.nat k, .nat c]] (arg 1) (.nat c) 3 0 W :=
    StDC.arg rfl hvw (by omega) (by have := wt_nat_le c; omega)
  have g := StDC.arith' g0 g1 (op := .add) (show BinOp.eval .add k c = k + c from rfl) (by omega)
  exact StDC.funDet hf g (by omega)

/-- The cost constant of the shift. -/
def sbShK : ℕ := 10 ^ 6

/-- **The shift of a list by `k`**, by a map. -/
theorem sbSh_spec {P : Program} {bA f : ℕ} (hb : P.HasAt bA (mapFuns bA f))
    (hf : P.funs[f]? = some sbAddF) {k : ℕ} {d : List ℕ} {Y : ℕ} (hd : ∀ x ∈ d, k + x ≤ Y)
    (hl : d.length ≤ Y) (hk : k ≤ Y) :
    FunDet P bA (.list [.nat k, natList d]) (natList (d.map (k + ·))) (sbShK * (Y + 1) ^ 3) := by
  have hM := map_spec hb (c := .nat k) (xs := d.map Val.nat)
    (R := fun x w => ∀ c : ℕ, x = .nat c → w = .nat (k + c))
    (B := fun _ => 200 * (Y + 1)) (by
      intro x hx
      obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hx
      refine FunAll.mono (sbAdd_spec hf (hd c hc')) fun w cw hw => ⟨fun c' hc'' => ?_, hw.2⟩
      cases hc''
      exact hw.1)
  refine hM.mono fun w cost ⟨ws, hw, hR, hcost⟩ => ?_
  have hws : ws = d.map fun c => Val.nat (k + c) := forall₂_map_eq (fun c _ w h => h c rfl) hR
  have hout : w = natList (d.map (k + ·)) := by
    rw [hw, hws, natList, List.map_map]; rfl
  refine ⟨hout, ?_⟩
  rw [hout] at hcost
  have hs : ((d.map Val.nat).map fun _ => 200 * (Y + 1)).sum = d.length * (200 * (Y + 1)) := by
    simp [Function.comp_def, List.map_const']
  have hlen : (d.map Val.nat).length = d.length := by simp
  have hA : (Val.list [.nat k, .list (d.map Val.nat)]).wt = (Val.list [.nat k, natList d]).wt :=
    rfl
  rw [hs, hlen, hA] at hcost
  have h1 : (natList d).wt ≤ 5 * (Y + 1) ^ 2 :=
    wt_natList_le_sq (fun x hx => by have := hd x hx; omega) hl
  have h2 : (natList (d.map (k + ·))).wt ≤ 5 * (Y + 1) ^ 2 :=
    wt_natList_le_sq (fun x hx => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx; exact hd c hc) (by simp; omega)
  have h3 := wt_list2_le (.nat k) (natList d)
  have h4 := wt_nat_le k
  have hY1 : Y + 1 ≤ (Y + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hY2 : (Y + 1) * (Y + 1) = (Y + 1) ^ 2 := by ring
  have hY3 : (Y + 1) * (Y + 1) ^ 2 = (Y + 1) ^ 3 := by ring
  have hY23 : (Y + 1) ^ 2 ≤ (Y + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have e1 : d.length * (200 * (Y + 1)) ≤ 200 * (Y + 1) ^ 2 := by
    rw [← hY2, mul_left_comm]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
  have e2 : mapK * (d.length + 1) * ((Val.list [.nat k, natList d]).wt +
      (natList (d.map (k + ·))).wt + 1) ≤ mapK * ((Y + 1) * (40 * (Y + 1) ^ 2)) := by
    rw [mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
  have e3 : (Y + 1) * (40 * (Y + 1) ^ 2) = 40 * (Y + 1) ^ 3 := by rw [mul_left_comm, hY3]
  unfold sbShK mapK at *
  omega

/-! ### The module -/

/-- **The step of the loop** on `[a, j, acc]`, `a = [k, q, κ, [0, …, q - 1], q ^ κ]`: the digits
`d` of `j`, the labels of `d` in increasing order, and, when the two agree, the value
`sbEntV k q d` added to `acc`. -/
def sbStep (b : ℕ) : Expr :=
  .letE (.get (.call (b + 10) (mk3 (mk2 (arg 1) .nil) (.get (arg 0) (.nat 1))
      (.get (arg 0) (.nat 2)))) (.nat 1))
    (.letE (.call (b + 13) (mk2 (.var 1) (.get (arg 0) (.nat 3))))
      (.ite (.call (b + 25) (mk2 (.var 2) (.var 1)))
        (.snoc (arg 2) (mk2 (.call (b + 22) (mk2 (.var 1) (.get (arg 0) (.nat 3))))
          (.call (b + 28) (mk2 (.get (arg 0) (.nat 0)) (.var 2)))))
        (arg 2)))

/-- The entry on `[k, q, κ]`: the loop on `[k, q, κ, [0, …, q - 1], q ^ κ]`. -/
def sbEntry (b : ℕ) : Expr :=
  .call (b + 1) (.snoc (mk4 (arg 0) (arg 1) (arg 2) (.call (b + 7) (arg 1)))
    (.call (b + 4) (mk2 (arg 1) (arg 2))))

/-- **The program of the test sets** at `b` (32 functions). -/
def sbFuns (b : ℕ) : List Expr :=
  [sbEntry b] ++ loopFuns (b + 1) (.get (.var 0) (.nat 4)) .nil (sbStep b) ++
    stDPowFuns (b + 4) ++ rangeFuns (b + 7) ++ stDDecFuns (b + 10) ++
    filterFuns (b + 13) (b + 16) ++ [sbPredF (b + 17)] ++ countFuns (b + 17) ++
    mapFuns (b + 22) (b + 16) ++ eqNatsFuns (b + 25) ++ mapFuns (b + 28) (b + 31) ++ [sbAddF]

/-- The accumulator after the numbers `j < i`. -/
def sbAcc (k q κ i : ℕ) : Val :=
  .list (((List.range i).filter (sbOk q κ)).map fun j => sbEntV k q (stDDec q κ j))

theorem sb_acc_succ (k q κ i : ℕ) :
    sbAcc k q κ (i + 1) = if sbOk q κ i then
      .list (((List.range i).filter (sbOk q κ)).map (fun j => sbEntV k q (stDDec q κ j)) ++
        [sbEntV k q (stDDec q κ i)]) else sbAcc k q κ i := by
  unfold sbAcc
  rw [List.range_succ, List.filter_append]
  cases h : sbOk q κ i <;> simp [h]

theorem sb_acc_top (k q κ : ℕ) : sbAcc k q κ (q ^ κ) = .list ((sbOrder q κ).sets.map (tsV k)) := by
  rw [← sb_order_vals, sbAcc, sbLists, sbIdx, List.map_map]
  rfl

/-- The context of the loop. -/
def sbA (k q κ : ℕ) : Val :=
  .list [.nat k, .nat q, .nat κ, natList (List.range q), .nat (q ^ κ)]

section Wt

variable {k q κ Y : ℕ}

theorem sb_Y_facts (_hY : q ^ κ + k + q + κ + 10 ≤ Y) :
    1 ≤ (Y + 1) ^ 2 ∧ Y + 1 ≤ (Y + 1) ^ 2 ∧ (Y + 1) ^ 2 ≤ (Y + 1) ^ 3 ∧
      (Y + 1) ^ 3 ≤ (Y + 1) ^ 4 ∧ (Y + 1) ^ 4 ≤ (Y + 1) ^ 5 ∧
      (Y + 1) * (Y + 1) ^ 2 = (Y + 1) ^ 3 ∧ (Y + 1) * (Y + 1) ^ 3 = (Y + 1) ^ 4 ∧
      (Y + 1) * (Y + 1) ^ 4 = (Y + 1) ^ 5 := by
  refine ⟨Nat.one_le_pow _ _ (by omega), Nat.le_self_pow (by norm_num) _,
    Nat.pow_le_pow_right (by omega) (by norm_num), Nat.pow_le_pow_right (by omega) (by norm_num),
    Nat.pow_le_pow_right (by omega) (by norm_num), by ring, by ring, by ring⟩

/-- The weight of one value `sbEntV`. -/
theorem sb_wt_ent (hY : q ^ κ + k + q + κ + 10 ≤ Y) {d : List ℕ} (hd : ∀ x ∈ d, x < q)
    (hl : d.length ≤ Y) : (sbEntV k q d).wt ≤ 30 * (Y + 1) ^ 2 := by
  obtain ⟨h1, -⟩ := sb_Y_facts hY
  have a1 : (natList (sbInd q d)).wt ≤ 5 * (Y + 1) ^ 2 :=
    wt_natList_le_sq (fun x hx => by
      obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
      have := Bool.toNat_le (decide (d.count c ≠ 0)); omega) (by simp [sbInd]; omega)
  have a2 : (natList (d.map (k + ·))).wt ≤ 5 * (Y + 1) ^ 2 :=
    wt_natList_le_sq (fun x hx => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx; have := hd c hc; omega) (by simp; omega)
  have := wt_list2_le (natList (sbInd q d)) (natList (d.map (k + ·)))
  unfold sbEntV
  omega

/-- The weight of the accumulator. -/
theorem sb_wt_acc (hq : 0 < q) (hY : q ^ κ + k + q + κ + 10 ≤ Y) {i : ℕ} (hi : i ≤ q ^ κ) :
    (sbAcc k q κ i).wt ≤ 100 * (Y + 1) ^ 3 := by
  obtain ⟨h1, h2, h3, -, -, h6, -⟩ := sb_Y_facts hY
  have hl : (((List.range i).filter (sbOk q κ)).map
      fun j => sbEntV k q (stDDec q κ j)).length ≤ Y := by
    simp only [List.length_map]
    exact (List.length_filter_le _ _).trans (by simp; omega)
  have h := cp_wt_list hl (c := 30 * (Y + 1) ^ 2) (by
    intro v hv
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hv
    exact sb_wt_ent hY (stDDec_lt hq) (by rw [stDDec_length]; omega))
  unfold sbAcc
  have : Y * (2 * (30 * (Y + 1) ^ 2) + 1) ≤ (Y + 1) * (61 * (Y + 1) ^ 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e : (Y + 1) * (61 * (Y + 1) ^ 2) = 61 * (Y + 1) ^ 3 := by ring
  omega

theorem sb_wt_A (hY : q ^ κ + k + q + κ + 10 ≤ Y) : (sbA k q κ).wt ≤ 30 * (Y + 1) ^ 2 := by
  obtain ⟨h1, h2, -⟩ := sb_Y_facts hY
  have a1 : (natList (List.range q)).wt ≤ 5 * (Y + 1) ^ 2 := sb_wt_range q Y (by omega)
  have := wt_list_le [Val.nat k, .nat q, .nat κ, natList (List.range q), .nat (q ^ κ)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at this
  have := wt_nat_le k; have := wt_nat_le q; have := wt_nat_le κ; have := wt_nat_le (q ^ κ)
  unfold sbA
  omega

end Wt

/-- The cost constant of one step. -/
def sbStK : ℕ := 10 ^ 13

/-- **One step of the loop.** -/
theorem sbStep_spec {P : Program} {b : ℕ} (h : P.HasAt b (sbFuns b)) {k q κ Y : ℕ}
    (hq : 0 < q) (hY : q ^ κ + k + q + κ + 10 ≤ Y) {i : ℕ} (hi : i < q ^ κ) :
    Det P [.list [sbA k q κ, .nat i, sbAcc k q κ i]] (sbStep b) (sbAcc k q κ (i + 1))
      (sbStK * (Y + 1) ^ 4) := by
  obtain ⟨f1, f2, f3, f4, -, f6, f7, -⟩ := sb_Y_facts hY
  have hdec : P.HasAt (b + 10) (stDDecFuns (b + 10)) := h.block 10 rfl
  have hfil : P.HasAt (b + 13) (filterFuns (b + 13) (b + 16)) := h.block 13 rfl
  have hpred : P.funs[b + 16]? = some (sbPredF (b + 17)) := (h.block 16 rfl).single
  have hcnt : P.HasAt (b + 17) (countFuns (b + 17)) := h.block 17 rfl
  have hind : P.HasAt (b + 22) (mapFuns (b + 22) (b + 16)) := h.block 22 rfl
  have heq : P.HasAt (b + 25) (eqNatsFuns (b + 25)) := h.block 25 rfl
  have hsh : P.HasAt (b + 28) (mapFuns (b + 28) (b + 31)) := h.block 28 rfl
  have hadd : P.funs[b + 31]? = some sbAddF := (h.block 31 rfl).single
  have hdgq : ∀ x ∈ stDDec q κ i, x < q := stDDec_lt hq
  have hdgl : (stDDec q κ i).length = κ := stDDec_length q κ i
  have hsq : ∀ x ∈ sbSrt q (stDDec q κ i), x < q := fun x hx => (sb_mem_srt.1 hx).1
  have hsl : (sbSrt q (stDDec q κ i)).length ≤ q := (List.length_filter_le _ _).trans (by simp)
  have wA := sb_wt_A hY (k := k)
  have wacc := sb_wt_acc hq hY (k := k) (le_of_lt hi)
  have wacc1 := sb_wt_acc hq hY (k := k) (i := i + 1) (by omega)
  have wdg : (natList (stDDec q κ i)).wt ≤ 5 * (Y + 1) ^ 2 :=
    wt_natList_le_sq (fun x hx => by have := hdgq x hx; omega) (by omega)
  have wsrt : (natList (sbSrt q (stDDec q κ i))).wt ≤ 5 * (Y + 1) ^ 2 :=
    wt_natList_le_sq (fun x hx => by have := hsq x hx; omega) (by omega)
  have wR : (natList (List.range q)).wt ≤ 5 * (Y + 1) ^ 2 := sb_wt_range q Y (by omega)
  have wi := wt_nat_le i
  have wq := wt_nat_le q
  have wκ := wt_nat_le κ
  have wk := wt_nat_le k
  have hiY : i ≤ Y := by omega
  set W := 10 ^ 4 * (Y + 1) ^ 3 with hW
  have wenv : (Val.list [(sbA k q κ), .nat i, (sbAcc k q κ i)]).wt ≤ W := by
    have := wt_list3_le (sbA k q κ) (.nat i) (sbAcc k q κ i); omega
  -- the digits
  have g0 : StDC P [Val.list [(sbA k q κ), .nat i, (sbAcc k q κ i)]] (arg 0) (sbA k q κ) 3 0 W :=
    StDC.arg rfl wenv (by omega) (by omega)
  have g1 : StDC P [Val.list [(sbA k q κ), .nat i, (sbAcc k q κ i)]] (arg 1) (.nat i) 3 0 W :=
    StDC.arg rfl wenv (by omega) (by omega)
  have gp := StDC.mk2 g1 (StDC.nil (by omega))
    (by have := wt_list2_le (.nat i) (.list []); simp only [wt_list_nil] at this; omega)
    (by omega)
  have gq := StDC.get (v := .nat q) g0 (StDC.nat 1 (by omega)) rfl (by omega)
  have gκ := StDC.get (v := .nat κ) g0 (StDC.nat 2 (by omega)) rfl (by omega)
  have wDA : (stDDA i q κ).wt ≤ 5 * Y + 60 := by
    have := wt_list2_le (.nat i) (.list []); simp only [wt_list_nil] at this
    have := wt_list3_le (.list [.nat i, .list []]) (.nat q) (.nat κ)
    unfold stDDA; omega
  have gD := StDC.mk3 gp gq gκ (by unfold stDDA at wDA; omega) (by omega)
  have hdc : stDDecK * (20 * Y + 100 + 1) ^ 3 ≤ 2 * 10 ^ 12 * (Y + 1) ^ 3 := by
    have : (20 * Y + 100 + 1) ^ 3 ≤ (101 * (Y + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    rw [mul_pow] at this
    unfold stDDecK; omega
  have sD := (stDDec_spec hdec (j := i) (q := q) (e := κ) hq (X := 20 * Y + 100)
    (by omega)).mono hdc
  have wpair : (Val.list [.nat (i / q ^ κ), natList (stDDec q κ i)]).wt ≤ 20 * (Y + 1) ^ 2 := by
    have := wt_list2_le (.nat (i / q ^ κ)) (natList (stDDec q κ i))
    have := wt_nat_le (i / q ^ κ); have := Nat.div_le_self i (q ^ κ); omega
  have gc := StDC.call gD sD (by omega)
  have gdg := StDC.get (v := natList (stDDec q κ i)) gc (StDC.nat 1 (by omega)) rfl (by omega)
  -- the labels of the digits, in increasing order
  set env1 := [Val.list [(sbA k q κ), .nat i, (sbAcc k q κ i)], natList (stDDec q κ i)] with henv1
  have g0' : StDC P env1 (arg 0) (sbA k q κ) 3 0 W := StDC.arg rfl wenv (by omega) (by omega)
  have gR := StDC.get (v := natList (List.range q)) g0' (StDC.nat 3 (by omega)) rfl (by omega)
  have gv1 : StDC P env1 (.var 1) (natList (stDDec q κ i)) 1 0 W := StDC.var' rfl (by omega)
  have gm := StDC.mk2 gv1 gR (by have := wt_list2_le (natList (stDDec q κ i)) (natList (List.range q)); omega)
    (by omega)
  have sS := sbSrt_spec hfil hpred hcnt (d := (stDDec q κ i)) (q := q) (Y := Y)
    (fun x hx => by have := hdgq x hx; omega) (by omega) (by omega)
  have gS := StDC.call gm sS (by omega)
  -- the test
  set env2 := env1 ++ [natList (sbSrt q (stDDec q κ i))] with henv2
  have g0'' : StDC P env2 (arg 0) (sbA k q κ) 3 0 W := StDC.arg rfl wenv (by omega) (by omega)
  have gR' := StDC.get (v := natList (List.range q)) g0'' (StDC.nat 3 (by omega)) rfl (by omega)
  have gv1' : StDC P env2 (.var 1) (natList (stDDec q κ i)) 1 0 W := StDC.var' rfl (by omega)
  have gv2' : StDC P env2 (.var 2) (natList (sbSrt q (stDDec q κ i))) 1 0 W := StDC.var' rfl (by omega)
  have g2' : StDC P env2 (arg 2) (sbAcc k q κ i) 3 0 W := StDC.arg rfl wenv (by omega) (by omega)
  have wsd := wt_list2_le (natList (sbSrt q (stDDec q κ i))) (natList (stDDec q κ i))
  have gE := StDC.mk2 gv2' gv1' (by omega) (by omega)
  have heqc : loopModK * ((sbSrt q (stDDec q κ i)).length + 1) * ((Val.list [natList (sbSrt q (stDDec q κ i)), natList (stDDec q κ i)]).wt +
      (sbSrt q (stDDec q κ i)).length + 4) ≤ 10 ^ 5 * (Y + 1) ^ 3 := by
    have : loopModK * ((sbSrt q (stDDec q κ i)).length + 1) * ((Val.list [natList (sbSrt q (stDDec q κ i)), natList (stDDec q κ i)]).wt +
        (sbSrt q (stDDec q κ i)).length + 4) ≤ loopModK * ((Y + 1) * (40 * (Y + 1) ^ 2)) := by
      rw [mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
    have e : (Y + 1) * (40 * (Y + 1) ^ 2) = 40 * (Y + 1) ^ 3 := by ring
    unfold loopModK at this ⊢; omega
  have gT := StDC.call gE ((eqNats_spec heq (sbSrt q (stDDec q κ i)) (stDDec q κ i)).mono heqc)
    (by have := wt_boolVal_le (decide ((sbSrt q (stDDec q κ i)) = (stDDec q κ i))); omega)
  -- the new entry
  have gI := StDC.call (StDC.mk2 gv1' gR'
    (by have := wt_list2_le (natList (stDDec q κ i)) (natList (List.range q)); omega) (by omega))
    (sbInd_spec hind hpred hcnt (d := (stDDec q κ i)) (q := q) (Y := Y)
      (fun x hx => by have := hdgq x hx; omega) (by omega) (by omega) (by omega))
    (by
      have : (natList (sbInd q (stDDec q κ i))).wt ≤ 5 * (Y + 1) ^ 2 :=
        wt_natList_le_sq (fun x hx => by
          obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
          have := Bool.toNat_le (decide ((stDDec q κ i).count c ≠ 0)); omega) (by simp [sbInd]; omega)
      omega)
  have gk := StDC.get (v := .nat k) g0'' (StDC.nat 0 (by omega)) rfl (by omega)
  have gH := StDC.call (StDC.mk2 gk gv2' (by have := wt_list2_le (.nat k) (natList (sbSrt q (stDDec q κ i))); omega)
      (by omega))
    (sbSh_spec hsh hadd (k := k) (d := (sbSrt q (stDDec q κ i))) (Y := Y)
      (fun x hx => by have := hsq x hx; omega) (by omega) (by omega))
    (by
      have : (natList ((sbSrt q (stDDec q κ i)).map (k + ·))).wt ≤ 5 * (Y + 1) ^ 2 :=
        wt_natList_le_sq (fun x hx => by
          obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx; have := hsq c hc; omega) (by simp; omega)
      omega)
  have wInd : (natList (sbInd q (stDDec q κ i))).wt ≤ 5 * (Y + 1) ^ 2 :=
    wt_natList_le_sq (fun x hx => by
      obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
      have := Bool.toNat_le (decide ((stDDec q κ i).count c ≠ 0)); omega) (by simp [sbInd]; omega)
  have wSh : (natList ((sbSrt q (stDDec q κ i)).map (k + ·))).wt ≤ 5 * (Y + 1) ^ 2 :=
    wt_natList_le_sq (fun x hx => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx; have := hsq c hc; omega) (by simp; omega)
  have wEnt := wt_list2_le (natList (sbInd q (stDDec q κ i)))
    (natList ((sbSrt q (stDDec q κ i)).map (k + ·)))
  have gite := StDC.ite (v := sbAcc k q κ (i + 1)) gT
    (fun hx => by
      have hsd : (sbSrt q (stDDec q κ i)) = (stDDec q κ i) := by simpa using hx
      have hok : sbOk q κ i = true := by simp [sbOk, hsd]
      have hval : Val.list (((List.range i).filter (sbOk q κ)).map
          (fun j => sbEntV k q (stDDec q κ j)) ++ [Val.list [natList (sbInd q (stDDec q κ i)),
            natList ((sbSrt q (stDDec q κ i)).map (k + ·))]]) = sbAcc k q κ (i + 1) := by
        rw [sb_acc_succ, hok, if_pos rfl, hsd]; rfl
      have hnew := StDC.snoc (vs := ((List.range i).filter (sbOk q κ)).map
          fun j => sbEntV k q (stDDec q κ j)) g2' (StDC.mk2 gI gH (by omega) (by omega))
        (by rw [hval]; omega)
      rw [hval] at hnew
      exact hnew)
    (fun hx => by
      have hsd : (sbSrt q (stDDec q κ i)) ≠ (stDDec q κ i) := by simpa using hx
      have hok : sbOk q κ i = false := by simp [sbOk, hsd]
      rw [sb_acc_succ, hok]
      exact g2')
    (by omega)
  have gL2 := StDC.letE gS gite (by omega)
  have gL1 := StDC.letE gdg gL2 (by omega)
  refine gL1.det.mono ?_
  unfold sbSrtK sbShK sbStK at *
  omega


/-- The cost constant of the program. -/
def sbK : ℕ := 10 ^ 14

/-- **The list of the test sets.** On `[k, q, κ]` the program returns the values `tsV k T` of
the test sets `T` in the order `sbOrder q κ`, at cost at most `sbK (Y + 1) ^ 5` for any
`Y ≥ q ^ κ + k + q + κ + 10`. -/
theorem sb_spec {P : Program} {b : ℕ} (h : P.HasAt b (sbFuns b)) {k q κ Y : ℕ} (hq : 0 < q)
    (hY : q ^ κ + k + q + κ + 10 ≤ Y) :
    FunDet P b (.list [.nat k, .nat q, .nat κ]) (.list ((sbOrder q κ).sets.map (tsV k)))
      (sbK * (Y + 1) ^ 5) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := sb_Y_facts hY
  have hentry : P.funs[b]? = some (sbEntry b) := (h.block 0 rfl).single
  have hloop : P.HasAt (b + 1) (loopFuns (b + 1) (.get (.var 0) (.nat 4)) .nil (sbStep b)) :=
    h.block 1 rfl
  have hpow : P.HasAt (b + 4) (stDPowFuns (b + 4)) := h.block 4 rfl
  have hrange : P.HasAt (b + 7) (rangeFuns (b + 7)) := h.block 7 rfl
  have wA := sb_wt_A hY (k := k)
  have wtop := sb_wt_acc hq hY (k := k) (i := q ^ κ) le_rfl
  -- the loop
  have hk : Det P [sbA k q κ] (.get (.var 0) (.nat 4)) (.nat (q ^ κ))
      ((sbA k q κ).wt + 1 + (4 + 3) + (Val.nat (q ^ κ)).wt + 1) :=
    Det.get' (Det.var' rfl) (Det.nat 4) rfl
  have := (sbA k q κ).two_le_size
  have := (sbA k q κ).size_le_wt
  have hL := loopBdd_spec hloop (a := sbA k q κ) hk Det.nil
    (by have := wt_nat_le (q ^ κ); omega) (M := 100 * (Y + 1) ^ 3)
    (Inv := fun i acc => acc = sbAcc k q κ i) (by simp [sbAcc])
    (fun i acc hi hacc => by rw [hacc]; exact sb_wt_acc hq hY hi)
    (D := fun _ => sbStK * (Y + 1) ^ 4) (fun i acc hi hacc => by
      subst hacc
      exact (sbStep_spec h hq hY hi).post fun c hc => ⟨rfl, by beta_reduce; omega⟩)
  have hLd : FunDet P (b + 1) (sbA k q κ) (sbAcc k q κ (q ^ κ)) ((sbStK + 2 * 10 ^ 5) * (Y + 1) ^ 5) := by
    refine hL.mono fun w cost ⟨hw, hc⟩ => ⟨hw, ?_⟩
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
    have e1 : q ^ κ * (sbStK * (Y + 1) ^ 4) ≤ sbStK * (Y + 1) ^ 5 := by
      rw [← f8, mul_left_comm]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
    have e2 : loopModK * (q ^ κ + 1) * ((sbA k q κ).wt + q ^ κ + 100 * (Y + 1) ^ 3 + 1) ≤
        loopModK * ((Y + 1) * (200 * (Y + 1) ^ 3)) := by
      rw [mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
    have e3 : (Y + 1) * (200 * (Y + 1) ^ 3) = 200 * (Y + 1) ^ 4 := by ring
    unfold loopModK at e2 hc
    unfold sbStK at e1 hc ⊢
    omega
  rw [sb_acc_top] at hLd
  -- the entry
  set W := 10 ^ 3 * (Y + 1) ^ 3 with hW
  have wv : (Val.list [.nat k, .nat q, .nat κ]).wt ≤ W := by
    have := wt_list3_le (.nat k) (.nat q) (.nat κ)
    have := wt_nat_le k; have := wt_nat_le q; have := wt_nat_le κ; omega
  have g0 : StDC P [Val.list [.nat k, .nat q, .nat κ]] (arg 0) (.nat k) 3 0 W :=
    StDC.arg rfl wv (by omega) (by have := wt_nat_le k; omega)
  have g1 : StDC P [Val.list [.nat k, .nat q, .nat κ]] (arg 1) (.nat q) 3 0 W :=
    StDC.arg rfl wv (by omega) (by have := wt_nat_le q; omega)
  have g2 : StDC P [Val.list [.nat k, .nat q, .nat κ]] (arg 2) (.nat κ) 3 0 W :=
    StDC.arg rfl wv (by omega) (by have := wt_nat_le κ; omega)
  have wR : (natList (List.range q)).wt ≤ 5 * (Y + 1) ^ 2 := sb_wt_range q Y (by omega)
  have sR : FunDet P (b + 7) (.nat q) (natList (List.range q)) (10 ^ 5 * (Y + 1) ^ 3) := by
    refine (range_spec hrange q).mono fun w cost ⟨hw, hc⟩ => ⟨hw, ?_⟩
    rw [hw] at hc
    have := wt_nat_le q
    have e2 : loopModK * (q + 1) * ((Val.nat q).wt + q + (natList (List.range q)).wt + 1) ≤
        loopModK * ((Y + 1) * (10 * (Y + 1) ^ 2)) := by
      rw [mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
    have e3 : (Y + 1) * (10 * (Y + 1) ^ 2) = 10 * (Y + 1) ^ 3 := by ring
    unfold loopModK at e2 hc
    omega
  have gR := StDC.call g1 sR (by omega)
  have g4 := StDC.mk4 g0 g1 g2 gR (by
    have := wt_list4_le (.nat k) (.nat q) (.nat κ) (natList (List.range q))
    have := wt_nat_le k; have := wt_nat_le q; have := wt_nat_le κ; omega) (by omega)
  have sP : FunDet P (b + 4) (.list [.nat q, .nat κ]) (.nat (q ^ κ)) (10 ^ 8 * (Y + 1) ^ 2) := by
    refine (stDPow_spec hpow hq (X := 3 * Y + 20) (by
      have := wt_list2_le (.nat q) (.nat κ); have := wt_nat_le q; have := wt_nat_le κ
      omega)).mono ?_
    have : (3 * Y + 20 + 1) ^ 2 ≤ (21 * (Y + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    rw [mul_pow] at this
    unfold stDPowK; omega
  have gP := StDC.call (StDC.mk2 g1 g2 (by
    have := wt_list2_le (.nat q) (.nat κ); have := wt_nat_le q; have := wt_nat_le κ; omega)
    (by omega)) sP (by have := wt_nat_le (q ^ κ); omega)
  have gA := StDC.snoc g4 gP (by
    change (sbA k q κ).wt ≤ W; omega)
  have gE := StDC.call gA hLd (by
    have := sb_wt_acc hq hY (k := k) (i := q ^ κ) le_rfl
    rw [sb_acc_top] at this; omega)
  refine StDC.funDet hentry gE ?_
  unfold sbK sbStK
  nlinarith

end GI.Impl
