import Workspace.Impl.AggCmpTup
import Workspace.Impl.AggSubProg

/-!
# The list of the test tuples, as a program

`cmTFuns b` (22 functions at `b`) on `[q, κ]` returns the list of the values `stTT a` of the
ordered test tuples `a`, in the order `cmTupOrder q κ hq` (`cmT_spec`). The comparison phase runs
over the pairs of this list, and hands the list to the items (`itSt`).

The program runs over the numbers `j < 2 q ^ κ`. For each `j` the digit program
(`stDDec_spec`) returns the pair `[j / q ^ κ, digits of j]`. The program lists the labels that
occur among the digits (`sbSrt_spec`) and keeps the pair when this list has `κ` entries, that is,
when the digits are distinct (`cm_ok_iff`). A kept pair is `stTT` of the tuple of `j`
(`cm_tt_eq`). No primitive is called.

Its cost is at most `cmTK (Y + 1) ^ 5` for any `Y ≥ 2 q ^ κ + q + κ + 10`. Since `κ` is a constant
of the round, this is polynomial in the input of the round.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang
open GI.Cited (Val)
open GI.Machine (BinOp)

variable {q κ : ℕ}

/-! ### The value of a kept number -/

/-- The pair that the digit program returns on `j`. -/
def cmTPair (q κ j : ℕ) : Val := .list [.nat (j / q ^ κ), natList (stDDec q κ j)]

theorem cm_div_eq (hq : 0 < q) {j : ℕ} (hj : j < 2 * q ^ κ) :
    j / q ^ κ = (decide (q ^ κ ≤ j)).toNat := by
  have hpos : 0 < q ^ κ := pow_pos hq _
  by_cases h : q ^ κ ≤ j
  · simp only [h, decide_true, Bool.toNat_true]
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  · simp only [h, decide_false, Bool.toNat_false]
    exact Nat.div_eq_of_lt (by omega)

/-- **A kept pair is the value of its test tuple.** -/
theorem cm_tt_eq (hq : 0 < q) {j : ℕ} (hj : j < 2 * q ^ κ) (hok : cmTupOk q κ j = true) :
    (cmTupOf (κ := κ) hq j).map stTT = some (cmTPair q κ j) := by
  rw [cmTupOf, dif_pos ⟨hok, hj⟩]
  simp only [Option.map_some, Option.some.injEq]
  unfold stTT stTv cmTPair
  rw [cm_div_eq hq hj, cm_dec_eq hq]
  rfl

theorem cm_tups_map_aux (hq : 0 < q) (l : List ℕ) (hl : ∀ j ∈ l, j < 2 * q ^ κ) :
    (l.filterMap (cmTupOf (κ := κ) hq)).map stTT = (l.filter (cmTupOk q κ)).map (cmTPair q κ) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    have ih' := ih fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have hj := hl j List.mem_cons_self
    by_cases hok : cmTupOk q κ j = true
    · have e := cm_tt_eq hq hj hok
      obtain ⟨a, ha, ha'⟩ := Option.map_eq_some_iff.1 e
      rw [List.filterMap_cons, ha, List.filter_cons_of_pos hok]
      simp only [List.map_cons, ha', ih']
    · have hn : cmTupOf (κ := κ) hq j = none := by
        rw [cmTupOf, dif_neg (fun h => hok h.1)]
      rw [List.filterMap_cons, hn, List.filter_cons_of_neg hok]
      exact ih'

/-- The values of the test tuples of `cmTupOrder`, as the program lists them. -/
theorem cm_order_vals (hq : 0 < q) :
    ((List.range (2 * q ^ κ)).filter (cmTupOk q κ)).map (cmTPair q κ) =
      (cmTupOrder q κ hq).tuples.map stTT :=
  (cm_tups_map_aux hq _ fun _ hj => List.mem_range.1 hj).symm

/-! ### The program -/

/-- **The step of the loop** on `[a, j, acc]`, `a = [q, κ, [0, …, q - 1], 2 q ^ κ]`: the pair
`[j / q ^ κ, digits d of j]`, the labels of `d`, and, when they are `κ`, the pair added to `acc`. -/
def cmTStep (b : ℕ) : Expr :=
  .letE (.call (b + 10) (mk3 (mk2 (arg 1) .nil) (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))))
    (.ite (.arith .eq (.length (.call (b + 13) (mk2 (.get (.var 1) (.nat 1)) (.get (arg 0) (.nat 2)))))
        (.get (arg 0) (.nat 1)))
      (.snoc (arg 2) (.var 1))
      (arg 2))

/-- The entry on `[q, κ]`: the loop on `[q, κ, [0, …, q - 1], 2 q ^ κ]`. -/
def cmTEntry (b : ℕ) : Expr :=
  .call (b + 1) (mk4 (arg 0) (arg 1) (.call (b + 7) (arg 0))
    (.arith .mul (.nat 2) (.call (b + 4) (mk2 (arg 0) (arg 1)))))

/-- **The program of the test tuples** at `b` (22 functions). -/
def cmTFuns (b : ℕ) : List Expr :=
  [cmTEntry b] ++ loopFuns (b + 1) (.get (.var 0) (.nat 3)) .nil (cmTStep b) ++
    stDPowFuns (b + 4) ++ rangeFuns (b + 7) ++ stDDecFuns (b + 10) ++
    filterFuns (b + 13) (b + 16) ++ [sbPredF (b + 17)] ++ countFuns (b + 17)

/-- The accumulator after the numbers `j < i`. -/
def cmTAcc (q κ i : ℕ) : Val := .list (((List.range i).filter (cmTupOk q κ)).map (cmTPair q κ))

theorem cm_acc_succ (q κ i : ℕ) :
    cmTAcc q κ (i + 1) = if cmTupOk q κ i then
      .list (((List.range i).filter (cmTupOk q κ)).map (cmTPair q κ) ++ [cmTPair q κ i])
      else cmTAcc q κ i := by
  unfold cmTAcc
  rw [List.range_succ, List.filter_append]
  cases h : cmTupOk q κ i <;> simp [h]

theorem cm_acc_top (hq : 0 < q) :
    cmTAcc q κ (2 * q ^ κ) = .list ((cmTupOrder q κ hq).tuples.map stTT) := by
  rw [← cm_order_vals hq]; rfl

/-- The context of the loop. -/
def cmTA (q κ : ℕ) : Val := .list [.nat q, .nat κ, natList (List.range q), .nat (2 * q ^ κ)]

section Wt

variable {Y : ℕ}

theorem cm_wt_pair (hq : 0 < q) (hY : 2 * q ^ κ + q + κ + 10 ≤ Y) {j : ℕ} (hj : j < 2 * q ^ κ) :
    (cmTPair q κ j).wt ≤ 20 * (Y + 1) ^ 2 := by
  obtain ⟨h1, h2, -⟩ := sb_Y_facts (k := 0) (q := q) (κ := κ) (Y := Y) (by
    have : q ^ κ ≤ 2 * q ^ κ := by omega
    omega)
  have wdg : (natList (stDDec q κ j)).wt ≤ 5 * (Y + 1) ^ 2 :=
    wt_natList_le_sq (fun x hx => by have := stDDec_lt hq x hx; omega)
      (by rw [stDDec_length]; omega)
  have := wt_list2_le (.nat (j / q ^ κ)) (natList (stDDec q κ j))
  have := wt_nat_le (j / q ^ κ)
  have := Nat.div_le_self j (q ^ κ)
  unfold cmTPair
  omega

theorem cm_wt_acc (hq : 0 < q) (hY : 2 * q ^ κ + q + κ + 10 ≤ Y) {i : ℕ} (hi : i ≤ 2 * q ^ κ) :
    (cmTAcc q κ i).wt ≤ 100 * (Y + 1) ^ 3 := by
  obtain ⟨h1, h2, h3, -, -, h6, -⟩ := sb_Y_facts (k := 0) (q := q) (κ := κ) (Y := Y) (by
    have : q ^ κ ≤ 2 * q ^ κ := by omega
    omega)
  have hl : (((List.range i).filter (cmTupOk q κ)).map (cmTPair q κ)).length ≤ Y := by
    simp only [List.length_map]
    exact (List.length_filter_le _ _).trans (by simp; omega)
  have h := cp_wt_list hl (c := 20 * (Y + 1) ^ 2) (by
    intro v hv
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hv
    have := List.mem_range.1 (List.mem_filter.1 hj).1
    exact cm_wt_pair hq hY (by omega))
  unfold cmTAcc
  have : Y * (2 * (20 * (Y + 1) ^ 2) + 1) ≤ (Y + 1) * (41 * (Y + 1) ^ 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e : (Y + 1) * (41 * (Y + 1) ^ 2) = 41 * (Y + 1) ^ 3 := by ring
  omega

theorem cm_wt_A (hY : 2 * q ^ κ + q + κ + 10 ≤ Y) : (cmTA q κ).wt ≤ 30 * (Y + 1) ^ 2 := by
  obtain ⟨h1, h2, -⟩ := sb_Y_facts (k := 0) (q := q) (κ := κ) (Y := Y) (by
    have : q ^ κ ≤ 2 * q ^ κ := by omega
    omega)
  have a1 : (natList (List.range q)).wt ≤ 5 * (Y + 1) ^ 2 := sb_wt_range q Y (by omega)
  have := wt_list4_le (.nat q) (.nat κ) (natList (List.range q)) (.nat (2 * q ^ κ))
  have := wt_nat_le q; have := wt_nat_le κ; have := wt_nat_le (2 * q ^ κ)
  unfold cmTA
  omega

end Wt

/-- The cost constant of one step. -/
def cmTStK : ℕ := 10 ^ 13

/-- **One step of the loop.** -/
theorem cmTStep_spec {P : Program} {b : ℕ} (h : P.HasAt b (cmTFuns b)) {q κ Y : ℕ}
    (hq : 0 < q) (hY : 2 * q ^ κ + q + κ + 10 ≤ Y) {i : ℕ} (hi : i < 2 * q ^ κ) :
    Det P [.list [cmTA q κ, .nat i, cmTAcc q κ i]] (cmTStep b) (cmTAcc q κ (i + 1))
      (cmTStK * (Y + 1) ^ 4) := by
  obtain ⟨f1, f2, f3, f4, -, f6, f7, -⟩ := sb_Y_facts (k := 0) (q := q) (κ := κ) (Y := Y) (by
    have : q ^ κ ≤ 2 * q ^ κ := by omega
    omega)
  have hdec : P.HasAt (b + 10) (stDDecFuns (b + 10)) := h.block 10 rfl
  have hfil : P.HasAt (b + 13) (filterFuns (b + 13) (b + 16)) := h.block 13 rfl
  have hpred : P.funs[b + 16]? = some (sbPredF (b + 17)) := (h.block 16 rfl).single
  have hcnt : P.HasAt (b + 17) (countFuns (b + 17)) := h.block 17 rfl
  have hdgq : ∀ x ∈ stDDec q κ i, x < q := stDDec_lt hq
  have hdgl : (stDDec q κ i).length = κ := stDDec_length q κ i
  have hsq : ∀ x ∈ sbSrt q (stDDec q κ i), x < q := fun x hx => (sb_mem_srt.1 hx).1
  have hsl : (sbSrt q (stDDec q κ i)).length ≤ q := (List.length_filter_le _ _).trans (by simp)
  have wA := cm_wt_A hY (q := q) (κ := κ)
  have wacc := cm_wt_acc hq hY (le_of_lt hi)
  have wacc1 := cm_wt_acc hq hY (i := i + 1) (by omega)
  have wpair := cm_wt_pair hq hY hi
  have wdg : (natList (stDDec q κ i)).wt ≤ 5 * (Y + 1) ^ 2 :=
    wt_natList_le_sq (fun x hx => by have := hdgq x hx; omega) (by omega)
  have wsrt : (natList (sbSrt q (stDDec q κ i))).wt ≤ 5 * (Y + 1) ^ 2 :=
    wt_natList_le_sq (fun x hx => by have := hsq x hx; omega) (by omega)
  have wR : (natList (List.range q)).wt ≤ 5 * (Y + 1) ^ 2 := sb_wt_range q Y (by omega)
  have wi := wt_nat_le i
  have wq := wt_nat_le q
  have wκ := wt_nat_le κ
  have hiY : i ≤ Y := by omega
  set W := 10 ^ 4 * (Y + 1) ^ 3 with hW
  have wenv : (Val.list [(cmTA q κ), .nat i, (cmTAcc q κ i)]).wt ≤ W := by
    have := wt_list3_le (cmTA q κ) (.nat i) (cmTAcc q κ i); omega
  -- the digits
  have g0 : StDC P [Val.list [(cmTA q κ), .nat i, (cmTAcc q κ i)]] (arg 0) (cmTA q κ) 3 0 W :=
    StDC.arg rfl wenv (by omega) (by omega)
  have g1 : StDC P [Val.list [(cmTA q κ), .nat i, (cmTAcc q κ i)]] (arg 1) (.nat i) 3 0 W :=
    StDC.arg rfl wenv (by omega) (by omega)
  have gp := StDC.mk2 g1 (StDC.nil (by omega))
    (by have := wt_list2_le (.nat i) (.list []); simp only [wt_list_nil] at this; omega)
    (by omega)
  have gq := StDC.get (v := .nat q) g0 (StDC.nat 0 (by omega)) rfl (by omega)
  have gκ := StDC.get (v := .nat κ) g0 (StDC.nat 1 (by omega)) rfl (by omega)
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
  have gc := StDC.call gD sD (by unfold cmTPair at wpair; omega)
  -- the labels of the digits, and their number
  set env1 := [Val.list [(cmTA q κ), .nat i, (cmTAcc q κ i)], cmTPair q κ i] with henv1
  have g0' : StDC P env1 (arg 0) (cmTA q κ) 3 0 W := StDC.arg rfl wenv (by omega) (by omega)
  have g2' : StDC P env1 (arg 2) (cmTAcc q κ i) 3 0 W := StDC.arg rfl wenv (by omega) (by omega)
  have gR := StDC.get (v := natList (List.range q)) g0' (StDC.nat 2 (by omega)) rfl (by omega)
  have gκ' := StDC.get (v := .nat κ) g0' (StDC.nat 1 (by omega)) rfl (by omega)
  have gv1 : StDC P env1 (.var 1) (cmTPair q κ i) 1 0 W := StDC.var' rfl (by omega)
  have gdg := StDC.get (v := natList (stDDec q κ i)) gv1 (StDC.nat 1 (by omega)) rfl (by omega)
  have gm := StDC.mk2 gdg gR
    (by have := wt_list2_le (natList (stDDec q κ i)) (natList (List.range q)); omega) (by omega)
  have sS := sbSrt_spec hfil hpred hcnt (d := (stDDec q κ i)) (q := q) (Y := Y)
    (fun x hx => by have := hdgq x hx; omega) (by omega) (by omega)
  have gS := StDC.call gm sS (by omega)
  have gL := StDC.length (vs := (sbSrt q (stDDec q κ i)).map Val.nat) gS
    (by simp only [List.length_map]; omega)
  have gT := StDC.arith' gL gκ' (op := .eq)
    (z := (decide ((sbSrt q (stDDec q κ i)).length = κ)).toNat) (by
      simp only [BinOp.eval, List.length_map]
      split_ifs with hx <;> simp [hx]) (by
      have := Bool.toNat_le (decide ((sbSrt q (stDDec q κ i)).length = κ)); omega)
  have gite := StDC.ite (v := cmTAcc q κ (i + 1)) gT
    (fun hx => by
      have hok : cmTupOk q κ i = true := by
        unfold cmTupOk; cases hd : decide ((sbSrt q (stDDec q κ i)).length = κ) <;> simp_all
      have hval : Val.list (((List.range i).filter (cmTupOk q κ)).map (cmTPair q κ) ++
          [cmTPair q κ i]) = cmTAcc q κ (i + 1) := by
        rw [cm_acc_succ, hok, if_pos rfl]
      have hnew := StDC.snoc (vs := ((List.range i).filter (cmTupOk q κ)).map (cmTPair q κ))
        g2' gv1 (by rw [hval]; omega)
      rw [hval] at hnew
      exact hnew)
    (fun hx => by
      have hok : cmTupOk q κ i = false := by
        unfold cmTupOk; cases hd : decide ((sbSrt q (stDDec q κ i)).length = κ) <;> simp_all
      rw [cm_acc_succ, hok]
      exact g2')
    (by omega)
  have gL1 := StDC.letE gc gite (by omega)
  refine gL1.det.mono ?_
  unfold sbSrtK cmTStK at *
  omega

/-- The cost constant of the program. -/
def cmTK : ℕ := 10 ^ 14

/-- **The list of the test tuples.** On `[q, κ]` the program returns the values `stTT a` of the
ordered test tuples `a` in the order `cmTupOrder q κ hq`, at cost at most `cmTK (Y + 1) ^ 5` for
any `Y ≥ 2 q ^ κ + q + κ + 10`. -/
theorem cmT_spec {P : Program} {b : ℕ} (h : P.HasAt b (cmTFuns b)) {q κ Y : ℕ} (hq : 0 < q)
    (hY : 2 * q ^ κ + q + κ + 10 ≤ Y) :
    FunDet P b (.list [.nat q, .nat κ]) (.list ((cmTupOrder q κ hq).tuples.map stTT))
      (cmTK * (Y + 1) ^ 5) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := sb_Y_facts (k := 0) (q := q) (κ := κ) (Y := Y) (by
    have : q ^ κ ≤ 2 * q ^ κ := by omega
    omega)
  have hentry : P.funs[b]? = some (cmTEntry b) := (h.block 0 rfl).single
  have hloop : P.HasAt (b + 1) (loopFuns (b + 1) (.get (.var 0) (.nat 3)) .nil (cmTStep b)) :=
    h.block 1 rfl
  have hpow : P.HasAt (b + 4) (stDPowFuns (b + 4)) := h.block 4 rfl
  have hrange : P.HasAt (b + 7) (rangeFuns (b + 7)) := h.block 7 rfl
  have wA := cm_wt_A hY (q := q) (κ := κ)
  have wtop := cm_wt_acc hq hY (i := 2 * q ^ κ) le_rfl
  -- the loop
  have hk : Det P [cmTA q κ] (.get (.var 0) (.nat 3)) (.nat (2 * q ^ κ))
      ((cmTA q κ).wt + 1 + (3 + 3) + (Val.nat (2 * q ^ κ)).wt + 1) :=
    Det.get' (Det.var' rfl) (Det.nat 3) rfl
  have := (cmTA q κ).two_le_size
  have := (cmTA q κ).size_le_wt
  have hL := loopBdd_spec hloop (a := cmTA q κ) hk Det.nil
    (by have := wt_nat_le (2 * q ^ κ); omega) (M := 100 * (Y + 1) ^ 3)
    (Inv := fun i acc => acc = cmTAcc q κ i) (by simp [cmTAcc])
    (fun i acc hi hacc => by rw [hacc]; exact cm_wt_acc hq hY hi)
    (D := fun _ => cmTStK * (Y + 1) ^ 4) (fun i acc hi hacc => by
      subst hacc
      exact (cmTStep_spec h hq hY hi).post fun c hc => ⟨rfl, by beta_reduce; omega⟩)
  have hLd : FunDet P (b + 1) (cmTA q κ) (cmTAcc q κ (2 * q ^ κ))
      ((cmTStK + 2 * 10 ^ 5) * (Y + 1) ^ 5) := by
    refine hL.mono fun w cost ⟨hw, hc⟩ => ⟨hw, ?_⟩
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
    have e1 : 2 * q ^ κ * (cmTStK * (Y + 1) ^ 4) ≤ cmTStK * (Y + 1) ^ 5 := by
      rw [← f8, mul_left_comm]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
    have e2 : loopModK * (2 * q ^ κ + 1) * ((cmTA q κ).wt + 2 * q ^ κ + 100 * (Y + 1) ^ 3 + 1) ≤
        loopModK * ((Y + 1) * (200 * (Y + 1) ^ 3)) := by
      rw [mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
    have e3 : (Y + 1) * (200 * (Y + 1) ^ 3) = 200 * (Y + 1) ^ 4 := by ring
    unfold loopModK at e2 hc
    unfold cmTStK at e1 hc ⊢
    omega
  rw [cm_acc_top hq] at hLd
  -- the entry
  set W := 10 ^ 3 * (Y + 1) ^ 3 with hW
  have wv : (Val.list [.nat q, .nat κ]).wt ≤ W := by
    have := wt_list2_le (.nat q) (.nat κ)
    have := wt_nat_le q; have := wt_nat_le κ; omega
  have g0 : StDC P [Val.list [.nat q, .nat κ]] (arg 0) (.nat q) 3 0 W :=
    StDC.arg rfl wv (by omega) (by have := wt_nat_le q; omega)
  have g1 : StDC P [Val.list [.nat q, .nat κ]] (arg 1) (.nat κ) 3 0 W :=
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
  have gR := StDC.call g0 sR (by omega)
  have sP : FunDet P (b + 4) (.list [.nat q, .nat κ]) (.nat (q ^ κ)) (10 ^ 8 * (Y + 1) ^ 2) := by
    refine (stDPow_spec hpow hq (X := 3 * Y + 20) (by
      have := wt_list2_le (.nat q) (.nat κ); have := wt_nat_le q; have := wt_nat_le κ
      omega)).mono ?_
    have : (3 * Y + 20 + 1) ^ 2 ≤ (21 * (Y + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    rw [mul_pow] at this
    unfold stDPowK; omega
  have gP := StDC.call (StDC.mk2 g0 g1 (by
    have := wt_list2_le (.nat q) (.nat κ); have := wt_nat_le q; have := wt_nat_le κ; omega)
    (by omega)) sP (by have := wt_nat_le (q ^ κ); omega)
  have g2 := StDC.arith' (StDC.nat 2 (by omega)) gP (op := .mul) (z := 2 * q ^ κ) rfl (by omega)
  have g4 := StDC.mk4 g0 g1 gR g2 (by change (cmTA q κ).wt ≤ W; omega) (by omega)
  have gE := StDC.call g4 hLd (by
    have := cm_wt_acc hq hY (i := 2 * q ^ κ) le_rfl
    rw [cm_acc_top hq] at this; omega)
  refine StDC.funDet hentry gE ?_
  unfold cmTK cmTStK
  nlinarith

end GI.Impl
