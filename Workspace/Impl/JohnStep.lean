import Workspace.Impl.JohnC

/-!
# One step over the pairs

`johnStepF` performs `johnStep` on values (`john_stepF_spec`): on the pair with index `p`, if its
label is `υ`, it computes `C(p / n, p % n)` and adds it to the list unless it is there.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

/-- A number read from a value (`0` for a list). -/
def johnNatOf : Val → ℕ
  | .nat a => a
  | .list _ => 0

/-- A list of numbers read from a value. -/
def johnNats : Val → List ℕ
  | .list ws => ws.map johnNatOf
  | .nat _ => []

theorem john_nats_natList (l : List ℕ) : johnNats (natList l) = l := by
  simp [johnNats, natList, List.map_map, Function.comp_def, johnNatOf]

/-- The test of the search for a set `cl`. -/
def johnQE (cl : List ℕ) (w : Val) : Bool := decide (johnNats w = cl)

/-- The shape of the list of sets kept so far: at most `n` lists of `n` bits. -/
structure JohnAccOK (n : ℕ) (accL : List (List ℕ)) : Prop where
  len : accL.length ≤ n
  ent : ∀ v ∈ accL, v.length = n ∧ ∀ b ∈ v, b ≤ 1

theorem john_wt_bitsN {v : List ℕ} {n : ℕ} (hv : v.length = n ∧ ∀ b ∈ v, b ≤ 1) :
    (natList v).wt ≤ 7 * n + 4 := by
  have := john_wt_bits hv.2; rw [hv.1] at this; omega

theorem john_wt_acc {n : ℕ} {accL : List (List ℕ)} (h : JohnAccOK n accL) :
    (Val.list (accL.map natList)).wt ≤ 20 * (n + 1) ^ 2 := by
  have := john_wt_list_le (vs := accL.map natList) (B := 7 * n + 4) (by
    intro w hw; obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw; exact john_wt_bitsN (h.ent v hv))
  simp only [List.length_map] at this
  have := h.len
  have : accL.length * (2 * (7 * n + 4) + 1) ≤ n * (2 * (7 * n + 4) + 1) :=
    Nat.mul_le_mul_right _ h.len
  nlinarith

/-- **The equality test.** -/
theorem john_eqF_spec {n : ℕ} {cl vl : List ℕ} (hc : cl.length = n ∧ ∀ b ∈ cl, b ≤ 1)
    (hv : vl.length = n ∧ ∀ b ∈ vl, b ≤ 1) :
    FunDet johnProgram 94 (.list [natList cl, natList vl]) (boolVal (johnQE cl (natList vl)))
      (200000 * (n + 1) ^ 2) := by
  set a := Val.list [natList cl, natList vl]
  have h0 : Det johnProgram [a] (arg 0) (natList cl) (2 * a.wt + 5) := Det.arg' rfl
  have h1 : Det johnProgram [a] (arg 1) (natList vl) (2 * a.wt + 6) := Det.arg' rfl
  have hcall := Det.call (Det.mk2 h1 h0) (eqNats_spec john_at_eqNats vl cl)
  have hq : johnQE cl (natList vl) = decide (vl = cl) := by
    simp [johnQE, john_nats_natList]
  rw [← hq] at hcall
  refine FunDet.intro john_at_eqF.single (hcall.mono ?_)
  have wc := john_wt_bitsN hc
  have wv := john_wt_bitsN hv
  have e1 := wt_list2_le (natList cl) (natList vl)
  have e2 := wt_list2_le (natList vl) (natList cl)
  have ea : a.wt = (Val.list [natList cl, natList vl]).wt := rfl
  have w9 : (Val.nat (johnQE cl (natList vl)).toNat).wt ≤ 3 := wt_boolVal_le _
  have w10 := wt_boolVal_le (johnQE cl (natList vl))
  have hA : (Val.list [natList vl, natList cl]).wt + vl.length + 4 ≤ 100 * (n + 1) := by omega
  have p : loopModK * (vl.length + 1) * ((Val.list [natList vl, natList cl]).wt + vl.length + 4)
      ≤ 1000 * (100 * (n + 1) ^ 2) := by
    rw [Nat.mul_assoc]
    refine Nat.mul_le_mul_left _ ?_
    calc (vl.length + 1) * ((Val.list [natList vl, natList cl]).wt + vl.length + 4) ≤
        (n + 1) * (100 * (n + 1)) :=
          Nat.mul_le_mul (by omega) hA
      _ = 100 * (n + 1) ^ 2 := by ring
  have y0 : n + 1 ≤ (n + 1) ^ 2 := by nlinarith
  omega

end GI.Impl

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

/-- **The search for a set.** -/
theorem john_anyEq_spec {n : ℕ} {cl : List ℕ} {accL : List (List ℕ)}
    (hc : cl.length = n ∧ ∀ b ∈ cl, b ≤ 1) (ha : JohnAccOK n accL) :
    FunDet johnProgram 91 (.list [natList cl, .list (accL.map natList)])
      (boolVal (accL.any fun v => decide (v = cl))) (500000 * (n + 1) ^ 3) := by
  have hA := any_spec john_at_anyEq (c := natList cl) (xs := accL.map natList)
    (q := johnQE cl) (B := fun _ => 200000 * (n + 1) ^ 2) (by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
      exact john_eqF_spec hc (ha.ent v hv))
  have e : (accL.map natList).any (johnQE cl) = accL.any fun v => decide (v = cl) := by
    rw [List.any_map]
    congr 1
    funext v
    simp [johnQE, john_nats_natList]
  refine hA.mono ?_
  rintro w cost ⟨rfl, hc'⟩
  refine ⟨by rw [e], hc'.trans ?_⟩
  have hsum := john_sum_le (l := accL.map natList)
    (f := fun _ => 200000 * (n + 1) ^ 2) (B := 200000 * (n + 1) ^ 2) fun _ _ => le_rfl
  simp only [List.length_map] at hsum ⊢
  have wc := john_wt_bitsN hc
  have wa := john_wt_acc ha
  have e1 := wt_list2_le (natList cl) (.list (accL.map natList))
  have hl := ha.len
  have y0 : n + 1 ≤ (n + 1) ^ 2 := by nlinarith
  have hA' : (Val.list [natList cl, .list (accL.map natList)]).wt + accL.length + 4 ≤
      100 * (n + 1) ^ 2 := by omega
  have p1 : accL.length * (200000 * (n + 1) ^ 2) ≤ 200000 * (n + 1) ^ 3 := by
    calc accL.length * (200000 * (n + 1) ^ 2) ≤ (n + 1) * (200000 * (n + 1) ^ 2) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 200000 * (n + 1) ^ 3 := by ring
  have p2 : loopModK * (accL.length + 1) *
      ((Val.list [natList cl, .list (accL.map natList)]).wt + accL.length + 4) ≤
      1000 * (100 * (n + 1) ^ 3) := by
    rw [Nat.mul_assoc]
    refine Nat.mul_le_mul_left _ ?_
    calc (accL.length + 1) * ((Val.list [natList cl, .list (accL.map natList)]).wt +
        accL.length + 4) ≤ (n + 1) * (100 * (n + 1) ^ 2) := Nat.mul_le_mul (by omega) hA'
      _ = 100 * (n + 1) ^ 3 := by ring
  omega

theorem john_sq_le4 (n : ℕ) : n * n ≤ (n + 1) ^ 4 := by nlinarith

theorem john_le_sq (n : ℕ) : n + 1 ≤ (n + 1) ^ 2 := by nlinarith

/-- The context of the step: `[D, labL, n, υ, Rn]`. -/
def johnCtxV (n : ℕ) (labL : List ℕ) (δ υ : ℕ) : Val :=
  .list [johnDV n labL δ, natList labL, .nat n, .nat υ, natList (List.range n)]

theorem john_C_shape (n : ℕ) (labL : List ℕ) (δ x y : ℕ) :
    (johnC n labL δ x y).length = n ∧ ∀ b ∈ johnC n labL δ x y, b ≤ 1 := by
  refine ⟨by simp [johnC], fun b hb => ?_⟩
  simp only [johnC, List.mem_map] at hb
  obtain ⟨r, -, rfl⟩ := hb
  exact Bool.toNat_le _

theorem john_step_val (n : ℕ) (labL : List ℕ) (δ υ : ℕ) (accL : List (List ℕ)) (p : ℕ) :
    (if BinOp.eval .eq (labL.getD p 0) υ = 0 then Val.list (accL.map natList) else
      (if (accL.any fun v => decide (v = johnC n labL δ (p / n) (p % n))).toNat = 0 then
        Val.list (accL.map natList ++ [natList (johnC n labL δ (p / n) (p % n))])
      else Val.list (accL.map natList))) =
      .list ((johnStep n labL δ υ accL p).map natList) := by
  unfold johnStep
  show (if (if labL.getD p 0 = υ then 1 else 0) = 0 then _ else _) = _
  by_cases h1 : labL.getD p 0 = υ
  · simp only [List.getD_eq_getElem?_getD] at h1
    cases hb : accL.any fun v => decide (v = johnC n labL δ (p / n) (p % n)) <;> simp_all
  · simp only [List.getD_eq_getElem?_getD] at h1
    simp [h1]

/-- **One step over the pairs.** -/
theorem john_stepF_spec {n : ℕ} {labL : List ℕ} {δ υ : ℕ} (hL : JohnLabOK n labL δ)
    (hυ : υ ≤ n * n) {accL : List (List ℕ)} (ha : JohnAccOK n accL) {p : ℕ} (hp : p < n * n) :
    FunDet johnProgram 77 (.list [johnCtxV n labL δ υ, .list (accL.map natList), .nat p])
      (.list ((johnStep n labL δ υ accL p).map natList)) (10000000 * (n + 1) ^ 4) := by
  have hn : 0 < n := Nat.pos_of_mul_pos_left (Nat.zero_lt_of_lt hp)
  have hx : p / n < n := Nat.div_lt_of_lt_mul hp
  have hy : p % n < n := Nat.mod_lt _ hn
  set ctx := johnCtxV n labL δ υ
  set accV := Val.list (accL.map natList)
  set a := Val.list [ctx, accV, .nat p]
  set Cl := johnC n labL δ (p / n) (p % n)
  have hc : Det johnProgram [a] (arg 0) ctx (2 * a.wt + 5) := Det.arg' rfl
  have hA : Det johnProgram [a] (arg 1) accV (2 * a.wt + 6) := Det.arg' rfl
  have hP : Det johnProgram [a] (arg 2) (.nat p) (2 * a.wt + 7) := Det.arg' rfl
  have g0 := Det.get' hc (Det.nat 0)
    (show [johnDV n labL δ, natList labL, .nat n, .nat υ, natList (List.range n)][0]? =
      some (johnDV n labL δ) from rfl)
  have g1 := Det.get' hc (Det.nat 1)
    (show [johnDV n labL δ, natList labL, .nat n, .nat υ, natList (List.range n)][1]? =
      some (natList labL) from rfl)
  have g2 := Det.get' hc (Det.nat 2)
    (show [johnDV n labL δ, natList labL, .nat n, .nat υ, natList (List.range n)][2]? =
      some (.nat n) from rfl)
  have g3 := Det.get' hc (Det.nat 3)
    (show [johnDV n labL δ, natList labL, .nat n, .nat υ, natList (List.range n)][3]? =
      some (.nat υ) from rfl)
  have g4 := Det.get' hc (Det.nat 4)
    (show [johnDV n labL δ, natList labL, .nat n, .nat υ, natList (List.range n)][4]? =
      some (natList (List.range n)) from rfl)
  have hlp : (labL.map Val.nat)[p]? = some (.nat (labL.getD p 0)) := by
    rw [List.getElem?_map, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [hL.len]; exact hp)]
    rfl
  have hcond := Det.arith (op := .eq) (Det.get' g1 hP hlp) g3
  -- The call of `C`.
  have hdiv := Det.arith (op := .div) hP g2
  have hmod := Det.arith (op := .mod) hP g2
  have hC := Det.call (Det.mk4 g0 g4 hdiv hmod) (john_compC_spec (labL := labL) (δ := δ) hx hy)
  -- The search, in the environment `[a, C]`.
  have hA' : Det johnProgram [a, natList Cl] (arg 1) accV (2 * a.wt + 6) := Det.arg' rfl
  have hCv : Det johnProgram [a, natList Cl] (.var 1) (natList Cl) ((natList Cl).wt + 1) :=
    Det.var' rfl
  have hany := Det.call (Det.mk2 hCv hA') (john_anyEq_spec (john_C_shape n labL δ _ _) ha)
  have hin := john_det_ite hany hA' (Det.snoc hA' hCv)
  have hlet := Det.letE hC hin
  have hout := john_det_ite hcond hlet hA
  have hval := john_step_val n labL δ υ accL p
  rw [hval] at hout
  refine FunDet.intro john_at_stepF.single (hout.mono ?_)
  -- The bound.
  have wD := john_wt_DV n labL δ
  have wl := john_wt_natList_sq hL.len hL.le
  have wR := john_wt_Rn n
  have wC := john_wt_C (n := n) (labL := labL) (δ := δ) (p / n) (p % n)
  have wa := john_wt_acc ha
  have ha2 : JohnAccOK n (johnStep n labL δ υ accL p) ∨ True := Or.inr trivial
  have wo : (Val.list ((johnStep n labL δ υ accL p).map natList)).wt ≤
      (Val.list (accL.map natList)).wt + 2 * (natList Cl).wt + 2 := by
    unfold johnStep
    split
    · rw [List.map_append]; exact wt_list_snoc_le _ _
    · omega
  have ec : ctx.wt = (Val.list [johnDV n labL δ, natList labL, .nat n, .nat υ,
    natList (List.range n)]).wt := rfl
  have e1 := wt_list_le [johnDV n labL δ, natList labL, .nat n, .nat υ, natList (List.range n)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at e1
  have e2 := wt_list3_le ctx accV (.nat p)
  have ea : a.wt = (Val.list [ctx, accV, .nat p]).wt := rfl
  have e3 := wt_list4_le (johnDV n labL δ) (natList (List.range n)) (.nat (BinOp.eval .div p n))
    (.nat (BinOp.eval .mod p n))
  have e4 := wt_list2_le (natList Cl) accV
  have e5 := wt_list_snoc_le (accL.map natList) (natList Cl)
  have w1 := wt_nat_le n; have w2 := wt_nat_le υ; have w3 := wt_nat_le p
  have w4 := wt_nat_le (BinOp.eval .div p n); have w5 := wt_nat_le (BinOp.eval .mod p n)
  have w6 := wt_nat_le (labL.getD p 0)
  have w7 : (Val.nat (BinOp.eval .eq (labL.getD p 0) υ)).wt ≤ 3 := by
    simp only [BinOp.eval]; split <;> simp [wt_nat, GI.Machine.len_zero]
  have w8 : (Val.nat (accL.any fun v => decide (v = Cl)).toNat).wt ≤ 3 := wt_boolVal_le _
  have w0 := wt_nat_le 0; have w01 := wt_nat_le 1; have w02 := wt_nat_le 2
  have w03 := wt_nat_le 3; have w04 := wt_nat_le 4
  have hdl : BinOp.eval .div p n ≤ n := by simp only [BinOp.eval]; omega
  have hml : BinOp.eval .mod p n ≤ n := by simp only [BinOp.eval]; omega
  have hgl : labL.getD p 0 ≤ n * n := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hL.len]; exact hp)]
    exact hL.le _ (List.getElem_mem _)
  have y1 := john_sq_le4 n
  have y0 := john_le_sq n
  have y24 : (n + 1) ^ 2 ≤ (n + 1) ^ 4 := john_pow_le (by omega) (by omega)
  have y34 : (n + 1) ^ 3 ≤ (n + 1) ^ 4 := john_pow_le (by omega) (by omega)
  have wC' : (natList (johnC n labL δ (BinOp.eval .div p n) (BinOp.eval .mod p n))).wt ≤
      7 * n + 4 := john_wt_C _ _
  have w8' : (boolVal (accL.any fun v => decide (v = Cl))).wt ≤ 3 := wt_boolVal_le _
  have eaV : accV.wt = (Val.list (accL.map natList)).wt := rfl
  have eC : (natList Cl).wt = (natList (johnC n labL δ (p / n) (p % n))).wt := rfl
  have wi : (if (accL.any fun v => decide (v = Cl)).toNat = 0 then
      Val.list (List.map natList accL ++ [natList Cl]) else accV).wt ≤
      (Val.list (List.map natList accL ++ [natList Cl])).wt + accV.wt := by
    split <;> omega
  clear ha2
  omega

end GI.Impl
