module

public import Workspace.Impl.AggItemC1Dat

@[expose] public section

/-!
# Case 1 as a program: the parity of a permutation

The Schreier generators and the aligning permutation depend on the parity of a permutation. A
permutation of `Fin q` is even exactly when its number of inversions is even
(`itp_sign_one_iff`). The program `itParF` counts, for each point `a`, the points `b < a` with
`σ a < σ b` (a `filter` with the test `itInvT`), and adds the counts modulo `2` (a `foldl`).
`it_par_spec`: on `encPerm σ` it returns `itpNInv σ % 2`. No primitive is called.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm)

variable {q : ℕ}

/-- On `[[S, a], b]` (a permutation and two points): `1` if `b < a` and `σ a < σ b`. -/
def itInvT : Expr :=
  let S := Expr.get (arg 0) (.nat 0)
  let A := Expr.get (arg 0) (.nat 1)
  .arith .mul (.arith .lt (arg 1) A) (.arith .lt (.get S A) (.get S (arg 1)))

/-- The inversion test as a test on point values. -/
def itInvQ (σ : Perm (Fin q)) (a : Fin q) : Val → Bool
  | .nat b => if h : b < q then decide ((⟨b, h⟩ : Fin q) < a ∧ σ a < σ ⟨b, h⟩) else false
  | _ => false

set_option maxHeartbeats 1000000 in
theorem it_invT_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some itInvT) (σ : Perm (Fin q))
    (a b : Fin q) :
    FunDet P f (.list [.list [encPerm σ, .nat a], .nat b]) (boolVal (itInvQ σ a (.nat b)))
      (10 ^ 4 * (q + 1) ^ 2) := by
  have hq1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqa : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  set W := 60 * (q + 1) ^ 2
  have hS := wt_encPerm_le σ
  have ha := wt_nat_le (a : ℕ)
  have hb := wt_nat_le (b : ℕ)
  have haq := a.isLt
  have hbq := b.isLt
  have hc := wt_list2_le (encPerm σ) (.nat a)
  have hin := wt_list2_le (.list [encPerm σ, .nat a]) (.nat b)
  set vs : List Val := [.list [encPerm σ, .nat a], .nat b]
  have g0 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 0) rfl (W := W) (by omega) (by omega)
    (by omega)
  have gB := StDC.arg (P := P) (rest := []) (vs := vs) (j := 1) rfl (W := W) (by omega) (by omega)
    (by omega)
  have gS := StDC.get g0 (StDC.nat 0 (by omega)) (v := encPerm σ) rfl (by omega)
  have gA := StDC.get g0 (StDC.nat 1 (by omega)) (v := .nat a) rfl (by omega)
  have sA := StDC.get (vs := (List.finRange q).map fun i => Val.nat (σ i : ℕ)) gS gA
    (encFun_getElem? (fun i => (σ i : ℕ)) a) (by have := wt_nat_le (σ a : ℕ); have := (σ a).isLt; omega)
  have sB := StDC.get (vs := (List.finRange q).map fun i => Val.nat (σ i : ℕ)) gS gB
    (encFun_getElem? (fun i => (σ i : ℕ)) b) (by have := wt_nat_le (σ b : ℕ); have := (σ b).isLt; omega)
  have a1 := StDC.arith' (op := .lt) gB gA rfl
    (by simp only [GI.Machine.BinOp.eval]; split_ifs <;> omega)
  have a2 := StDC.arith' (op := .lt) sA sB rfl
    (by simp only [GI.Machine.BinOp.eval]; split_ifs <;> omega)
  have a3 := StDC.arith' (op := .mul) a1 a2 rfl
    (by simp only [GI.Machine.BinOp.eval]; split_ifs <;> omega)
  have e : itInvQ σ a (.nat b) = decide (b < a ∧ σ a < σ b) := by simp [itInvQ, b.isLt]
  have e2 : (decide (b < a ∧ σ a < σ b)).toNat =
      GI.Machine.BinOp.eval .mul (GI.Machine.BinOp.eval .lt b a)
        (GI.Machine.BinOp.eval .lt (σ a) (σ b)) := by
    simp only [GI.Machine.BinOp.eval, Fin.lt_def]
    by_cases h1 : (b : ℕ) < a <;> by_cases h2 : (σ a : ℕ) < σ b <;> simp [h1, h2]
  rw [e, boolVal, e2]
  refine StDC.funDet hf a3 ?_
  omega

/-- The number of inversions at `a`. -/
def itInvAt (σ : Perm (Fin q)) (a : Fin q) : ℕ :=
  (Finset.univ.filter fun b => b < a ∧ σ a < σ b).card

theorem itInvAt_le (σ : Perm (Fin q)) (a : Fin q) : itInvAt σ a ≤ q := by
  have := Finset.card_le_univ (Finset.univ.filter fun b => b < a ∧ σ a < σ b)
  simpa [itInvAt] using this

theorem it_filter_inv (σ : Perm (Fin q)) (a : Fin q) :
    (((List.range q).map Val.nat).filter (itInvQ σ a)).length = itInvAt σ a := by
  classical
  have e1 : (List.range q).map Val.nat = (List.finRange q).map fun i : Fin q => Val.nat i.val := by
    have := it_range_eq (q := q); rw [natList] at this; exact Val.list.inj this
  rw [e1, List.filter_map, List.length_map, itInvAt, ac_card_filter]
  congr 1
  refine List.filter_congr fun i _ => ?_
  simp [itInvQ, i.isLt]

/-- On `[[S, R], a]`: the number of inversions at `a`. -/
def itInvB (flt : ℕ) : Expr :=
  .length (.call flt (mk2 (mk2 (.get (arg 0) (.nat 0)) (arg 1)) (.get (arg 0) (.nat 1))))

set_option maxHeartbeats 1000000 in
theorem it_invB_spec {P : Program} {f flt it : ℕ} (hf : P.funs[f]? = some (itInvB flt))
    (hflt : P.HasAt flt (filterFuns flt it)) (hit : P.funs[it]? = some itInvT)
    (σ : Perm (Fin q)) (a : Fin q) :
    FunDet P f (.list [.list [encPerm σ, natList (List.range q)], .nat a])
      (.nat (itInvAt σ a)) (10 ^ 6 * (q + 1) ^ 3) := by
  have hq1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqa : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hq3 : (q + 1) ^ 2 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  set W := 100 * (q + 1) ^ 2
  have hS := wt_encPerm_le σ
  have hR := it_range_wt (q := q)
  have ha := wt_nat_le (a : ℕ)
  have haq := a.isLt
  have hc := wt_list2_le (encPerm σ) (natList (List.range q))
  have hin := wt_list2_le (.list [encPerm σ, natList (List.range q)]) (.nat a)
  have hc2 := wt_list2_le (encPerm σ) (.nat a)
  have hfi := wt_list2_le (.list [encPerm σ, .nat a]) (natList (List.range q))
  set vs : List Val := [.list [encPerm σ, natList (List.range q)], .nat a]
  have g0 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 0) rfl (W := W) (by omega) (by omega)
    (by omega)
  have gA := StDC.arg (P := P) (rest := []) (vs := vs) (j := 1) rfl (W := W) (by omega) (by omega)
    (by omega)
  have gS := StDC.get g0 (StDC.nat 0 (by omega)) (v := encPerm σ) rfl (by omega)
  have gR := StDC.get g0 (StDC.nat 1 (by omega)) (v := natList (List.range q)) rfl (by omega)
  have m2 := StDC.mk2 (StDC.mk2 gS gA (by omega) (by omega)) gR (by omega) (by omega)
  have hF := filter_spec hflt (c := .list [encPerm σ, .nat a])
    (xs := (List.range q).map Val.nat) (q := itInvQ σ a) (B := fun _ => 10 ^ 4 * (q + 1) ^ 2)
    (fun v hv => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hv
      exact it_invT_spec hit σ a ⟨b, List.mem_range.1 hb⟩)
  set out := ((List.range q).map Val.nat).filter (itInvQ σ a)
  have hlen : ((List.range q).map Val.nat).length = q := by simp
  have hol : out.length ≤ q := (List.length_filter_le _ _).trans hlen.le
  have howt : (Val.list out).wt ≤ 5 * (q + 1) ^ 2 := by
    have h1 := wt_list_le_of out (c := q + 2) (fun v hv => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (List.mem_of_mem_filter hv)
      have := wt_nat_le y; have := List.mem_range.1 hy; omega)
    have h2 : out.length * (2 * (q + 2) + 1) ≤ q * (2 * (q + 2) + 1) := Nat.mul_le_mul_right _ hol
    nlinarith
  have hFd : FunDet P flt (.list [.list [encPerm σ, .nat a], natList (List.range q)])
      (.list out) (q * (10 ^ 4 * (q + 1) ^ 2) +
        loopModK * (q + 1) * (W + q + 5 * (q + 1) ^ 2 + 1)) := by
    refine hF.mono fun w c ⟨h1, h2⟩ => ⟨h1, ?_⟩
    subst h1
    have hsum : (((List.range q).map Val.nat).map fun _ => 10 ^ 4 * (q + 1) ^ 2).sum =
        q * (10 ^ 4 * (q + 1) ^ 2) := by
      simp [Function.comp_def, List.map_const', List.sum_replicate]
    rw [hsum, hlen] at h2
    refine h2.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _)
    have : (Val.list [.list [encPerm σ, .nat a], .list ((List.range q).map Val.nat)]).wt ≤ W := by
      show (Val.list [.list [encPerm σ, .nat a], natList (List.range q)]).wt ≤ W
      omega
    omega
  have c1 := StDC.call m2 hFd (by omega)
  have c2 := StDC.length c1 (by omega)
  rw [← it_filter_inv σ a]
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

/-! ### The sum modulo two -/

/-- On `[c, acc, v]`: `(acc + v) % 2`. -/
def itParS : Expr := .arith .mod (.arith .add (arg 1) (arg 2)) (.nat 2)

/-- The step of the sum modulo two on values. -/
def itParG : Val → Val → Val
  | .nat a, .nat b => .nat ((a + b) % 2)
  | _, _ => .nat 0

theorem it_parS_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some itParS) (c : Val) (a b : ℕ)
    {W : ℕ} (hW : (Val.list [c, .nat a, .nat b]).wt + 4 ≤ W) (ha : a < 2) (hb : b + 4 ≤ W) :
    FunDet P f (.list [c, .nat a, .nat b]) (.nat ((a + b) % 2)) (20 * (W + 1)) := by
  have h1 := wt_le_wt_list (vs := [c, .nat a, .nat b]) (v := .nat a) (by simp)
  have h2 := wt_le_wt_list (vs := [c, .nat a, .nat b]) (v := .nat b) (by simp)
  have g1 := StDC.arg (P := P) (rest := []) (vs := [c, .nat a, .nat b]) (j := 1) rfl (W := W)
    (by omega) (by omega) (by omega)
  have g2 := StDC.arg (P := P) (rest := []) (vs := [c, .nat a, .nat b]) (j := 2) rfl (W := W)
    (by omega) (by omega) (by omega)
  have hab : (Val.nat (a + b)).wt ≤ W := by
    have := wt_nat_le (a + b); omega
  have a1 := StDC.arith (op := .add) g1 g2 rfl hab
  have a2 := StDC.arith (op := .mod) a1 (StDC.nat 2 (by omega)) rfl
    (by simp only [GI.Machine.BinOp.eval]; have := wt_nat_le ((a + b) % 2)
        have := Nat.mod_lt (a + b) (show 2 > 0 by omega); omega)
  exact StDC.funDet hf a2 (by omega)

theorem it_parG_foldl (l : List ℕ) {acc : ℕ} (hacc : acc < 2) :
    (l.map Val.nat).foldl itParG (.nat acc) = .nat ((acc + l.sum) % 2) := by
  induction l generalizing acc with
  | nil => simp [Nat.mod_eq_of_lt hacc]
  | cons x l ih =>
    simp only [List.map_cons, List.foldl_cons, itParG, List.sum_cons]
    rw [ih (Nat.mod_lt _ (by omega))]
    congr 1
    omega

theorem it_parG_foldl0 (l : List ℕ) :
    (l.map Val.nat).foldl itParG (.nat 0) = .nat (l.sum % 2) := by
  rw [it_parG_foldl l (by omega), zero_add]

/-- On `encPerm σ`: the number of inversions modulo `2`. -/
def itParF (rng mp fld : ℕ) : Expr :=
  .letE (.call rng (.length (.var 0)))
    (.letE (.call mp (mk2 (mk2 (.var 0) (.var 1)) (.var 1)))
      (.call fld (mk3 (.nat 0) (.var 2) (.nat 0))))

/-- The cost bound of `itParF`. -/
def itParC (q : ℕ) : ℕ := 10 ^ 7 * (q + 1) ^ 4

theorem itpNInv_eq_sum (σ : Perm (Fin q)) :
    itpNInv σ = ((List.finRange q).map (itInvAt σ)).sum := by
  rw [itpNInv, ← Fin.sum_univ_def]; rfl

set_option maxHeartbeats 2000000 in
/-- **The parity as a program.** -/
theorem it_par_spec {P : Program} {f rng mp ib flt it fld st : ℕ}
    (hf : P.funs[f]? = some (itParF rng mp fld)) (hrng : P.HasAt rng (rangeFuns rng))
    (hmp : P.HasAt mp (mapFuns mp ib)) (hib : P.funs[ib]? = some (itInvB flt))
    (hflt : P.HasAt flt (filterFuns flt it)) (hit : P.funs[it]? = some itInvT)
    (hfld : P.HasAt fld (foldlFuns fld st)) (hst : P.funs[st]? = some itParS)
    (σ : Perm (Fin q)) :
    FunDet P f (encPerm σ) (.nat (itpNInv σ % 2)) (itParC q) := by
  have hq1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqa : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hq3 : (q + 1) ^ 2 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hq4 : (q + 1) ^ 3 ≤ (q + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  set W := 100 * (q + 1) ^ 2
  have hS := wt_encPerm_le σ
  have hR := it_range_wt (q := q)
  have hC := it_encFun_wt (itInvAt σ) (itInvAt_le σ)
  have cR : FunDet P rng (.nat q) (natList (List.range q)) (10000 * (q + 1) ^ 3) :=
    st_range_det hrng q
  have cM := it_tab hmp (c := .list [encPerm σ, natList (List.range q)]) (itInvAt σ)
    (itInvAt_le σ) (fun a => it_invB_spec hib hflt hit σ a)
  -- the fold
  set xs : List Val := (List.finRange q).map fun a => Val.nat (itInvAt σ a)
  have hxs : xs = ((List.finRange q).map (itInvAt σ)).map Val.nat := by
    simp only [xs, List.map_map]; rfl
  have hT : ∀ i, (xs.take i).foldl itParG (.nat 0) =
      .nat ((List.take i (List.map (itInvAt σ) (List.finRange q))).sum % 2) := fun i => by
    rw [hxs, ← List.map_take, it_parG_foldl0]
  have hacc : ∀ i ≤ xs.length, ((xs.take i).foldl itParG (.nat 0)).wt ≤ 3 := by
    intro i _
    rw [hT]
    have := wt_nat_le ((List.take i (List.map (itInvAt σ) (List.finRange q))).sum % 2)
    have := Nat.mod_lt ((List.take i (List.map (itInvAt σ) (List.finRange q))).sum)
      (show 2 > 0 by omega)
    omega
  have hF := foldl_spec_fun hfld (c := .nat 0) (xs := xs) (acc0 := .nat 0) (G := itParG)
    (M := 3) (B := fun _ => 20 * (W + 1)) hacc (fun i hi => by
      have hi' : i < q := by simpa [xs] using hi
      have hx : xs[i] = .nat (itInvAt σ ((List.finRange q)[i]'(by simpa using hi'))) := by
        simp [xs]
      rw [hx, hT]
      set s0 := (List.take i (List.map (itInvAt σ) (List.finRange q))).sum % 2
      set v := itInvAt σ ((List.finRange q)[i]'(by simpa using hi'))
      have hs0 : s0 < 2 := Nat.mod_lt _ (by omega)
      have hv : v ≤ q := itInvAt_le σ _
      have := it_parS_spec hst (.nat 0) s0 v (W := W) (by
          have h1 := wt_list3_le (.nat 0) (.nat s0) (.nat v)
          have := wt_nat_le s0
          have := wt_nat_le v
          have : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
          omega) hs0 (by omega)
      simpa [itParG] using this)
  have hfold : xs.foldl itParG (.nat 0) = .nat (itpNInv σ % 2) := by
    rw [hxs, it_parG_foldl0, itpNInv_eq_sum]
  rw [hfold] at hF
  have hxl : xs.length = q := by simp [xs]
  rw [hxl] at hF
  -- the body
  have d0 : StDC P [encPerm σ] (.var 0) (encPerm σ) 1 0 W := StDC.var' rfl (by omega)
  have dl := StDC.length (vs := (List.finRange q).map fun i => Val.nat (σ i : ℕ)) d0
    (by simp; omega)
  simp only [List.length_map, List.length_finRange] at dl
  have d1 := StDC.call dl cR (by omega)
  have v0 : StDC P [encPerm σ, natList (List.range q)] (.var 0) (encPerm σ) 1 0 W := StDC.var' rfl (by omega)
  have v1 : StDC P [encPerm σ, natList (List.range q)] (.var 1) (natList (List.range q)) 1 0 W := StDC.var' rfl (by omega)
  have hw1 := wt_list2_le (encPerm σ) (natList (List.range q))
  have hw2 := wt_list2_le (.list [encPerm σ, natList (List.range q)]) (natList (List.range q))
  have d2 := StDC.call (StDC.mk2 (StDC.mk2 v0 v1 (by omega) (by omega)) v1 (by omega)
    (by omega)) cM (by omega)
  have u2 : StDC P [encPerm σ, natList (List.range q), encFun (itInvAt σ)] (.var 2) (encFun (itInvAt σ)) 1 0 W := StDC.var' rfl (by omega)
  have hw3 := wt_list3_le (.nat 0) (encFun (itInvAt σ)) (.nat 0)
  have h0 : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
  have hF' : FunDet P fld (.list [.nat 0, encFun (itInvAt σ), .nat 0]) (.nat (itpNInv σ % 2))
      (q * (20 * (W + 1)) + loopModK * (q + 1) * (100 * (q + 1) ^ 2)) := by
    refine hF.mono ?_
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    refine Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _
    show (Val.list [.nat 0, encFun (itInvAt σ), .nat 0]).wt + q + 3 + 1 ≤ _
    omega
  have hpw : (Val.nat (itpNInv σ % 2)).wt ≤ W := by
    have := wt_nat_le (itpNInv σ % 2); have := Nat.mod_lt (itpNInv σ) (show 2 > 0 by omega)
    omega
  have d3 := StDC.call (StDC.mk3 (StDC.nat 0 (by omega)) u2 (StDC.nat 0 (by omega)) (by omega)
    (by omega)) hF' hpw
  have dall := StDC.letE d1 (StDC.letE d2 d3 hpw) hpw
  refine StDC.funDet hf dall ?_
  have hc1 : q * (10 ^ 6 * (q + 1) ^ 3) ≤ 10 ^ 6 * (q + 1) ^ 4 := by
    calc q * (10 ^ 6 * (q + 1) ^ 3) ≤ (q + 1) * (10 ^ 6 * (q + 1) ^ 3) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 10 ^ 6 * (q + 1) ^ 4 := by ring
  have hm : mapK * (q + 1) * (2 * (Val.list [encPerm σ, natList (List.range q)]).wt +
      22 * (q + 1) ^ 2) ≤ 10 ^ 5 * (q + 1) ^ 3 := by
    calc mapK * (q + 1) * (2 * (Val.list [encPerm σ, natList (List.range q)]).wt +
          22 * (q + 1) ^ 2)
        ≤ 1000 * (q + 1) * (100 * (q + 1) ^ 2) := Nat.mul_le_mul_left _ (by omega)
      _ = 10 ^ 5 * (q + 1) ^ 3 := by ring
  have hf1 : q * (20 * (W + 1)) ≤ 3000 * (q + 1) ^ 3 := by
    calc q * (20 * (W + 1)) ≤ (q + 1) * (3000 * (q + 1) ^ 2) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ = 3000 * (q + 1) ^ 3 := by ring
  have hf2 : loopModK * (q + 1) * (100 * (q + 1) ^ 2) = 10 ^ 5 * (q + 1) ^ 3 := by
    simp only [loopModK]; ring
  unfold itParC
  omega

end GI.Impl
