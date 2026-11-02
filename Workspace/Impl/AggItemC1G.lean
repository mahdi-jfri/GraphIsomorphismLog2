import Workspace.Impl.AggItemC1Sw

/-!
# Case 1 as a program: the generators of the stabilizer

On the data `itDatV lab` of orbit labels, `itGensF` returns the list `itcGp lab` of
generators of the stabilizer of the partition (`it_gens_spec`):

* the transpositions `(lab x, x)` for the points `x` (`itTrB`, a map over `[0, …, q-1]`);
* for every index `j < q²`, with `x = j / q` and `y = j % q`, the block swap of the blocks of `x`
  and `y` if they have the same size, else the identity (`itGenB`, a map over `[0, …, q²-1]`).

The list has the same members as `itcGens lab` (`itcGp_mem`), so it generates the stabilizer
(`itcGp_gens`). No primitive is called.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens)

variable {q : ℕ}

/-! ### The list and its members -/

/-- The transposition of a point with its center, for `x < q`. -/
def itcTrN (lab : Fin q → ℕ) (x : ℕ) : Perm (Fin q) :=
  if h : x < q then Equiv.swap (itcC lab ⟨x, h⟩) ⟨x, h⟩ else 1

/-- The block swap of the index `j = x q + y`. -/
noncomputable def itcGenN (lab : Fin q → ℕ) (j : ℕ) : Perm (Fin q) :=
  if h : j / q < q ∧ j % q < q then itcGen lab ⟨j / q, h.1⟩ ⟨j % q, h.2⟩ else 1

/-- **The program's generators of the stabilizer.** -/
noncomputable def itcGp (lab : Fin q → ℕ) : List (Perm (Fin q)) :=
  (List.range q).map (itcTrN lab) ++ (List.range (q * q)).map (itcGenN lab)

theorem itcGp_mem (lab : Fin q → ℕ) (g : Perm (Fin q)) : g ∈ itcGp lab ↔ g ∈ itcGens lab := by
  simp only [itcGp, itcGens, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap,
    List.mem_finRange, true_and]
  refine or_congr ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, by simp [itcTrN, hx]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.isLt, by simp [itcTrN, x.isLt]⟩
  · rintro ⟨j, hj, rfl⟩
    have hq : 0 < q := by
      rcases Nat.eq_zero_or_pos q with h | h
      · subst h; simp at hj
      · exact h
    have h1 : j / q < q := (Nat.div_lt_iff_lt_mul hq).2 hj
    have h2 : j % q < q := Nat.mod_lt _ hq
    exact ⟨⟨j / q, h1⟩, ⟨j % q, h2⟩, by simp [itcGenN, h1, h2]⟩
  · rintro ⟨x, y, rfl⟩
    have hq : 0 < q := x.pos
    have hj : (x : ℕ) * q + y < q * q := by
      have := y.isLt; have := x.isLt; nlinarith
    have h1 : ((x : ℕ) * q + y) / q = x := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt y.isLt, zero_add]
    have h2 : ((x : ℕ) * q + y) % q = y := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt y.isLt]
    refine ⟨x * q + y, hj, ?_⟩
    have hc : ((x : ℕ) * q + y) / q < q ∧ ((x : ℕ) * q + y) % q < q := by rw [h1, h2]; exact ⟨x.isLt, y.isLt⟩
    rw [itcGenN, dif_pos hc]
    congr 1 <;> exact Fin.ext (by simp [h1, h2])

/-- **The program's list generates the stabilizer.** -/
theorem itcGp_gens {gs : List (Perm (Fin q))} {lab : Fin q → ℕ} (h : ItcLab gs lab) :
    gens (itcGp lab) = MulAction.stabilizer (Perm (Fin q)) (itpPart lab) := by
  rw [← itc_closure h]
  unfold gens
  congr 1
  ext g
  exact itcGp_mem lab g

/-! ### The transpositions -/

theorem itcC_val' {lab : Fin q → ℕ} (hlt : ∀ x, lab x < q) (x : Fin q) :
    (itcC lab x : ℕ) = lab x := by simp [itcC, hlt x]

/-- On `[[L, R], x]`: the transposition `(lab x, x)`. -/
def itTrB (sw : ℕ) : Expr :=
  .call sw (mk2 (mk2 (.get (.get (arg 0) (.nat 0)) (arg 1)) (arg 1)) (.get (arg 0) (.nat 1)))

set_option maxHeartbeats 1000000 in
theorem it_trB_spec {P : Program} {f sw sb : ℕ} (hf : P.funs[f]? = some (itTrB sw))
    (hsw : P.HasAt sw (mapFuns sw sb)) (hsb : P.funs[sb]? = some itSwB) {lab : Fin q → ℕ}
    (hlt : ∀ x, lab x < q) (x : Fin q) :
    FunDet P f (.list [.list [encFun lab, natList (List.range q)], .nat x])
      (encPerm (itcTrN lab x)) (2 * 10 ^ 5 * (q + 1) ^ 3) := by
  have hq1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqa : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hq3 : (q + 1) ^ 2 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  set W := 100 * (q + 1) ^ 2
  have hL := it_encFun_wt lab fun x => (hlt x).le
  have hR := it_range_wt (q := q)
  have hx := wt_nat_le (x : ℕ)
  have hxq := x.isLt
  have hlx := wt_nat_le (lab x)
  have hlxq := hlt x
  have hc := wt_list2_le (encFun lab) (natList (List.range q))
  have hin := wt_list2_le (.list [encFun lab, natList (List.range q)]) (.nat x)
  have h2 := wt_list2_le (.nat (lab x)) (.nat x)
  have h3 := wt_list2_le (.list [.nat (lab x), .nat x]) (natList (List.range q))
  have hT := wt_encPerm_le (itcTrN lab x)
  set vs : List Val := [.list [encFun lab, natList (List.range q)], .nat x]
  have g0 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 0) rfl (W := W) (by omega) (by omega)
    (by omega)
  have gX := StDC.arg (P := P) (rest := []) (vs := vs) (j := 1) rfl (W := W) (by omega) (by omega)
    (by omega)
  have gL := StDC.get g0 (StDC.nat 0 (by omega)) (v := encFun lab) rfl (by omega)
  have gR := StDC.get g0 (StDC.nat 1 (by omega)) (v := natList (List.range q)) rfl (by omega)
  have lX := StDC.get (vs := (List.finRange q).map fun i => Val.nat (lab i)) gL gX
    (encFun_getElem? lab x) (by omega)
  have m := StDC.mk2 (StDC.mk2 lX gX (by omega) (by omega)) gR (by omega) (by omega)
  have hsw' := it_swTab_spec hsw hsb (itcC lab x) x
  rw [itcC_val' hlt] at hsw'
  have hTr : itcTrN lab x = Equiv.swap (itcC lab x) x := by simp [itcTrN, x.isLt]
  rw [hTr] at hT ⊢
  have c1 := StDC.call m hsw' (by omega)
  refine StDC.funDet hf c1 ?_
  omega

/-! ### The block swaps of the pairs -/

/-- On `[D, j]` (the data of the labeling and an index `j < q²`): the block swap of the blocks
of `j / q` and `j % q` if they have the same size, else the identity. -/
def itGenB (bs : ℕ) : Expr :=
  let L := Expr.get (arg 0) (.nat 0)
  let Sz := Expr.get (arg 0) (.nat 1)
  let Ps := Expr.get (arg 0) (.nat 2)
  let Iv := Expr.get (arg 0) (.nat 3)
  let R := Expr.get (arg 0) (.nat 4)
  let X := Expr.arith .div (arg 1) (.length R)
  let Y := Expr.arith .mod (arg 1) (.length R)
  .ite (.arith .eq (.get Sz X) (.get Sz Y))
    (.call bs (mk2 (.snoc (mk4 L Ps Iv (.get L X)) (.get L Y)) R)) R

theorem it_range_one : natList (List.range q) = encPerm (1 : Perm (Fin q)) := it_range_eq

theorem itc_bsOK {gs : List (Perm (Fin q))} {lab : Fin q → ℕ} (h : ItcLab gs lab) {x y : Fin q}
    (hs : itpSz lab x = itpSz lab y) : ItpBsOK lab (itcC lab x) (itcC lab y) := by
  have hc1 := itcC_lab h
  have hc2 : ∀ x y, lab x = lab y → itcC lab x ≤ y := fun x y => itcC_le h
  exact ⟨itp_c_rk hc1 hc2 x, itp_c_rk hc1 hc2 y, by
    rw [itpSz_congr (hc1 x), itpSz_congr (hc1 y), hs]⟩

set_option maxHeartbeats 4000000 in
theorem it_genB_spec {P : Program} {f bs bb : ℕ} (hf : P.funs[f]? = some (itGenB bs))
    (hbs : P.HasAt bs (mapFuns bs bb)) (hbb : P.funs[bb]? = some itBsB)
    {gs : List (Perm (Fin q))} {lab : Fin q → ℕ} (hl : ItcLab gs lab) {j : ℕ} (hj : j < q * q) :
    FunDet P f (.list [itDatV lab, .nat j]) (encPerm (itcGenN lab j)) (2 * 10 ^ 6 * (q + 1) ^ 3) := by
  have hlt : ∀ x, lab x < q := fun x => (hl.min x).1
  have hq : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; simp at hj
    · exact h
  have hx : j / q < q := (Nat.div_lt_iff_lt_mul hq).2 hj
  have hy : j % q < q := Nat.mod_lt _ hq
  set x : Fin q := ⟨j / q, hx⟩
  set y : Fin q := ⟨j % q, hy⟩
  have hq1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqa : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hq3 : (q + 1) ^ 2 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hjq : j + 2 ≤ (q + 1) ^ 2 := by nlinarith
  set W := 300 * (q + 1) ^ 2
  have hD := it_datV_wt lab hlt
  have hj' := wt_nat_le j
  have hin := wt_list2_le (itDatV lab) (.nat j)
  have hpt : ∀ k : ℕ, k < q → (Val.nat k).wt ≤ W := fun k hk => by
    have := wt_nat_le k; omega
  have hL := it_encFun_wt lab fun x => (hlt x).le
  have hS := it_encFun_wt (itpSz lab) (itpSz_le lab)
  have hP := wt_encPerm_le (itpPosE lab)
  have hI := wt_encPerm_le (itpPosE lab)⁻¹
  have hR := it_range_wt (q := q)
  have hG := wt_encPerm_le (itcGenN lab j)
  set vs : List Val := [itDatV lab, .nat j]
  have g0 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 0) rfl (W := W) (by omega) (by omega)
    (by omega)
  have gJ := StDC.arg (P := P) (rest := []) (vs := vs) (j := 1) rfl (W := W) (by omega) (by omega)
    (by omega)
  have g0' : StDC P [Val.list vs] (arg 0) (.list [encFun lab, encFun (itpSz lab),
      encPerm (itpPosE lab), encPerm (itpPosE lab)⁻¹, natList (List.range q)]) 3 0 W := g0
  have gL := StDC.get g0' (StDC.nat 0 (by omega)) (v := encFun lab) rfl (by omega)
  have gS := StDC.get g0' (StDC.nat 1 (by omega)) (v := encFun (itpSz lab)) rfl (by omega)
  have gP := StDC.get g0' (StDC.nat 2 (by omega)) (v := encPerm (itpPosE lab)) rfl (by omega)
  have gI := StDC.get g0' (StDC.nat 3 (by omega)) (v := encPerm (itpPosE lab)⁻¹) rfl (by omega)
  have gR := StDC.get g0' (StDC.nat 4 (by omega)) (v := natList (List.range q)) rfl (by omega)
  have gQ := StDC.length (vs := (List.range q).map Val.nat) gR (by simp; omega)
  simp only [List.length_map, List.length_range] at gQ
  have gX := StDC.arith' (op := .div) gJ gQ rfl (by
    simp only [GI.Machine.BinOp.eval]; omega)
  have gY := StDC.arith' (op := .mod) gJ gQ rfl (by
    simp only [GI.Machine.BinOp.eval]; omega)
  have sX := StDC.get (vs := (List.finRange q).map fun i => Val.nat (itpSz lab i)) gS gX
    (encFun_getElem? (itpSz lab) x) (by have := itpSz_le lab x; have := wt_nat_le (itpSz lab x); omega)
  have sY := StDC.get (vs := (List.finRange q).map fun i => Val.nat (itpSz lab i)) gS gY
    (encFun_getElem? (itpSz lab) y) (by have := itpSz_le lab y; have := wt_nat_le (itpSz lab y); omega)
  have e1 := StDC.arith' (op := .eq) sX sY rfl
    (by simp only [GI.Machine.BinOp.eval]; split_ifs <;> omega)
  have outer := it_ite (p := itpSz lab x = itpSz lab y) (v := encPerm (itcGenN lab j)) e1
    (fun hs => by
      have hok := itc_bsOK hl hs
      have lX := StDC.get (vs := (List.finRange q).map fun i => Val.nat (lab i)) gL gX
        (encFun_getElem? lab x) (hpt _ (hlt x))
      have lY := StDC.get (vs := (List.finRange q).map fun i => Val.nat (lab i)) gL gY
        (encFun_getElem? lab y) (hpt _ (hlt y))
      have hctx : (Val.list ([encFun lab, encPerm (itpPosE lab), encPerm (itpPosE lab)⁻¹,
          .nat (lab x)] ++ [.nat (lab y)])) = itBsCtx lab (itcC lab x) (itcC lab y) := by
        rw [itBsCtx, itcC_val' hlt, itcC_val' hlt]; rfl
      have hcw := it_bsCtx_wt hlt (itcC lab x) (itcC lab y)
      have h4 := wt_list4_le (encFun lab) (encPerm (itpPosE lab)) (encPerm (itpPosE lab)⁻¹)
        (.nat (lab x))
      have hlxw := wt_nat_le (lab x)
      have hlxq := hlt x
      have hlyw := wt_nat_le (lab y)
      have hlyq := hlt y
      have m4 := StDC.mk4 gL gP gI lX (by omega) (by omega)
      have m5 := StDC.snoc m4 lY (by rw [hctx]; omega)
      rw [hctx] at m5
      have h2 := wt_list2_le (itBsCtx lab (itcC lab x) (itcC lab y)) (natList (List.range q))
      have m := StDC.mk2 m5 gR (by omega) (by omega)
      have hv : itcGenN lab j = itpBs lab (itcC lab x) (itcC lab y) := by
        rw [itcGenN, dif_pos ⟨hx, hy⟩, itcGen, if_pos hs]
      rw [hv]
      exact StDC.call m (it_bsTab_spec hbs hbb hlt hok) (by
        have := wt_encPerm_le (itpBs lab (itcC lab x) (itcC lab y)); omega))
    (fun hs => by
      have hv : itcGenN lab j = 1 := by
        rw [itcGenN, dif_pos ⟨hx, hy⟩, itcGen, if_neg hs]
      rw [hv, ← it_range_one]
      exact gR) (by omega)
  refine StDC.funDet hf outer ?_
  have : 200 * (W + 1) ≤ 10 ^ 5 * (q + 1) ^ 3 := by omega
  omega

/-! ### The whole list -/

/-- On the data `D` of a labeling: the list `itcGp lab`. -/
def itGensF (mpT rng mpG app : ℕ) : Expr :=
  let L := Expr.get (.var 0) (.nat 0)
  let R := Expr.get (.var 0) (.nat 4)
  .letE (.call mpT (mk2 (mk2 L R) R))
    (.letE (.call rng (.arith .mul (.length R) (.length R)))
      (.letE (.call mpG (mk2 (.var 0) (.var 2)))
        (.call app (mk2 (.var 1) (.var 3)))))

/-- The cost bound of `itGensF`. -/
def itGensC (q : ℕ) : ℕ := 10 ^ 9 * (q + 1) ^ 6

/-- The block swaps of the indices as values. -/
noncomputable def itGenV (lab : Fin q → ℕ) : Val → Val
  | .nat j => encPerm (itcGenN lab j)
  | _ => .nat 0

/-- The transpositions of the points as values. -/
def itTrV (lab : Fin q → ℕ) : Val → Val
  | .nat x => encPerm (itcTrN lab x)
  | _ => .nat 0

theorem it_perms_wt {l : List (Perm (Fin q))} {m : ℕ} (hl : l.length ≤ m) :
    (Val.list (l.map encPerm)).wt ≤ m * (9 * (q + 1) ^ 2) + 4 := by
  have h := wt_list_le_of (l.map encPerm) (c := 4 * (q + 1) ^ 2) (fun v hv => by
    obtain ⟨σ, -, rfl⟩ := List.mem_map.1 hv; exact wt_encPerm_le σ)
  rw [List.length_map] at h
  have : l.length * (2 * (4 * (q + 1) ^ 2) + 1) ≤ m * (9 * (q + 1) ^ 2) := by
    have : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    exact Nat.mul_le_mul hl (by omega)
  omega

set_option maxHeartbeats 4000000 in
/-- **The generators of the stabilizer as a program.** -/
theorem it_gens_spec {P : Program} {f mpT trB sw sb rng mpG gb bs bb app : ℕ}
    (hf : P.funs[f]? = some (itGensF mpT rng mpG app))
    (hmpT : P.HasAt mpT (mapFuns mpT trB)) (htrB : P.funs[trB]? = some (itTrB sw))
    (hsw : P.HasAt sw (mapFuns sw sb)) (hsb : P.funs[sb]? = some itSwB)
    (hrng : P.HasAt rng (rangeFuns rng))
    (hmpG : P.HasAt mpG (mapFuns mpG gb)) (hgb : P.funs[gb]? = some (itGenB bs))
    (hbs : P.HasAt bs (mapFuns bs bb)) (hbb : P.funs[bb]? = some itBsB)
    (happ : P.HasAt app (appendFuns app))
    {gs : List (Perm (Fin q))} {lab : Fin q → ℕ} (hl : ItcLab gs lab) :
    FunDet P f (itDatV lab) (.list ((itcGp lab).map encPerm)) (itGensC q) := by
  have hlt : ∀ x, lab x < q := fun x => (hl.min x).1
  have hq1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqa : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hq3 : (q + 1) ^ 2 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hq4 : (q + 1) ^ 3 ≤ (q + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hq5 : (q + 1) ^ 4 ≤ (q + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have hq6 : (q + 1) ^ 5 ≤ (q + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hqq : q * q + 1 ≤ (q + 1) ^ 2 := by nlinarith
  have hqq2 : (q * q + 1) ^ 2 ≤ (q + 1) ^ 4 :=
    calc (q * q + 1) ^ 2 ≤ ((q + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left hqq 2
      _ = (q + 1) ^ 4 := by ring
  have hqq3 : (q * q + 1) ^ 3 ≤ (q + 1) ^ 6 :=
    calc (q * q + 1) ^ 3 ≤ ((q + 1) ^ 2) ^ 3 := Nat.pow_le_pow_left hqq 3
      _ = (q + 1) ^ 6 := by ring
  set W := 300 * (q + 1) ^ 4
  have hD := it_datV_wt lab hlt
  have hL := it_encFun_wt lab fun x => (hlt x).le
  have hR := it_range_wt (q := q)
  have hRR := it_range_wt (q := q * q)
  have hRRw : (natList (List.range (q * q))).wt ≤ 5 * (q + 1) ^ 4 := by
    omega
  -- the transpositions
  set T := ((List.range q).map (itcTrN lab)).map encPerm
  have hTm : FunDet P mpT (.list [.list [encFun lab, natList (List.range q)], natList (List.range q)])
      (.list T) (q * (2 * 10 ^ 5 * (q + 1) ^ 3) + mapK * (q + 1) * (100 * (q + 1) ^ 3)) := by
    have h := map_det hmpT (c := .list [encFun lab, natList (List.range q)])
      (xs := (List.range q).map Val.nat) (F := itTrV lab) (B := 2 * 10 ^ 5 * (q + 1) ^ 3)
      (fun v hv => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
        exact it_trB_spec htrB hsw hsb hlt ⟨x, List.mem_range.1 hx⟩)
    have e : ((List.range q).map Val.nat).map (itTrV lab) = T := by
      simp only [T, List.map_map]; rfl
    rw [e] at h
    refine h.mono ?_
    have hT : (Val.list T).wt ≤ q * (9 * (q + 1) ^ 2) + 4 :=
      it_perms_wt (l := (List.range q).map (itcTrN lab)) (m := q) (by simp)
    have h2 := wt_list2_le (encFun lab) (natList (List.range q))
    have h3 := wt_list2_le (.list [encFun lab, natList (List.range q)]) (natList (List.range q))
    simp only [List.length_map, List.length_range]
    have : q * (9 * (q + 1) ^ 2) ≤ 9 * (q + 1) ^ 3 := by
      calc q * (9 * (q + 1) ^ 2) ≤ (q + 1) * (9 * (q + 1) ^ 2) := Nat.mul_le_mul_right _ (by omega)
        _ = 9 * (q + 1) ^ 3 := by ring
    refine Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _
    show (Val.list [.list [encFun lab, natList (List.range q)], natList (List.range q)]).wt +
      (Val.list T).wt + 1 ≤ _
    omega
  -- the block swaps
  set G := ((List.range (q * q)).map (itcGenN lab)).map encPerm
  have hGm : FunDet P mpG (.list [itDatV lab, natList (List.range (q * q))]) (.list G)
      (q * q * (2 * 10 ^ 6 * (q + 1) ^ 3) + mapK * (q * q + 1) * (300 * (q + 1) ^ 4)) := by
    have h := map_det hmpG (c := itDatV lab)
      (xs := (List.range (q * q)).map Val.nat) (F := itGenV lab) (B := 2 * 10 ^ 6 * (q + 1) ^ 3)
      (fun v hv => by
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hv
        exact it_genB_spec hgb hbs hbb hl (List.mem_range.1 hj))
    have e : ((List.range (q * q)).map Val.nat).map (itGenV lab) = G := by
      simp only [G, List.map_map]; rfl
    rw [e] at h
    refine h.mono ?_
    have hG : (Val.list G).wt ≤ (q + 1) ^ 2 * (9 * (q + 1) ^ 2) + 4 :=
      it_perms_wt (l := (List.range (q * q)).map (itcGenN lab)) (m := (q + 1) ^ 2) (by
        simp only [List.length_map, List.length_range]; omega)
    have : (q + 1) ^ 2 * (9 * (q + 1) ^ 2) = 9 * (q + 1) ^ 4 := by ring
    have h2 := wt_list2_le (itDatV lab) (natList (List.range (q * q)))
    simp only [List.length_map, List.length_range]
    refine Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _
    show (Val.list [itDatV lab, natList (List.range (q * q))]).wt + (Val.list G).wt + 1 ≤ _
    omega
  -- the append
  have hTw : (Val.list T).wt ≤ q * (9 * (q + 1) ^ 2) + 4 :=
    it_perms_wt (l := (List.range q).map (itcTrN lab)) (m := q) (by simp)
  have hGw : (Val.list G).wt ≤ (q + 1) ^ 2 * (9 * (q + 1) ^ 2) + 4 :=
    it_perms_wt (l := (List.range (q * q)).map (itcGenN lab)) (m := (q + 1) ^ 2) (by
      simp only [List.length_map, List.length_range]; omega)
  have hTw' : (Val.list T).wt ≤ 13 * (q + 1) ^ 3 := by
    have : q * (9 * (q + 1) ^ 2) ≤ 9 * (q + 1) ^ 3 := by
      calc q * (9 * (q + 1) ^ 2) ≤ (q + 1) * (9 * (q + 1) ^ 2) := Nat.mul_le_mul_right _ (by omega)
        _ = 9 * (q + 1) ^ 3 := by ring
    omega
  have hGw' : (Val.list G).wt ≤ 13 * (q + 1) ^ 4 := by
    have : (q + 1) ^ 2 * (9 * (q + 1) ^ 2) = 9 * (q + 1) ^ 4 := by ring
    omega
  have hout : (itcGp lab).map encPerm = T ++ G := by simp [itcGp, T, G]
  have hOw : (Val.list (T ++ G)).wt ≤ 13 * (q + 1) ^ 4 := by
    rw [← hout]
    have := it_perms_wt (l := itcGp lab) (m := (q + 1) ^ 2) (by
      simp only [itcGp, List.length_append, List.length_map, List.length_range]; nlinarith)
    have : (q + 1) ^ 2 * (9 * (q + 1) ^ 2) = 9 * (q + 1) ^ 4 := by ring
    omega
  have hTG := wt_list2_le (.list T) (.list G)
  have hAp : FunDet P app (.list [.list T, .list G]) (.list (T ++ G))
      (loopModK * (q * q + 1) * (300 * (q + 1) ^ 4)) := by
    refine (append_spec happ T G).mono fun w c ⟨h1, h2⟩ => ⟨h1, ?_⟩
    subst h1
    have hGl : G.length = q * q := by simp [G]
    rw [hGl] at h2
    refine h2.trans (Nat.mul_le_mul_left _ ?_)
    omega
  -- the body
  have hRw : (natList (List.range q)).wt ≤ 5 * (q + 1) ^ 2 := hR
  have v0 : StDC P [itDatV lab] (.var 0) (itDatV lab) 1 0 W := StDC.var' rfl (by omega)
  have v0' : StDC P [itDatV lab] (.var 0) (.list [encFun lab, encFun (itpSz lab),
      encPerm (itpPosE lab), encPerm (itpPosE lab)⁻¹, natList (List.range q)]) 1 0 W := v0
  have gL := StDC.get v0' (StDC.nat 0 (by omega)) (v := encFun lab) rfl (by omega)
  have gR := StDC.get v0' (StDC.nat 4 (by omega)) (v := natList (List.range q)) rfl (by omega)
  have h2 := wt_list2_le (encFun lab) (natList (List.range q))
  have h3 := wt_list2_le (.list [encFun lab, natList (List.range q)]) (natList (List.range q))
  have m1 := StDC.mk2 (StDC.mk2 gL gR (by omega) (by omega)) gR (by omega) (by omega)
  have d1 := StDC.call m1 hTm (by omega)
  -- second step
  set E1 : List Val := [itDatV lab, .list T]
  have v0b : StDC P E1 (.var 0) (.list [encFun lab, encFun (itpSz lab),
      encPerm (itpPosE lab), encPerm (itpPosE lab)⁻¹, natList (List.range q)]) 1 0 W :=
    StDC.var' rfl (show (itDatV lab).wt ≤ W by omega)
  have gRb := StDC.get v0b (StDC.nat 4 (by omega)) (v := natList (List.range q)) rfl (by omega)
  have lR := StDC.length (vs := (List.range q).map Val.nat) gRb (by simp; omega)
  simp only [List.length_map, List.length_range] at lR
  have mq := StDC.arith (op := .mul) lR lR rfl (by
    simp only [GI.Machine.BinOp.eval]; have := wt_nat_le (q * q); omega)
  have hRng : FunDet P rng (.nat (q * q)) (natList (List.range (q * q)))
      (10000 * (q * q + 1) ^ 3) := st_range_det hrng (q * q)
  have d2 := StDC.call mq hRng (by omega)
  -- third step
  set E2 : List Val := [itDatV lab, .list T, natList (List.range (q * q))]
  have u0 : StDC P E2 (.var 0) (itDatV lab) 1 0 W := StDC.var' rfl (by omega)
  have u2 : StDC P E2 (.var 2) (natList (List.range (q * q))) 1 0 W := StDC.var' rfl (by
    omega)
  have h4 := wt_list2_le (itDatV lab) (natList (List.range (q * q)))
  have d3 := StDC.call (StDC.mk2 u0 u2 (by omega) (by omega)) hGm (by omega)
  -- the last step
  set E3 : List Val := [itDatV lab, .list T, natList (List.range (q * q)), .list G]
  have w1 : StDC P E3 (.var 1) (.list T) 1 0 W := StDC.var' rfl (by omega)
  have w3 : StDC P E3 (.var 3) (.list G) 1 0 W := StDC.var' rfl (by omega)
  have d4 := StDC.call (StDC.mk2 w1 w3 (by omega) (by omega)) hAp (by omega)
  have dall := StDC.letE d1 (StDC.letE d2 (StDC.letE d3 d4 (by omega)) (by omega)) (by omega)
  rw [hout]
  refine StDC.funDet hf dall ?_
  -- the cost
  have c1 : q * (2 * 10 ^ 5 * (q + 1) ^ 3) ≤ 2 * 10 ^ 5 * (q + 1) ^ 6 := by
    calc q * (2 * 10 ^ 5 * (q + 1) ^ 3) ≤ (q + 1) * (2 * 10 ^ 5 * (q + 1) ^ 3) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 2 * 10 ^ 5 * (q + 1) ^ 4 := by ring
      _ ≤ 2 * 10 ^ 5 * (q + 1) ^ 6 := by omega
  have c2 : mapK * (q + 1) * (100 * (q + 1) ^ 3) ≤ 10 ^ 5 * (q + 1) ^ 6 := by
    calc mapK * (q + 1) * (100 * (q + 1) ^ 3) = 10 ^ 5 * (q + 1) ^ 4 := by simp only [mapK]; ring
      _ ≤ 10 ^ 5 * (q + 1) ^ 6 := by omega
  have c3 : q * q * (2 * 10 ^ 6 * (q + 1) ^ 3) ≤ 2 * 10 ^ 6 * (q + 1) ^ 6 := by
    calc q * q * (2 * 10 ^ 6 * (q + 1) ^ 3) ≤ (q + 1) ^ 2 * (2 * 10 ^ 6 * (q + 1) ^ 3) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 2 * 10 ^ 6 * (q + 1) ^ 5 := by ring
      _ ≤ 2 * 10 ^ 6 * (q + 1) ^ 6 := by omega
  have c4 : mapK * (q * q + 1) * (300 * (q + 1) ^ 4) ≤ 3 * 10 ^ 5 * (q + 1) ^ 6 := by
    calc mapK * (q * q + 1) * (300 * (q + 1) ^ 4) ≤ 1000 * (q + 1) ^ 2 * (300 * (q + 1) ^ 4) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hqq)
      _ = 3 * 10 ^ 5 * (q + 1) ^ 6 := by ring
  have c5 : loopModK * (q * q + 1) * (300 * (q + 1) ^ 4) ≤ 3 * 10 ^ 5 * (q + 1) ^ 6 := by
    calc loopModK * (q * q + 1) * (300 * (q + 1) ^ 4) ≤ 1000 * (q + 1) ^ 2 * (300 * (q + 1) ^ 4) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hqq)
      _ = 3 * 10 ^ 5 * (q + 1) ^ 6 := by ring
  have c6 : 10000 * (q * q + 1) ^ 3 ≤ 10000 * (q + 1) ^ 6 := by
    omega
  have c7 : 100 * (W + 1) ≤ 10 ^ 6 * (q + 1) ^ 6 := by omega
  unfold itGensC
  omega

end GI.Impl
