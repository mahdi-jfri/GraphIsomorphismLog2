module

public import Workspace.Impl.AggItemCiPartK

@[expose] public section

/-!
# The colored-partition item as a program: alignment and generators

* `itciAF`, `itci_al_spec`: on `[encFun fX, encFun fY]` the aligning permutation
  `encPerm (itciAl fX fY)` (two position tables, an inverse and a product).
* `itciGF`, `itci_g_spec`: on `[encFun f, R]` the centers, the first point that is not its center
  (`itciOt f`, by `find` with Case 1's `itFixT`), the transpositions `itciT f` (Case 1's
  `itTrB`), and, if there is such a point `a`, the odd transposition `itciTr f a` and the Schreier
  list `itciMs f (some a)` (Case 1's `itSchF`). The output is `itciGV f`.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens)

variable {q : ℕ}

/-! ### The alignment -/

/-- On `[FX, FY]`: the aligning permutation. -/
def itciAF (rng mpP inv cmp : ℕ) : Expr :=
  .letE (.call rng (.length (.get (.var 0) (.nat 0))))
  (.letE (.call mpP (mk2 (mk3 (.get (.var 0) (.nat 0)) (.get (.var 0) (.nat 0)) (.var 1)) (.var 1)))
  (.letE (.call mpP (mk2 (mk3 (.get (.var 0) (.nat 1)) (.get (.var 0) (.nat 1)) (.var 1)) (.var 1)))
  (.letE (.call inv (.var 3))
    (.call cmp (mk2 (.var 4) (.var 2))))))

/-- The cost bound of `itciAF`. -/
def itciAC (M : ℕ) : ℕ := 10 ^ 10 * (M + 2) ^ 4

set_option maxHeartbeats 4000000 in
/-- **The aligning permutation as a program.** -/
theorem itci_al_spec {P : Program} {fa rng mpP pb flt kb inv cmp : ℕ}
    (hfa : P.funs[fa]? = some (itciAF rng mpP inv cmp)) (hrng : P.HasAt rng (rangeFuns rng))
    (hmpP : P.HasAt mpP (mapFuns mpP pb)) (hpb : P.funs[pb]? = some (itPosB flt))
    (hflt : P.HasAt flt (filterFuns flt kb)) (hkb : P.funs[kb]? = some itKeyB)
    (hinv : P.HasAt inv (invFuns inv)) (hcmp : P.HasAt cmp (composeFuns cmp))
    (fX fY : Fin q → ℕ) {M : ℕ} (hMX : (encFun fX).wt ≤ M) (hMY : (encFun fY).wt ≤ M) :
    FunDet P fa (.list [encFun fX, encFun fY]) (encPerm (itciAl fX fY)) (itciAC M) := by
  have hqM := (itci_q_le_wt fX).trans hMX
  have hR := it_range_wt (q := q)
  have hq1 : (q + 1) ^ 2 ≤ (M + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hq3 : (q + 1) ^ 3 ≤ (M + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hq4 : (q + 1) ^ 4 ≤ (M + 2) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have hM2 : M + 2 ≤ (M + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hM23 : (M + 2) ^ 2 ≤ (M + 2) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hM34 : (M + 2) ^ 3 ≤ (M + 2) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  set W := 100 * (M + 2) ^ 2 with hW
  have hPX := wt_encPerm_le (itciPosE fX)
  have hPY := wt_encPerm_le (itciPosE fY)
  have hIY := wt_encPerm_le (itciPosE fY)⁻¹
  have hAl := wt_encPerm_le ((itciPosE fY)⁻¹ * itciPosE fX)
  have hin := wt_list2_le (encFun fX) (encFun fY)
  have hRl : (natList (List.range q)).wt + 0 = (natList (List.range q)).wt := rfl
  set v0 := Val.list [encFun fX, encFun fY]
  have w0 : StDC P [v0] (.var 0) v0 1 0 W := StDC.var' rfl (by omega)
  have gX0 := StDC.get w0 (StDC.nat 0 (by omega)) (v := encFun fX) rfl (by omega)
  have l1 := StDC.length (vs := (List.finRange q).map fun i => Val.nat (fX i)) gX0
    (by simp; omega)
  simp only [List.length_map, List.length_finRange] at l1
  have d1 := StDC.call l1 (st_range_det hrng q) (by omega)
  set E1 : List Val := [v0, natList (List.range q)]
  have x0 : StDC P E1 (.var 0) v0 1 0 W := StDC.var' rfl (by omega)
  have x1 : StDC P E1 (.var 1) (natList (List.range q)) 1 0 W := StDC.var' rfl (by omega)
  have gX := StDC.get x0 (StDC.nat 0 (by omega)) (v := encFun fX) rfl (by omega)
  have hc3 := wt_list3_le (encFun fX) (encFun fX) (natList (List.range q))
  have hc2 := wt_list2_le (.list [encFun fX, encFun fX, natList (List.range q)])
    (natList (List.range q))
  have d2 := StDC.call (StDC.mk2 (StDC.mk3 gX gX x1 (by omega) (by omega)) x1 (by omega)
    (by omega)) (itci_pos_tab hmpP hpb hflt hkb fX hMX) (by omega)
  set E2 : List Val := E1 ++ [encPerm (itciPosE fX)]
  have y0 : StDC P E2 (.var 0) v0 1 0 W := StDC.var' rfl (by omega)
  have y1 : StDC P E2 (.var 1) (natList (List.range q)) 1 0 W := StDC.var' rfl (by omega)
  have gY := StDC.get y0 (StDC.nat 1 (by omega)) (v := encFun fY) rfl (by omega)
  have hc3' := wt_list3_le (encFun fY) (encFun fY) (natList (List.range q))
  have hc2' := wt_list2_le (.list [encFun fY, encFun fY, natList (List.range q)])
    (natList (List.range q))
  have d3 := StDC.call (StDC.mk2 (StDC.mk3 gY gY y1 (by omega) (by omega)) y1 (by omega)
    (by omega)) (itci_pos_tab hmpP hpb hflt hkb fY hMY) (by omega)
  set E3 : List Val := E2 ++ [encPerm (itciPosE fY)]
  have d4 := StDC.call (StDC.var' (W := W) (env := E3) (i := 3) rfl (by omega))
    (inv_spec hinv (itciPosE fY)) (by omega)
  set E4 : List Val := E3 ++ [encPerm (itciPosE fY)⁻¹]
  have z4 : StDC P E4 (.var 4) (encPerm (itciPosE fY)⁻¹) 1 0 W := StDC.var' rfl (by omega)
  have z2 : StDC P E4 (.var 2) (encPerm (itciPosE fX)) 1 0 W := StDC.var' rfl (by omega)
  have hip := wt_list2_le (encPerm (itciPosE fY)⁻¹) (encPerm (itciPosE fX))
  have d5 := StDC.call (StDC.mk2 z4 z2 (by omega) (by omega))
    (compose_spec hcmp (itciPosE fY)⁻¹ (itciPosE fX)) (by omega)
  have dall := StDC.letE d1 (StDC.letE d2 (StDC.letE d3 (StDC.letE d4 d5 (by omega)) (by omega))
    (by omega)) (by omega)
  refine StDC.funDet hfa dall ?_
  unfold itciAC itciTC
  simp only [invK, permK]
  omega

/-! ### The found point -/

/-- The index of the first point that is not its center (`q` if there is none). -/
def itciIdx (f : Fin q → ℕ) : ℕ := ((List.range q).map Val.nat).findIdx (itFixQ (itciCN f))

/-- **The found point**: the first point that is not its center, if there is one. -/
def itciOt (f : Fin q → ℕ) : Option (Fin q) :=
  if h : itciIdx f < q then some ⟨itciIdx f, h⟩ else none

theorem itciIdx_le (f : Fin q → ℕ) : itciIdx f ≤ q := by
  have := List.findIdx_le_length (p := itFixQ (itciCN f)) (xs := (List.range q).map Val.nat)
  simpa [itciIdx] using this

/-- **The found point is not its center, and with none every point is its center.** -/
theorem itciOt_spec (f : Fin q → ℕ) :
    (itciOt f = none → ∀ a, itciC f a = a) ∧ ∀ a, itciOt f = some a → itciC f a ≠ a := by
  refine ⟨fun h a => ?_, fun a h => ?_⟩
  · unfold itciOt at h
    split_ifs at h with hlt
    have hq : itciIdx f = q := le_antisymm (itciIdx_le f) (not_lt.1 hlt)
    have hall := (List.findIdx_eq_length (p := itFixQ (itciCN f))
      (xs := (List.range q).map Val.nat)).1 (by simpa [itciIdx] using hq)
    have := hall (.nat a) (List.mem_map.2 ⟨a, List.mem_range.2 a.isLt, rfl⟩)
    simp only [itFixQ, a.isLt, dif_pos, decide_eq_false_iff_not, not_not] at this
    exact Fin.ext this
  · unfold itciOt at h
    split_ifs at h with hlt
    rw [Option.some.injEq] at h
    subst h
    have hl : ((List.range q).map Val.nat).findIdx (itFixQ (itciCN f)) <
        ((List.range q).map Val.nat).length := by
      rw [List.length_map, List.length_range]; exact hlt
    have hsat := List.findIdx_getElem (w := hl)
    simp only [List.getElem_map, List.getElem_range, itFixQ] at hsat
    have hlt2 : ((List.range q).map Val.nat).findIdx (itFixQ (itciCN f)) < q := hlt
    rw [dif_pos hlt2] at hsat
    have hsat' := of_decide_eq_true hsat
    intro he
    exact hsat' (congrArg Fin.val he)

/-! ### The generators -/

/-- On `[F, R]`: the centers, the found point, the transpositions, and if there is a found point
`a`, `[1, t, ms]` with `t = itciTr f a` and the Schreier list `ms`; else `[0]`. -/
def itciGF (mpC fd mpT swt sch : ℕ) : Expr :=
  let F := Expr.get (.var 0) (.nat 0)
  let R := Expr.get (.var 0) (.nat 1)
  .letE (.call mpC (mk2 (mk2 F R) R))
  (.letE (.call fd (mk2 (.var 1) R))
  (.letE (.call mpT (mk2 (mk2 (.var 1) R) R))
  (.ite (.arith .lt (.var 2) (.length R))
    (.letE (.call swt (mk2 (mk2 (.get (.var 1) (.var 2)) (.var 2)) R))
    (.letE (.call sch (mk2 (.var 4) (.var 3)))
      (mk3 (.nat 1) (.var 4) (.var 5))))
    (.snoc .nil (.nat 0)))))

/-- The output of `itciGF`. -/
noncomputable def itciGV (f : Fin q → ℕ) : Val :=
  match itciOt f with
  | some a => .list [.nat 1, encPerm (itciTr f a), .list ((itciMs f (some a)).map encPerm)]
  | none => .list [.nat 0]

/-- The cost bound of `itciGF`. -/
def itciGC (M : ℕ) : ℕ := 10 ^ 11 * (M + 2) ^ 6

theorem itciMs_length (f : Fin q → ℕ) (a : Fin q) : (itciMs f (some a)).length ≤ 2 * q := by
  simp [itciMs, itciT_length]

theorem itciCN_lt (f : Fin q → ℕ) (x : Fin q) : itciCN f x < q := (itciC f x).isLt

set_option maxHeartbeats 8000000 in
/-- **The generators of the even stabilizer as a program.** -/
theorem itci_g_spec {P : Program} {fg mpC cb fnd t fd ft mpT trB sw sb swt sch rng mps sbb par cmp : ℕ}
    (hfg : P.funs[fg]? = some (itciGF mpC fd mpT swt sch))
    (hmpC : P.HasAt mpC (mapFuns mpC cb)) (hcb : P.funs[cb]? = some (itciCB fnd))
    (hfnd : P.HasAt fnd (findFuns fnd t)) (ht : P.funs[t]? = some itciEqT)
    (hfd : P.HasAt fd (findFuns fd ft)) (hft : P.funs[ft]? = some itFixT)
    (hmpT : P.HasAt mpT (mapFuns mpT trB)) (htrB : P.funs[trB]? = some (itTrB sw))
    (hsw : P.HasAt sw (mapFuns sw sb)) (hsb : P.funs[sb]? = some itSwB)
    (hswt : P.HasAt swt (mapFuns swt sb))
    (hsch : P.funs[sch]? = some (itSchF rng mps)) (hrng : P.HasAt rng (rangeFuns rng))
    (hmps : P.HasAt mps (mapFuns mps sbb)) (hsbb : P.funs[sbb]? = some (itSchB par cmp))
    (hpar : ∀ σ : Perm (Fin q), FunDet P par (encPerm σ) (.nat (itpNInv σ % 2)) (itParC q))
    (hcmp : P.HasAt cmp (composeFuns cmp))
    (f : Fin q → ℕ) {M : ℕ} (hM : (encFun f).wt ≤ M) :
    FunDet P fg (.list [encFun f, natList (List.range q)]) (itciGV f) (itciGC M) := by
  have hqM := (itci_q_le_wt f).trans hM
  have hR := it_range_wt (q := q)
  have hq1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqa : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hqb : (q + 1) ^ 2 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hq2 : (q + 1) ^ 2 ≤ (M + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hq3 : (q + 1) ^ 3 ≤ (M + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hq6 : (q + 1) ^ 6 ≤ (M + 2) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have hM2 : M + 2 ≤ (M + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hM23 : (M + 2) ^ 2 ≤ (M + 2) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hM34 : (M + 2) ^ 3 ≤ (M + 2) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hM46 : (M + 2) ^ 4 ≤ (M + 2) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  set W := 100 * (M + 2) ^ 3 with hW
  have hC := it_encFun_wt (itciCN f) fun x => (itciCN_lt f x).le
  have hlt : ∀ x, itciCN f x < q := itciCN_lt f
  have hin := wt_list2_le (encFun f) (natList (List.range q))
  have hc2 := wt_list2_le (.list [encFun f, natList (List.range q)]) (natList (List.range q))
  have w0 : StDC P [Val.list [encFun f, natList (List.range q)]] (.var 0)
      (Val.list [encFun f, natList (List.range q)]) 1 0 W := StDC.var' rfl (by omega)
  have gF := StDC.get w0 (StDC.nat 0 (by omega)) (v := encFun f) rfl (by omega)
  have gR := StDC.get w0 (StDC.nat 1 (by omega)) (v := natList (List.range q)) rfl (by omega)
  -- the centers
  have d1 := StDC.call (StDC.mk2 (StDC.mk2 gF gR (by omega) (by omega)) gR (by omega) (by omega))
    (itci_c_tab hmpC hcb hfnd ht f hM) (by omega)
  set E1 : List Val := [Val.list [encFun f, natList (List.range q)], encFun (itciCN f)]
  have x0 : StDC P E1 (.var 0) (Val.list [encFun f, natList (List.range q)]) 1 0 W := StDC.var' rfl (by omega)
  have x1 : StDC P E1 (.var 1) (encFun (itciCN f)) 1 0 W := StDC.var' rfl (by omega)
  have xR := StDC.get x0 (StDC.nat 1 (by omega)) (v := natList (List.range q)) rfl (by omega)
  have hcr := wt_list2_le (encFun (itciCN f)) (natList (List.range q))
  -- the found point
  have hfnd' : FunDet P fd (.list [encFun (itciCN f), natList (List.range q)]) (.nat (itciIdx f))
      (10 ^ 5 * (q + 1) ^ 3) := by
    set xs := (List.range q).map Val.nat
    have hxl : xs.length = q := by simp [xs]
    have h := find_spec hfd (c := encFun (itciCN f)) (xs := xs) (q := itFixQ (itciCN f))
      (B := fun _ => 1000 * (q + 1) ^ 2) (fun v hv => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
        exact it_fixT_spec hft hlt ⟨x, List.mem_range.1 hx⟩)
    refine h.mono fun w c ⟨h1, h2⟩ => ⟨h1, ?_⟩
    have hsum : (xs.map fun _ => 1000 * (q + 1) ^ 2).sum = q * (1000 * (q + 1) ^ 2) := by
      simp [Function.comp_def, List.map_const', List.sum_replicate, xs]
    rw [hsum, hxl] at h2
    have hw : (Val.list [encFun (itciCN f), .list xs]).wt ≤ 30 * (q + 1) ^ 2 := by
      show (Val.list [encFun (itciCN f), natList (List.range q)]).wt ≤ _; omega
    refine h2.trans ?_
    have c1 : q * (1000 * (q + 1) ^ 2) ≤ 1000 * (q + 1) ^ 3 := by
      calc q * (1000 * (q + 1) ^ 2) ≤ (q + 1) * (1000 * (q + 1) ^ 2) :=
            Nat.mul_le_mul_right _ (by omega)
        _ = 1000 * (q + 1) ^ 3 := by ring
    have c2 : loopModK * (q + 1) * ((Val.list [encFun (itciCN f), .list xs]).wt + 2 * q + 3) ≤
        5 * 10 ^ 4 * (q + 1) ^ 3 := by
      calc loopModK * (q + 1) * ((Val.list [encFun (itciCN f), .list xs]).wt + 2 * q + 3)
          ≤ 1000 * (q + 1) * (50 * (q + 1) ^ 2) := Nat.mul_le_mul_left _ (by omega)
        _ = 5 * 10 ^ 4 * (q + 1) ^ 3 := by ring
    omega
  have hiq := itciIdx_le f
  have hiw : (Val.nat (itciIdx f)).wt ≤ q + 2 := by have := wt_nat_le (itciIdx f); omega
  have d2 := StDC.call (StDC.mk2 x1 xR (by omega) (by omega)) hfnd' (by omega)
  set E2 : List Val := E1 ++ [.nat (itciIdx f)]
  have y0 : StDC P E2 (.var 0) (Val.list [encFun f, natList (List.range q)]) 1 0 W := StDC.var' rfl (by omega)
  have y1 : StDC P E2 (.var 1) (encFun (itciCN f)) 1 0 W := StDC.var' rfl (by omega)
  have yR := StDC.get y0 (StDC.nat 1 (by omega)) (v := natList (List.range q)) rfl (by omega)
  -- the transpositions
  set T := (itciT f).map encPerm
  have hTw : (Val.list T).wt ≤ q * (9 * (q + 1) ^ 2) + 4 :=
    it_perms_wt (l := itciT f) (m := q) (by simp [itciT_length])
  have hT3 : q * (9 * (q + 1) ^ 2) ≤ 9 * (q + 1) ^ 3 := by
    calc q * (9 * (q + 1) ^ 2) ≤ (q + 1) * (9 * (q + 1) ^ 2) := Nat.mul_le_mul_right _ (by omega)
      _ = 9 * (q + 1) ^ 3 := by ring
  have hTm : FunDet P mpT (.list [.list [encFun (itciCN f), natList (List.range q)],
      natList (List.range q)]) (.list T)
      (q * (2 * 10 ^ 5 * (q + 1) ^ 3) + mapK * (q + 1) * (100 * (q + 1) ^ 3)) := by
    have h := map_det hmpT (c := .list [encFun (itciCN f), natList (List.range q)])
      (xs := (List.range q).map Val.nat) (F := itTrV (itciCN f)) (B := 2 * 10 ^ 5 * (q + 1) ^ 3)
      (fun v hv => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
        exact it_trB_spec htrB hsw hsb hlt ⟨x, List.mem_range.1 hx⟩)
    have e : ((List.range q).map Val.nat).map (itTrV (itciCN f)) = T := by
      simp only [T, itciT, List.map_map]; rfl
    rw [e] at h
    refine h.mono ?_
    have h3 := wt_list2_le (.list [encFun (itciCN f), natList (List.range q)])
      (natList (List.range q))
    simp only [List.length_map, List.length_range]
    refine Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _
    show (Val.list [.list [encFun (itciCN f), natList (List.range q)],
      natList (List.range q)]).wt + (Val.list T).wt + 1 ≤ _
    omega
  have hcr2 := wt_list2_le (.list [encFun (itciCN f), natList (List.range q)])
    (natList (List.range q))
  have d3 := StDC.call (StDC.mk2 (StDC.mk2 y1 yR (by omega) (by omega)) yR (by omega) (by omega))
    hTm (by omega)
  set E3 : List Val := E2 ++ [.list T]
  have z0 : StDC P E3 (.var 0) (Val.list [encFun f, natList (List.range q)]) 1 0 W := StDC.var' rfl (by omega)
  have z1 : StDC P E3 (.var 1) (encFun (itciCN f)) 1 0 W := StDC.var' rfl (by omega)
  have z2 : StDC P E3 (.var 2) (.nat (itciIdx f)) 1 0 W := StDC.var' rfl (by omega)
  have z3 : StDC P E3 (.var 3) (.list T) 1 0 W := StDC.var' rfl (by omega)
  have zR := StDC.get z0 (StDC.nat 1 (by omega)) (v := natList (List.range q)) rfl (by omega)
  have zl := StDC.length (vs := (List.range q).map Val.nat) zR (by simp; omega)
  simp only [List.length_map, List.length_range] at zl
  have hW4 : 4 ≤ W := by omega
  have hGw : (itciGV f).wt ≤ W := by
    unfold itciGV
    split
    · rename_i a _
      have := wt_list3_le (.nat 1) (encPerm (itciTr f a)) (.list ((itciMs f (some a)).map encPerm))
      have h1 := wt_encPerm_le (itciTr f a)
      have h2 := it_perms_wt (l := itciMs f (some a)) (m := 2 * q) (itciMs_length f a)
      have h3 : 2 * q * (9 * (q + 1) ^ 2) ≤ 18 * (q + 1) ^ 3 := by
        calc 2 * q * (9 * (q + 1) ^ 2) ≤ 2 * (q + 1) * (9 * (q + 1) ^ 2) :=
              Nat.mul_le_mul_right _ (by omega)
          _ = 18 * (q + 1) ^ 3 := by ring
      have := wt_nat_le 1
      omega
    · have := wt_list_le_of [Val.nat 0] (c := 2) (fun v hv => by
        rw [List.mem_singleton] at hv; subst hv; exact wt_nat_le 0)
      simp at this; omega
  have hbr := StDC.ite (v := itciGV f)
    (StDC.arith (op := .lt) z2 zl rfl (by
      have := wt_nat_le (GI.Machine.BinOp.eval .lt (itciIdx f) q)
      simp only [GI.Machine.BinOp.eval] at this ⊢; split_ifs at this ⊢ <;> omega))
    (fun hp => by
      have hlt' : itciIdx f < q := by
        by_contra h; simp [GI.Machine.BinOp.eval, h] at hp
      set a : Fin q := ⟨itciIdx f, hlt'⟩
      have hot : itciOt f = some a := by simp [itciOt, hlt', a]
      have hV : itciGV f = .list [.nat 1, encPerm (itciTr f a),
          .list ((itciMs f (some a)).map encPerm)] := by
        unfold itciGV; rw [hot]
      rw [hV] at hGw ⊢
      have ga := StDC.get (vs := (List.finRange q).map fun i => Val.nat (itciCN f i)) z1 z2
        (encFun_getElem? _ a) (by have := wt_nat_le (itciCN f a); have := hlt a; omega)
      have hpa := wt_list2_le (.nat (itciCN f a)) (.nat (itciIdx f))
      have hpa' := wt_list2_le (.list [.nat (itciCN f a), .nat (itciIdx f)]) (natList (List.range q))
      have hna := wt_nat_le (itciCN f a)
      have hca := hlt a
      have hsw' := it_swTab_spec hswt hsb (itciC f a) a
      have htw := wt_encPerm_le (itciTr f a)
      have htw' := wt_encPerm_le (Equiv.swap (itciC f a) a)
      have f1 := StDC.call (StDC.mk2 (StDC.mk2 ga z2 (by omega) hW4) zR (by omega) hW4) hsw'
        (by omega)
      set E4 : List Val := E3 ++ [encPerm (Equiv.swap (itciC f a) a)]
      have u4 : StDC P E4 (.var 4) (encPerm (itciTr f a)) 1 0 W := StDC.var' rfl (by omega)
      have u3 : StDC P E4 (.var 3) (.list T) 1 0 W := StDC.var' rfl (by omega)
      have hut := wt_list2_le (encPerm (itciTr f a)) (.list T)
      have hsch' := it_sch_spec hsch hrng hmps hsbb hpar hcmp (itciTr f a) (S := itciT f)
        (by rw [itciT_length]; omega)
      have hms := it_perms_wt (l := itciMs f (some a)) (m := 2 * q) (itciMs_length f a)
      have h3 : 2 * q * (9 * (q + 1) ^ 2) ≤ 18 * (q + 1) ^ 3 := by
        calc 2 * q * (9 * (q + 1) ^ 2) ≤ 2 * (q + 1) * (9 * (q + 1) ^ 2) :=
              Nat.mul_le_mul_right _ (by omega)
          _ = 18 * (q + 1) ^ 3 := by ring
      have hsch'' : FunDet P sch (.list [encPerm (itciTr f a), .list T])
          (.list ((itciMs f (some a)).map encPerm)) (itSchC q) := hsch'
      have f2 := StDC.call (StDC.mk2 u4 u3 (by omega) hW4) hsch'' (by omega)
      set E5 : List Val := E4 ++ [.list ((itciMs f (some a)).map encPerm)]
      have r4 : StDC P E5 (.var 4) (encPerm (itciTr f a)) 1 0 W := StDC.var' rfl (by omega)
      have r5 : StDC P E5 (.var 5) (.list ((itciMs f (some a)).map encPerm)) 1 0 W :=
        StDC.var' rfl (by omega)
      have f3 := StDC.mk3 (StDC.nat (env := E5) 1 (by omega)) r4 r5 hGw hW4
      exact StDC.letE f1 (StDC.letE f2 f3 hGw) hGw)
    (fun hp => by
      have hge : ¬ itciIdx f < q := fun h => by simp [GI.Machine.BinOp.eval, h] at hp
      have hot : itciOt f = none := by simp [itciOt, hge]
      have hV : itciGV f = .list [.nat 0] := by unfold itciGV; rw [hot]
      rw [hV] at hGw ⊢
      exact StDC.snoc (StDC.nil hW4) (StDC.nat 0 (by omega)) (by simpa using hGw))
    hGw
  have dall := StDC.letE d1 (StDC.letE d2 (StDC.letE d3 hbr hGw) hGw) hGw
  refine StDC.funDet hfg dall ?_
  unfold itciGC itciTC itSchC
  simp only [mapK]
  have c1 : q * (2 * 10 ^ 5 * (q + 1) ^ 3) ≤ 2 * 10 ^ 5 * (M + 2) ^ 4 := by
    calc q * (2 * 10 ^ 5 * (q + 1) ^ 3) ≤ (q + 1) * (2 * 10 ^ 5 * (q + 1) ^ 3) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 2 * 10 ^ 5 * (q + 1) ^ 4 := by ring
      _ ≤ 2 * 10 ^ 5 * (M + 2) ^ 4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
  have c2 : 1000 * (q + 1) * (100 * (q + 1) ^ 3) ≤ 10 ^ 5 * (M + 2) ^ 4 := by
    calc 1000 * (q + 1) * (100 * (q + 1) ^ 3) = 10 ^ 5 * (q + 1) ^ 4 := by ring
      _ ≤ 10 ^ 5 * (M + 2) ^ 4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
  omega

end GI.Impl
