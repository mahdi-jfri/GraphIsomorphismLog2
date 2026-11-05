module

public import Workspace.Impl.TermRecRep

@[expose] public section

/-!
# T5, the case `ℓ = 0` of the recursion (item 4)

"If `ℓ = 0`, the action is trivial, and equality of the multisets decides." With fuel `0` the
hypothesis `relDerived H N 0 ≤ N` says `H ≤ N`, and `N` fixes every listed object. So
`Iso_H(X, Y)` is `H` when `X = Y` and empty otherwise (`tmRi_base_iso`).

The program (`tmRiBaseE`) compares the two multisets by counts (`tmRi_ms_eq_iff`): `|X| = |Y|`
and every entry of `X` has as many equal entries in `X` as in `Y`. Equality of two objects is
the orbit test with the trivial group (`tmRi_sameOrb_nil`). The count of one entry is the
function `b + 4` (`tmRi_cnt_spec`), and the whole case is `tmRi_base_spec`.
-/

namespace GI.Impl

open GI.Lang GI.Multicoset Equiv
open GI.Machine (BinOp)
open GI.Cited (Val encPerm encGroup gens SolvableCosetIntersection DerivedSubgroup Membership)

variable {n : ℕ}

/-! ### The mathematics -/

theorem tmRi_gens_nil : gens ([] : List (Perm (Fin n))) = ⊥ := by
  simp [gens]

/-- Under the trivial group, two objects are in one orbit exactly when they are equal. -/
theorem tmRi_sameOrb_nil {x y : CObj ℕ (Perm (Fin n))} :
    SameOrb (gens ([] : List (Perm (Fin n)))) x y ↔ x = y := by
  rw [tmRi_gens_nil]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [Subgroup.mem_bot] at ha
    rw [ha, act_one]
  · rintro rfl
    exact sameOrb_refl _ _

open Classical in
/-- **The case `ℓ = 0`.** If `H ≤ N` and `N` fixes `X`, every element of `H` fixes `X`, so
`Iso_H(X, Y)` is `H` when `X = Y` and empty otherwise. -/
theorem tmRi_base_iso {G : Type} [Group G] {Ω : Type} [RAct G Ω] {H N : Subgroup G}
    (hHN : H ≤ N) {X Y : Multiset Ω} (hX : Fixes N X) :
    Iso H X Y = if X = Y then (H : Set G) else ∅ := by
  ext h
  rw [mem_iso]
  split_ifs with he
  · subst he
    exact ⟨fun h => h.1, fun hh => ⟨hh, hX.act_eq (hHN hh)⟩⟩
  · simp only [Set.mem_empty_iff_false, iff_false, not_and]
    intro hh hXY
    exact he (by rw [← hXY, hX.act_eq (hHN hh)])

/-! ### The count of one entry -/

/-- **The count test** `b + 4` on `[[gens G, X, Y], x]`: whether `x` has as many entries in its
`G`-orbit in `X` as in `Y`. -/
theorem tmRi_cnt_spec {P : Program} {b jsci jder jmem gObj : ℕ}
    {hsci : SolvableCosetIntersection} {hder : DerivedSubgroup} {hmem : Membership}
    (hP : TmRiAt P b jsci jder jmem gObj hsci hder hmem) {gs : List (Perm (Fin n))}
    {C : ℕ} {L : List (TmRiO n)} (hsol : TmRiListNorm (gens gs) L) (hgl : gs.length ≤ n ^ 2)
    (hok : TmRiOK C L) {Xs Ys : List (TmRiO n)} (hXs : ∀ o ∈ Xs, o ∈ L) (hYs : ∀ o ∈ Ys, o ∈ L)
    {x : Val} (hx : x ∈ L.map tmGlObjVal) {E : ℕ}
    (hE : (Val.list [.list [encGroup gs, tmGlObjsVal Xs, tmGlObjsVal Ys], x]).wt ≤ E) :
    FunDet P (b + 4) (.list [.list [encGroup gs, tmGlObjsVal Xs, tmGlObjsVal Ys], x])
      (boolVal (decide (((Xs.map tmGlObjVal).filter (tmRiQ (gens gs) x)).length =
        ((Ys.map tmGlObjVal).filter (tmRiQ (gens gs) x)).length)))
      (tmRiPcsStepC (tmRiObjPC (solvableCosetIntersectionPrim hsci) n C) E) := by
  set OP := tmRiObjPC (solvableCosetIntersectionPrim hsci) n C with hOPdef
  set Xv := Xs.map tmGlObjVal with hXv
  set Yv := Ys.map tmGlObjVal with hYv
  set c : Val := .list [encGroup gs, .list Xv, .list Yv] with hc
  set vs : List Val := [c, x] with hvs
  set ctx : Val := .list [encGroup gs, x] with hctx
  have hvE : (Val.list vs).wt ≤ E := hE
  have hsubX : ∀ y ∈ Xv, y ∈ L.map tmGlObjVal := fun y hy => by
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hy; exact List.mem_map_of_mem (hXs o ho)
  have hsubY : ∀ y ∈ Yv, y ∈ L.map tmGlObjVal := fun y hy => by
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hy; exact List.mem_map_of_mem (hYs o ho)
  have hp := tmRi_objP_vals hP hsol hgl hok hx
  -- weights
  have hcw : c.wt < (Val.list vs).wt := wt_le_wt_list (by simp [hvs])
  have hxw : x.wt < (Val.list vs).wt := wt_le_wt_list (by simp [hvs])
  have hGw : (encGroup gs).wt < c.wt := wt_le_wt_list (by simp [hc])
  have hXw : (Val.list Xv).wt < c.wt := wt_le_wt_list (by simp [hc])
  have hYw : (Val.list Yv).wt < c.wt := wt_le_wt_list (by simp [hc])
  have hXl : Xv.length < (Val.list Xv).wt := length_lt_wt_list Xv
  have hYl : Yv.length < (Val.list Yv).wt := length_lt_wt_list Yv
  have hctxw : ctx.wt ≤ 2 * ((encGroup gs).wt + x.wt) + 6 := wt_list2_le _ _
  have hcXw : (Val.list [ctx, .list Xv]).wt ≤ 2 * (ctx.wt + (Val.list Xv).wt) + 6 := wt_list2_le _ _
  have hcYw : (Val.list [ctx, .list Yv]).wt ≤ 2 * (ctx.wt + (Val.list Yv).wt) + 6 := wt_list2_le _ _
  have hfXw : (Val.list (Xv.filter (tmRiQ (gens gs) x))).wt ≤ (Val.list Xv).wt :=
    wt_list_sublist List.filter_sublist
  have hfYw : (Val.list (Yv.filter (tmRiQ (gens gs) x))).wt ≤ (Val.list Yv).wt :=
    wt_list_sublist List.filter_sublist
  have hE1 : 1 ≤ (E + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hEE : E + 1 ≤ (E + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  -- the filters
  have hfX := filter_spec hP.filt (c := ctx) (xs := Xv) (q := tmRiQ (gens gs) x)
    (fun y hy => hp y (hsubX y hy))
  have hfY := filter_spec hP.filt (c := ctx) (xs := Yv) (q := tmRiQ (gens gs) x)
    (fun y hy => hp y (hsubY y hy))
  have hsX := tmRi_sum_const Xv (fun _ => OP) (K := OP) (fun _ _ => le_rfl)
  have hsY := tmRi_sum_const Yv (fun _ => OP) (K := OP) (fun _ _ => le_rfl)
  have hmX : loopModK * (Xv.length + 1) * ((Val.list [ctx, .list Xv]).wt + Xv.length +
      (Val.list (Xv.filter (tmRiQ (gens gs) x))).wt + 1) ≤ 20000 * (E + 1) ^ 2 := by
    rw [mul_assoc]
    calc _ ≤ loopModK * (20 * (E + 1) ^ 2) :=
          Nat.mul_le_mul_left _ (tmRi_ml (E := E) (c := 20) (by omega) (by omega))
      _ = 20000 * (E + 1) ^ 2 := by simp only [loopModK]; ring
  have hmY : loopModK * (Yv.length + 1) * ((Val.list [ctx, .list Yv]).wt + Yv.length +
      (Val.list (Yv.filter (tmRiQ (gens gs) x))).wt + 1) ≤ 20000 * (E + 1) ^ 2 := by
    rw [mul_assoc]
    calc _ ≤ loopModK * (20 * (E + 1) ^ 2) :=
          Nat.mul_le_mul_left _ (tmRi_ml (E := E) (c := 20) (by omega) (by omega))
      _ = 20000 * (E + 1) ^ 2 := by simp only [loopModK]; ring
  have hOX : Xv.length * OP ≤ E * OP := Nat.mul_le_mul_right _ (by omega)
  have hOY : Yv.length * OP ≤ E * OP := Nat.mul_le_mul_right _ (by omega)
  have hfX' : FunDet P (b + 51) (.list [ctx, .list Xv]) (.list (Xv.filter (tmRiQ (gens gs) x)))
      ((Xv.map fun _ => OP).sum + loopModK * (Xv.length + 1) * ((Val.list [ctx, .list Xv]).wt +
        Xv.length + (Val.list (Xv.filter (tmRiQ (gens gs) x))).wt + 1)) :=
    hfX.mono fun w c h => ⟨h.1, by have h2 := h.2; rw [h.1] at h2; exact h2⟩
  have hfY' : FunDet P (b + 51) (.list [ctx, .list Yv]) (.list (Yv.filter (tmRiQ (gens gs) x)))
      ((Yv.map fun _ => OP).sum + loopModK * (Yv.length + 1) * ((Val.list [ctx, .list Yv]).wt +
        Yv.length + (Val.list (Yv.filter (tmRiQ (gens gs) x))).wt + 1)) :=
    hfY.mono fun w c h => ⟨h.1, by have h2 := h.2; rw [h.1] at h2; exact h2⟩
  -- the body
  have d0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have d1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
  have dg := Det.get' d0 (Det.nat 0) (v := encGroup gs) rfl
  have dctx := Det.mk2 dg d1
  have dX := Det.get' d0 (Det.nat 1) (v := .list Xv) rfl
  have dY := Det.get' d0 (Det.nat 2) (v := .list Yv) rfl
  have dcX := Det.length (Det.call (Det.mk2 dctx dX) hfX')
  have dcY := Det.length (Det.call (Det.mk2 dctx dY) hfY')
  have dall := Det.arith (op := .eq) dcX dcY
  have hval : Val.nat (BinOp.eval .eq (Xv.filter (tmRiQ (gens gs) x)).length
      (Yv.filter (tmRiQ (gens gs) x)).length) =
      boolVal (decide ((Xv.filter (tmRiQ (gens gs) x)).length =
        (Yv.filter (tmRiQ (gens gs) x)).length)) := by
    by_cases h : (Xv.filter (tmRiQ (gens gs) x)).length = (Yv.filter (tmRiQ (gens gs) x)).length
      <;> simp [BinOp.eval, h]
  rw [hval] at dall
  refine FunDet.intro hP.cntP (dall.mono ?_)
  have hb := wt_boolVal_le (decide ((Xv.filter (tmRiQ (gens gs) x)).length =
    (Yv.filter (tmRiQ (gens gs) x)).length))
  have hlX := wt_nat_le (Xv.filter (tmRiQ (gens gs) x)).length
  have hlY := wt_nat_le (Yv.filter (tmRiQ (gens gs) x)).length
  have hlX' : (Xv.filter (tmRiQ (gens gs) x)).length ≤ Xv.length := List.length_filter_le _ _
  have hlY' : (Yv.filter (tmRiQ (gens gs) x)).length ≤ Yv.length := List.length_filter_le _ _
  have hg0 : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
  have hg1 : (Val.nat 1).wt ≤ 3 := wt_nat_le 1
  have hg2 : (Val.nat 2).wt ≤ 4 := wt_nat_le 2
  unfold tmRiPcsStepC
  have hOP2 : 2 * E * OP = E * OP + E * OP := by ring
  have r1 : (Val.list [encGroup gs, x]).wt = ctx.wt := rfl
  have r2 : (Val.list [Val.list [encGroup gs, x], Val.list Xv]).wt =
    (Val.list [ctx, Val.list Xv]).wt := rfl
  have r3 : (Val.list [Val.list [encGroup gs, x], Val.list Yv]).wt =
    (Val.list [ctx, Val.list Yv]).wt := rfl
  omega

/-! ### The case `ℓ = 0` as a program -/

/-- The cost bound of the case `ℓ = 0`, for an input of weight at most `W`, with `OP` the cost
of the orbit predicate. -/
def tmRiBaseC (OP n W : ℕ) : ℕ :=
  W * tmRiPcsStepC OP (10 * W + 2000 * (n + 1) ^ 6) + 10 ^ 7 * (W + (n + 1) ^ 6 + 1) ^ 2

open Classical in
/-- **The case `ℓ = 0`.** -/
theorem tmRi_base_spec {P : Program} {b jsci jder jmem gObj : ℕ}
    {hsci : SolvableCosetIntersection} {hder : DerivedSubgroup} {hmem : Membership}
    (hP : TmRiAt P b jsci jder jmem gObj hsci hder hmem) {M : ℕ} {σH σN : List (Perm (Fin n))}
    {X Y : List (TmRiO n)} (hHN : gens σH ≤ gens σN) (hNX : Fixes (gens σN) (tmGlMs X))
    (hHl : σH.length ≤ n ^ 2) (hok : TmRecObjOK M (X ++ Y)) {W : ℕ}
    (hW : (tmRecIn 0 σH σN X Y).wt ≤ W) :
    FunAll P (b + 1) (tmRecIn 0 σH σN X Y) (fun u cost =>
      CosetC n u (Iso (gens σH) (tmGlMs X) (tmGlMs Y)) ∧
      cost ≤ tmRiBaseC (tmRiObjPC (solvableCosetIntersectionPrim hsci) n (2 * M)) n W) := by
  set OP := tmRiObjPC (solvableCosetIntersectionPrim hsci) n (2 * M) with hOPdef
  set Xv := X.map tmGlObjVal with hXv
  set Yv := Y.map tmGlObjVal with hYv
  set g1 : Val := encGroup ([] : List (Perm (Fin n))) with hg1
  set vs : List Val := [.nat 0, encGroup σH, encGroup σN, .list Xv, .list Yv] with hvs
  have ha : tmRecIn 0 σH σN X Y = .list vs := rfl
  rw [ha] at hW ⊢
  have hok' : TmRiOK (2 * M) (X ++ Y) := fun o ho =>
    ⟨(hok o ho).1, by have := (hok o ho).2.1; omega, (hok o ho).2.2⟩
  have hsol1 : TmRiListNorm (gens ([] : List (Perm (Fin n)))) (X ++ Y) := TmRiListNorm.bot (X ++ Y)
  -- weights
  have hHw : (encGroup σH).wt < (Val.list vs).wt := wt_le_wt_list (by simp [hvs])
  have hXw : (Val.list Xv).wt < (Val.list vs).wt := wt_le_wt_list (by simp [hvs])
  have hYw : (Val.list Yv).wt < (Val.list vs).wt := wt_le_wt_list (by simp [hvs])
  have hXl : Xv.length < (Val.list Xv).wt := length_lt_wt_list Xv
  have hYl : Yv.length < (Val.list Yv).wt := length_lt_wt_list Yv
  have hg1w : g1.wt ≤ 320 * (n + 1) ^ 6 := wt_encGroup_le_sq (by simp)
  have hF1 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  set F := (n + 1) ^ 6 with hF
  set c : Val := .list [g1, .list Xv, .list Yv] with hc
  have hcw : c.wt ≤ 2 * (g1.wt + (Val.list Xv).wt + (Val.list Yv).wt) + 7 := wt_list3_le _ _ _
  have hacw : (Val.list [c, .list Xv]).wt ≤ 2 * (c.wt + (Val.list Xv).wt) + 6 := wt_list2_le _ _
  set E := 10 * W + 2000 * F with hE
  -- the count test on every entry of `X`
  have hcnt : ∀ x ∈ Xv, FunDet P (b + 4) (.list [c, x])
      (boolVal (decide ((Xv.filter (tmRiQ (gens ([] : List (Perm (Fin n)))) x)).length =
        (Yv.filter (tmRiQ (gens ([] : List (Perm (Fin n)))) x)).length)))
      (tmRiPcsStepC OP E) := by
    intro x hx
    have hxw : x.wt < (Val.list Xv).wt := wt_le_wt_list hx
    have hx' : x ∈ (X ++ Y).map tmGlObjVal := by
      rw [List.map_append]; exact List.mem_append_left _ hx
    refine tmRi_cnt_spec hP hsol1 (by simp) hok' (Xs := X) (Ys := Y)
      (fun o ho => List.mem_append_left _ ho) (fun o ho => List.mem_append_right _ ho) hx' ?_
    have := wt_list2_le c x
    show (Val.list [c, x]).wt ≤ E
    omega
  have hall := all_spec hP.all (c := c) hcnt
  set q : Val → Bool := fun x => decide ((Xv.filter (tmRiQ (gens ([] : List (Perm (Fin n)))) x)).length =
    (Yv.filter (tmRiQ (gens ([] : List (Perm (Fin n)))) x)).length) with hq
  have hsA := tmRi_sum_const Xv (fun _ => tmRiPcsStepC OP E) (K := tmRiPcsStepC OP E)
    (fun _ _ => le_rfl)
  have hall' : FunDet P (b + 57) (.list [c, .list Xv]) (boolVal (Xv.all q))
      ((Xv.map fun _ => tmRiPcsStepC OP E).sum +
        loopModK * (Xv.length + 1) * ((Val.list [c, .list Xv]).wt + Xv.length + 4)) :=
    hall.mono fun w c h => h
  -- the body
  have d1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) (v := encGroup σH) rfl
  have dn := Det.get' d1 (Det.nat 0) (v := .nat n) rfl
  have dl1 := Det.get' d1 (Det.nat 1) (v := .list ((1 :: σH).map encPerm)) rfl
  have de1 := Det.get' dl1 (Det.nat 0) (v := encPerm 1) rfl
  have dg := Det.mk2 dn (Det.mk1 de1)
  have hg : Val.list [.nat n, .list [encPerm (1 : Perm (Fin n))]] = g1 := by
    simp [hg1, encGroup, GI.Cited.encPerms]
  rw [hg] at dg
  set env : List Val := [.list vs, g1] with henv
  have e3 := Det.arg' (P := P) (vs := vs) (rest := [g1]) (j := 3) (v := .list Xv) rfl
  have e4 := Det.arg' (P := P) (vs := vs) (rest := [g1]) (j := 4) (v := .list Yv) rfl
  have elen := Det.arith (op := .eq) (Det.length e3) (Det.length e4)
  have ev1 := Det.var' (P := P) (env := env) (i := 1) (v := g1) rfl
  have dallc := Det.call (Det.mk2 (Det.mk3 ev1 e3 e4) e3) hall'
  set u1 : Val := .list [encPerm (1 : Perm (Fin n)), encGroup σH] with hu1
  have e1 := Det.arg' (P := P) (vs := vs) (rest := [g1]) (j := 1) (v := encGroup σH) rfl
  have dthen := Det.mk2 (Det.get' (Det.get' e1 (Det.nat 1) (v := .list ((1 :: σH).map encPerm)) rfl)
    (Det.nat 0) (v := encPerm 1) rfl) e1
  have dinner := tmRi_ite dallc dthen (Det.nil (P := P) (env := env))
  have douter := tmRi_ite elen dinner (Det.nil (P := P) (env := env))
  have dbody := Det.letE dg douter
  refine FunAll.intro hP.base (EvalAll.mono dbody fun w cw ⟨hw, hcw'⟩ => ⟨?_, ?_⟩)
  · -- the answer
    subst hw
    have hHN' := tmRi_base_iso hHN hNX (Y := tmGlMs Y)
    -- equality of the multisets from the counts
    have hqv : ∀ a b : Val, tmRiQ (gens ([] : List (Perm (Fin n)))) a b = true ↔
        tmRiObj (tmRiDec (n := n) a) = tmRiObj (tmRiDec (n := n) b) := by
      intro a b; simp only [tmRiQ, decide_eq_true_eq]; exact tmRi_sameOrb_nil
    have hms := tmRi_ms_eq_iff (fun v => tmRiObj (tmRiDec (n := n) v)) _ hqv Xv Yv
    have hmap : ∀ Z : List (TmRiO n), (((Z.map tmGlObjVal).map
        (fun v => tmRiObj (tmRiDec (n := n) v)) : List (CObj ℕ (Perm (Fin n)))) :
        Multiset (CObj ℕ (Perm (Fin n)))) = tmGlMs Z := by
      intro Z
      rw [List.map_map]
      unfold tmGlMs
      congr 1
      exact List.map_congr_left fun o _ => by simp [tmRiDec_val]
    rw [hmap, hmap] at hms
    have hlenv : Xv.length = Yv.length ↔ X.length = Y.length := by simp [hXv, hYv]
    by_cases he : tmGlMs X = tmGlMs Y
    · obtain ⟨hl, hcn⟩ := hms.1 he
      have hall1 : Xv.all q = true := List.all_eq_true.2 fun x hx => by
        simp only [hq, decide_eq_true_eq]; exact hcn x hx
      have hl' : BinOp.eval .eq Xv.length Yv.length ≠ 0 := by simp [BinOp.eval, hl]
      have hb : (boolVal (Xv.all q)).isNatNum = 1 := by rw [hall1]; rfl
      rw [if_neg hl']
      have : (if (Xv.all q).toNat = 0 then Val.list [] else u1) = u1 := by rw [hall1]; rfl
      rw [this]
      refine Or.inr ⟨1, σH, rfl, hHl, ?_⟩
      rw [hHN', if_pos he]
      ext g; simp
    · rw [hHN', if_neg he]
      refine Or.inl ⟨?_, rfl⟩
      by_cases hl : Xv.length = Yv.length
      · have hall0 : Xv.all q = false := by
          rw [Bool.eq_false_iff]
          intro hall1
          apply he
          refine hms.2 ⟨hl, fun x hx => ?_⟩
          have := List.all_eq_true.1 hall1 x hx
          simpa [hq] using this
        have hl' : BinOp.eval .eq Xv.length Yv.length ≠ 0 := by simp [BinOp.eval, hl]
        rw [if_neg hl', hall0]
        rfl
      · have hl' : BinOp.eval .eq Xv.length Yv.length = 0 := by simp [BinOp.eval, hl]
        rw [if_pos hl']
  · -- the cost
    have hu1w : u1.wt ≤ 2 * ((encPerm (1 : Perm (Fin n))).wt + (encGroup σH).wt) + 6 :=
      wt_list2_le _ _
    have hp1 : (encPerm (1 : Perm (Fin n))).wt ≤ 4 * (n + 1) ^ 2 := wt_encPerm_le _
    have hn2 : (n + 1) ^ 2 ≤ F := Nat.pow_le_pow_right (by omega) (by omega)
    have hHw' : (encGroup σH).wt ≤ 320 * F := wt_encGroup_le_sq hHl
    have hnn : (Val.nat n).wt < (encGroup σH).wt := wt_le_wt_list (by simp [encGroup, GI.Cited.encPerms])
    have hl1 : (Val.list ((1 :: σH).map encPerm)).wt < (encGroup σH).wt :=
      wt_le_wt_list (by simp [encGroup, GI.Cited.encPerms])
    have hp1' : (encPerm (1 : Perm (Fin n))).wt < (Val.list ((1 :: σH).map encPerm)).wt :=
      wt_le_wt_list (List.mem_cons_self ..)
    have hm1 := wt_list1_le (encPerm (1 : Perm (Fin n)))
    have hm2 := wt_list2_le (.nat n) (.list [encPerm (1 : Perm (Fin n))])
    have hw1 := wt_boolVal_le (Xv.all q)
    have hw2 : (Val.nat (BinOp.eval .eq Xv.length Yv.length)).wt ≤ 3 := by
      have := wt_nat_le (BinOp.eval .eq Xv.length Yv.length)
      have : BinOp.eval .eq Xv.length Yv.length ≤ 1 := by simp only [BinOp.eval]; split <;> omega
      omega
    have hlx := wt_nat_le Xv.length
    have hly := wt_nat_le Yv.length
    have hni : ∀ i : ℕ, i ≤ 4 → (Val.nat i).wt ≤ 6 := fun i hi => by
      have := wt_nat_le i; omega
    have h0 := hni 0 (by omega)
    have h1 := hni 1 (by omega)
    have h3 := hni 3 (by omega)
    have h4 := hni 4 (by omega)
    have hmm : loopModK * (Xv.length + 1) * ((Val.list [c, .list Xv]).wt + Xv.length + 4) ≤
        2 * 10 ^ 6 * (W + F + 1) ^ 2 := by
      rw [mul_assoc]
      have : (Xv.length + 1) * ((Val.list [c, .list Xv]).wt + Xv.length + 4) ≤
          (W + F + 1) * (2000 * (W + F + 1)) := Nat.mul_le_mul (by omega) (by omega)
      calc loopModK * ((Xv.length + 1) * ((Val.list [c, .list Xv]).wt + Xv.length + 4))
          ≤ loopModK * ((W + F + 1) * (2000 * (W + F + 1))) := Nat.mul_le_mul_left _ this
        _ = 2 * 10 ^ 6 * (W + F + 1) ^ 2 := by simp only [loopModK]; ring
    have hXK : Xv.length * tmRiPcsStepC OP E ≤ W * tmRiPcsStepC OP E :=
      Nat.mul_le_mul_right _ (by omega)
    have hm3 := wt_list3_le g1 (.list Xv) (.list Yv)
    have hm4 := wt_list2_le (Val.list [g1, .list Xv, .list Yv]) (.list Xv)
    have hWF : (W + F + 1) ^ 2 = W * W + 2 * W * F + F * F + 2 * W + 2 * F + 1 := by ring
    have hvw : (Val.list vs).wt = (Val.list [.nat 0, encGroup σH, encGroup σN, .list Xv,
      .list Yv]).wt := rfl
    unfold tmRiBaseC
    rw [← hF, ← hE]
    have hW' : (Val.list [Val.nat 0, encGroup σH, encGroup σN, Val.list Xv, Val.list Yv]).wt ≤ W := hW
    have hu1e : (Val.list [encPerm (1 : Perm (Fin n)), encGroup σH]).wt = u1.wt := rfl
    have hnil5 : (Val.list []).wt = 4 := wt_list_nil
    by_cases hA : (Xv.all q).toNat = 0 <;> by_cases hB : BinOp.eval .eq Xv.length Yv.length = 0 <;>
      simp only [hA, hB, if_true, if_false] at hcw' <;>
    omega

end GI.Impl
