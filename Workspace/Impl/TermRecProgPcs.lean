import Workspace.Impl.TermRecProgTest
import Workspace.CitedChecks.AlgoDetermined

/-!
# T5, the pieces of a list of objects

`tmRi_pcs_spec`: on `[gens A, Z]` with `Z` the values of a list `L` of objects, the function
`b + 6` returns the list of the `A`-orbit classes of `Z` (each as the list of its entries, in
the order of their first entries), `tmRiPcs (tmRiQ A) Z (nat 0) |Z|`. By `tmRiPcs_eq` these are
the pieces `pieces A (tmGlMs L)` (`tmRi_pcs_eq`).
-/

namespace GI.Impl

open GI.Lang GI.Multicoset Equiv
open GI.Machine (BinOp)
open GI.Cited (Val encPerm encGroup gens SolvableCosetIntersection DerivedSubgroup Membership)

variable {n : ℕ}

theorem tmRi_objVal_inj {o o' : TmRiO n} (h : tmGlObjVal o = tmGlObjVal o') : o = o' := by
  obtain ⟨c, σ, x⟩ := o
  obtain ⟨c', σ', x'⟩ := o'
  simp only [tmGlObjVal, Val.list.injEq, List.cons.injEq, Val.nat.injEq, and_true] at h
  obtain ⟨rfl, h2, h3⟩ := h
  rw [GI.CitedChecks.detm_encGroup_inj h2, GI.CitedChecks.detm_encPerm_inj h3]

open Classical in
/-- Decoding an object value (any object for a value that is not one). -/
noncomputable def tmRiDec (v : Val) : TmRiO n :=
  if h : ∃ o : TmRiO n, tmGlObjVal o = v then h.choose else (0, [], 1)

theorem tmRiDec_val (o : TmRiO n) : tmRiDec (n := n) (tmGlObjVal o) = o := by
  have h : ∃ o' : TmRiO n, tmGlObjVal o' = tmGlObjVal o := ⟨o, rfl⟩
  rw [tmRiDec, dif_pos h]
  exact tmRi_objVal_inj h.choose_spec

open Classical in
/-- The orbit test on values. -/
noncomputable def tmRiQ (G : Subgroup (Perm (Fin n))) (v w : Val) : Bool :=
  decide (SameOrb G (tmRiObj (tmRiDec (n := n) v)) (tmRiObj (tmRiDec (n := n) w)))

/-- `Det.ite'` with the sum of the branch costs in place of their maximum. -/
theorem tmRi_ite {P : Program} {env : List Val} {c t e : Expr} {x : ℕ} {v1 v0 : Val}
    {cc ct ce : ℕ} (hc : Det P env c (.nat x) cc) (ht : Det P env t v1 ct)
    (he : Det P env e v0 ce) :
    Det P env (.ite c t e) (if x = 0 then v0 else v1) (cc + ct + ce + v1.wt + v0.wt + 1) :=
  (Det.ite' hc ht he).mono (by
    have h1 : max ct ce ≤ ct + ce := max_le (by omega) (by omega)
    have h2 : max v1.wt v0.wt ≤ v1.wt + v0.wt := max_le (by omega) (by omega)
    omega)

/-- The objects of a list are well formed with colors at most `C`. -/
def TmRiOK (C : ℕ) (L : List (TmRiO n)) : Prop :=
  ∀ o ∈ L, o.2.1.length ≤ n ^ 2 ∧ o.1 ≤ C ∧ ∀ o' ∈ L, o.1 = o'.1 → gens o.2.1 = gens o'.2.1

theorem tmRi_ml {a b E c : ℕ} (ha : a ≤ E) (hb : b ≤ c * (E + 1)) :
    (a + 1) * b ≤ c * (E + 1) ^ 2 :=
  calc (a + 1) * b ≤ (E + 1) * (c * (E + 1)) := Nat.mul_le_mul (by omega) hb
    _ = c * (E + 1) ^ 2 := by ring

theorem tmRi_sum_const {α : Type} (l : List α) (B : α → ℕ) {K : ℕ} (h : ∀ x ∈ l, B x ≤ K) :
    (l.map B).sum ≤ l.length * K := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := h a (by simp)
    have := ih fun x hx => h x (by simp [hx])
    nlinarith

/-- The predicate `b + 3` on the values of a list. -/
theorem tmRi_objP_vals {P : Program} {b jsci jder jmem gObj : ℕ}
    {hsci : SolvableCosetIntersection} {hder : DerivedSubgroup} {hmem : Membership}
    (hP : TmRiAt P b jsci jder jmem gObj hsci hder hmem) {gs : List (Perm (Fin n))}
    (hsol : IsSolvable (gens gs)) (hgl : gs.length ≤ n ^ 2) {C : ℕ} {L : List (TmRiO n)}
    (hok : TmRiOK C L) {z : Val} (hz : z ∈ L.map tmGlObjVal) :
    ∀ x ∈ L.map tmGlObjVal, FunDet P (b + 3) (.list [.list [encGroup gs, z], x])
      (boolVal (tmRiQ (gens gs) z x)) (tmRiObjPC (solvableCosetIntersectionPrim hsci) n C) := by
  intro x hx
  obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hz
  obtain ⟨o', ho', rfl⟩ := List.mem_map.1 hx
  have h1 := hok o ho
  have h2 := hok o' ho'
  have := tmRi_objP_spec hP hsol hgl h1.1 h2.1 (h1.2.2 o' ho') h1.2.1 h2.2.1
  convert this using 2
  simp only [tmRiQ, tmRiDec_val, decide_eq_decide]

/-- The cost bound of one step of the pieces, for a context of weight at most `E`. -/
def tmRiPcsStepC (OP E : ℕ) : ℕ := 2 * E * OP + 10 ^ 6 * (E + 1) ^ 2

/-- **One step of the pieces.** -/
theorem tmRi_pcsStep_spec {P : Program} {b jsci jder jmem gObj : ℕ}
    {hsci : SolvableCosetIntersection} {hder : DerivedSubgroup} {hmem : Membership}
    (hP : TmRiAt P b jsci jder jmem gObj hsci hder hmem) {gs : List (Perm (Fin n))}
    (hsol : IsSolvable (gens gs)) (hgl : gs.length ≤ n ^ 2) {C : ℕ} {L : List (TmRiO n)}
    (hok : TmRiOK C L) {i : ℕ} (hi : i < L.length) {acc : List Val} {E : ℕ}
    (hE : (Val.list [encGroup gs, .list (L.map tmGlObjVal)]).wt ≤ E)
    (hacc : (Val.list acc).wt ≤ 4 * (E + 1) ^ 2) :
    FunDet P (b + 7) (.list [.list [encGroup gs, .list (L.map tmGlObjVal)], .nat i, .list acc])
      (.list (acc ++ (if (L.map tmGlObjVal).findIdx
          (tmRiQ (gens gs) ((L.map tmGlObjVal).getD i (.nat 0))) = i then
        [.list ((L.map tmGlObjVal).filter
          (tmRiQ (gens gs) ((L.map tmGlObjVal).getD i (.nat 0))))] else [])))
      (tmRiPcsStepC (tmRiObjPC (solvableCosetIntersectionPrim hsci) n C) E) := by
  set Zv := L.map tmGlObjVal with hZv
  set c : Val := .list [encGroup gs, .list Zv] with hc
  set vs : List Val := [c, .nat i, .list acc] with hvs
  have hiZ : i < Zv.length := by simpa [hZv] using hi
  set z := Zv[i] with hzdef
  have hzD : Zv.getD i (.nat 0) = z := by simp [hzdef, List.getD_eq_getElem?_getD, hiZ]
  rw [hzD]
  have hzm : z ∈ Zv := List.getElem_mem hiZ
  -- weights
  have hGw : (encGroup gs).wt < c.wt := wt_le_wt_list (by simp)
  have hZw : (Val.list Zv).wt < c.wt := wt_le_wt_list (by simp)
  have hzw : z.wt < (Val.list Zv).wt := wt_le_wt_list hzm
  have hlen : Zv.length < (Val.list Zv).wt := length_lt_wt_list Zv
  have hiw := wt_nat_le i
  have hvw : (Val.list vs).wt ≤ 2 * (c.wt + (Val.nat i).wt + (Val.list acc).wt) + 7 :=
    wt_list3_le _ _ _
  set ctx : Val := .list [encGroup gs, z] with hctx
  have hctxw : ctx.wt ≤ 2 * ((encGroup gs).wt + z.wt) + 6 := wt_list2_le _ _
  have hcz : (Val.list [ctx, .list Zv]).wt ≤ 2 * (ctx.wt + (Val.list Zv).wt) + 6 :=
    wt_list2_le _ _
  have hE1 : 1 ≤ (E + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hEE : E + 1 ≤ (E + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  -- the calls
  have hfind := find_spec hP.find (c := ctx) (xs := Zv) (q := tmRiQ (gens gs) z)
    (tmRi_objP_vals hP hsol hgl hok hzm)
  have hfilt := filter_spec hP.filt (c := ctx) (xs := Zv) (q := tmRiQ (gens gs) z)
    (tmRi_objP_vals hP hsol hgl hok hzm)
  have hsf := tmRi_sum_const Zv (fun _ => (tmRiObjPC (solvableCosetIntersectionPrim hsci) n C)) (K := (tmRiObjPC (solvableCosetIntersectionPrim hsci) n C)) (fun _ _ => le_rfl)
  have hfw : (Val.list (Zv.filter (tmRiQ (gens gs) z))).wt ≤ (Val.list Zv).wt :=
    wt_list_sublist List.filter_sublist
  have hm1 : loopModK * (Zv.length + 1) * ((Val.list [ctx, .list Zv]).wt + 2 * Zv.length + 3) ≤
      20000 * (E + 1) ^ 2 := by
    rw [mul_assoc]
    calc _ ≤ loopModK * (20 * (E + 1) ^ 2) :=
          Nat.mul_le_mul_left _ (tmRi_ml (E := E) (c := 20) (by omega) (by omega))
      _ = 20000 * (E + 1) ^ 2 := by simp only [loopModK]; ring
  have hm2 : loopModK * (Zv.length + 1) * ((Val.list [ctx, .list Zv]).wt + Zv.length +
      (Val.list (Zv.filter (tmRiQ (gens gs) z))).wt + 1) ≤ 20000 * (E + 1) ^ 2 := by
    rw [mul_assoc]
    calc _ ≤ loopModK * (20 * (E + 1) ^ 2) :=
          Nat.mul_le_mul_left _ (tmRi_ml (E := E) (c := 20) (by omega) (by omega))
      _ = 20000 * (E + 1) ^ 2 := by simp only [loopModK]; ring
  have hOP : Zv.length * (tmRiObjPC (solvableCosetIntersectionPrim hsci) n C) ≤ E * (tmRiObjPC (solvableCosetIntersectionPrim hsci) n C) := Nat.mul_le_mul_right _ (by omega)
  -- the body
  have d0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have d1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
  have dz := Det.get' (Det.get' d0 (Det.nat 1) (v := .list Zv) rfl) d1 (v := z)
    (by simp [hzdef, hiZ])
  have dctx := Det.mk2 (Det.get' (Det.arg' (P := P) (vs := vs) (rest := [z]) (j := 0) rfl)
    (Det.nat 0) (v := encGroup gs) rfl) (Det.var' (P := P) (env := [.list vs, z]) (i := 1) rfl)
  have e0 := Det.arg' (P := P) (vs := vs) (rest := [z, ctx]) (j := 0) rfl
  have eZ := Det.get' e0 (Det.nat 1) (v := .list Zv) rfl
  have ev := Det.var' (P := P) (env := [.list vs, z, ctx]) (i := 2) (v := ctx) rfl
  have dfind := Det.call (Det.mk2 ev eZ) (hfind.mono fun w c h => ⟨h.1, h.2⟩)
  have dcmp := Det.arith' (op := .eq) dfind (Det.arg' (P := P) (vs := vs) (rest := [z, ctx])
    (j := 1) rfl) rfl
  have dacc := Det.arg' (P := P) (vs := vs) (rest := [z, ctx]) (j := 2) rfl
  have hfilt' : FunDet P (b + 51) (.list [ctx, .list Zv]) (.list (Zv.filter (tmRiQ (gens gs) z)))
      ((Zv.map fun _ => (tmRiObjPC (solvableCosetIntersectionPrim hsci) n C)).sum + loopModK * (Zv.length + 1) * ((Val.list [ctx, .list Zv]).wt +
        Zv.length + (Val.list (Zv.filter (tmRiQ (gens gs) z))).wt + 1)) :=
    hfilt.mono fun w c h => ⟨h.1, by have h2 := h.2; rw [h.1] at h2; exact h2⟩
  have dfilt := Det.call (Det.mk2 ev eZ) hfilt'
  have dsnoc := Det.snoc dacc dfilt
  have dite := tmRi_ite dcmp dsnoc dacc
  have dall := Det.letE dz (Det.letE dctx dite)
  have hval : (if BinOp.eval .eq (Zv.findIdx (tmRiQ (gens gs) z)) i = 0 then Val.list acc
      else Val.list (acc ++ [.list (Zv.filter (tmRiQ (gens gs) z))])) =
      .list (acc ++ (if Zv.findIdx (tmRiQ (gens gs) z) = i then
        [.list (Zv.filter (tmRiQ (gens gs) z))] else [])) := by
    by_cases hf : Zv.findIdx (tmRiQ (gens gs) z) = i <;> simp [BinOp.eval, hf]
  rw [hval] at dall
  refine FunDet.intro hP.pcsStep (dall.mono ?_)
  have hout : (Val.list (acc ++ (if Zv.findIdx (tmRiQ (gens gs) z) = i then
      [.list (Zv.filter (tmRiQ (gens gs) z))] else []))).wt ≤
      (Val.list acc).wt + 2 * (Val.list Zv).wt + 2 := by
    split_ifs
    · have := wt_list_snoc_le acc (.list (Zv.filter (tmRiQ (gens gs) z))); omega
    · simp only [List.append_nil]; omega
  have hb1 : BinOp.eval .eq (Zv.findIdx (tmRiQ (gens gs) z)) i ≤ 1 := by
    simp only [BinOp.eval]; split <;> omega
  have hfi : (Val.nat (Zv.findIdx (tmRiQ (gens gs) z))).wt ≤ E + 2 := by
    have := wt_nat_le (Zv.findIdx (tmRiQ (gens gs) z))
    have := List.findIdx_le_length (p := tmRiQ (gens gs) z) (xs := Zv)
    omega
  have hsnw := wt_list_snoc_le acc (.list (Zv.filter (tmRiQ (gens gs) z)))
  unfold tmRiPcsStepC
  have hOP2 : 2 * E * (tmRiObjPC (solvableCosetIntersectionPrim hsci) n C) =
      2 * (E * (tmRiObjPC (solvableCosetIntersectionPrim hsci) n C)) := by ring
  have hctx' : (Val.list [encGroup gs, z]).wt = ctx.wt := rfl
  omega

theorem tmRi_wt_list_le (vs : List Val) {c : ℕ} (h : ∀ v ∈ vs, v.wt ≤ c) :
    (Val.list vs).wt ≤ vs.length * (2 * c + 1) + 4 := by
  have h1 := wt_list_le vs
  have h2 := List.sum_le_card_nsmul (vs.map Val.wt) c (by
    simp only [List.mem_map, forall_exists_index, and_imp]
    rintro _ v hv rfl; exact h v hv)
  simp only [List.length_map, smul_eq_mul] at h2
  have : vs.length * (2 * c + 1) = 2 * (vs.length * c) + vs.length := by ring
  omega

theorem tmRiPcs_length_le {α : Type} (q : α → α → Bool) (L : List α) (d : α) (i : ℕ) :
    (tmRiPcs q L d i).length ≤ i := by
  unfold tmRiPcs
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

theorem tmRiPcs_sub {α : Type} (q : α → α → Bool) (L : List α) (d : α) (i : ℕ) :
    ∀ S ∈ tmRiPcs q L d i, S.Sublist L := by
  intro S hS
  unfold tmRiPcs at hS
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hS
  exact List.filter_sublist

/-- The weight of a partial list of pieces. -/
theorem tmRi_wt_pcs {q : Val → Val → Bool} {Zv : List Val} {i E : ℕ} (hi : i ≤ E)
    (hZ : (Val.list Zv).wt ≤ E) :
    (Val.list ((tmRiPcs q Zv (.nat 0) i).map Val.list)).wt ≤ 4 * (E + 1) ^ 2 := by
  have h1 := tmRi_wt_list_le ((tmRiPcs q Zv (.nat 0) i).map Val.list) (c := E) (by
    intro v hv
    obtain ⟨S, hS, rfl⟩ := List.mem_map.1 hv
    exact (wt_list_sublist (tmRiPcs_sub q Zv _ i S hS)).trans hZ)
  have h2 := tmRiPcs_length_le q Zv (.nat 0) i
  rw [List.length_map] at h1
  have h3 : (tmRiPcs q Zv (.nat 0) i).length * (2 * E + 1) ≤ E * (2 * E + 1) :=
    Nat.mul_le_mul_right _ (h2.trans hi)
  nlinarith

/-- The cost bound of the pieces. -/
def tmRiPcsC (OP E : ℕ) : ℕ := E * tmRiPcsStepC OP E + 10 ^ 5 * (E + 1) ^ 3

/-- **The pieces of a list of objects.** -/
theorem tmRi_pcs_spec {P : Program} {b jsci jder jmem gObj : ℕ}
    {hsci : SolvableCosetIntersection} {hder : DerivedSubgroup} {hmem : Membership}
    (hP : TmRiAt P b jsci jder jmem gObj hsci hder hmem) {gs : List (Perm (Fin n))}
    (hsol : IsSolvable (gens gs)) (hgl : gs.length ≤ n ^ 2) {C : ℕ} {L : List (TmRiO n)}
    (hok : TmRiOK C L) {E : ℕ}
    (hE : (Val.list [encGroup gs, .list (L.map tmGlObjVal)]).wt ≤ E) :
    FunDet P (b + 6) (.list [encGroup gs, .list (L.map tmGlObjVal)])
      (.list ((tmRiPcs (tmRiQ (gens gs)) (L.map tmGlObjVal) (.nat 0) L.length).map Val.list))
      (tmRiPcsC (tmRiObjPC (solvableCosetIntersectionPrim hsci) n C) E) := by
  set Zv := L.map tmGlObjVal with hZv
  set c : Val := .list [encGroup gs, .list Zv] with hc
  have hZw : (Val.list Zv).wt < c.wt := wt_le_wt_list (by simp)
  have hlen : Zv.length < (Val.list Zv).wt := length_lt_wt_list Zv
  have hLZ : Zv.length = L.length := by simp [hZv]
  have hit := iter_spec hP.iterPcs (c := c) (k := Zv.length) (acc0 := .list [])
    (Inv := fun i acc => acc = .list ((tmRiPcs (tmRiQ (gens gs)) Zv (.nat 0) i).map Val.list))
    (M := 4 * (E + 1) ^ 2) (B := fun _ => tmRiPcsStepC (tmRiObjPC (solvableCosetIntersectionPrim hsci) n C) E)
    rfl (fun i acc hi h => by
      rw [h]; exact tmRi_wt_pcs (q := tmRiQ (gens gs)) (Zv := Zv) (i := i) (by omega) (by omega))
    (fun i acc hi h => by
      rw [h]
      have := tmRi_pcsStep_spec hP hsol hgl hok (i := i) (by omega) (E := E)
        (acc := (tmRiPcs (tmRiQ (gens gs)) Zv (.nat 0) i).map Val.list) hE
        (tmRi_wt_pcs (q := tmRiQ (gens gs)) (Zv := Zv) (i := i) (by omega) (by omega))
      refine FunAll.mono this fun w cost hw => ⟨?_, hw.2⟩
      show w = _
      rw [hw.1, tmRiPcs_succ, List.map_append, ← hZv]
      split_ifs <;> simp)
  set vs : List Val := [c] with hvs
  have d0 := Det.var' (P := P) (env := [c]) (i := 0) (v := c) rfl
  have dl := Det.length (Det.arg' (P := P) (vs := [encGroup gs, .list Zv]) (rest := [])
    (j := 1) rfl)
  have hargs := Det.mk3 d0 dl (Det.nil (P := P) (env := [c]))
  have dcall := Det.call hargs (hit.mono fun w cost h => ⟨h.1, h.2⟩)
  rw [hLZ] at dcall
  refine FunDet.intro hP.pcs (dcall.mono ?_)
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hk : L.length ≤ E := by omega
  have hw3 : (Val.list [c, .nat L.length, .list []]).wt ≤
      2 * (c.wt + (Val.nat L.length).wt + (Val.list []).wt) + 7 := wt_list3_le _ _ _
  have hkw := wt_nat_le L.length
  have hnil : (Val.list []).wt ≤ 5 := by decide
  have hE2 : E + 1 ≤ (E + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hloop : loopModK * (L.length + 1) * ((Val.list [c, .nat L.length, .list []]).wt +
      L.length + 4 * (E + 1) ^ 2 + 1) ≤ 30000 * (E + 1) ^ 3 := by
    rw [mul_assoc]
    calc _ ≤ loopModK * (30 * (E + 1) ^ 3) := by
          refine Nat.mul_le_mul_left _ ?_
          calc _ ≤ (E + 1) * (30 * (E + 1) ^ 2) := Nat.mul_le_mul (by omega) (by omega)
            _ = 30 * (E + 1) ^ 3 := by ring
      _ = 30000 * (E + 1) ^ 3 := by simp only [loopModK]; ring
  have hstep : L.length * tmRiPcsStepC (tmRiObjPC (solvableCosetIntersectionPrim hsci) n C) E ≤
      E * tmRiPcsStepC (tmRiObjPC (solvableCosetIntersectionPrim hsci) n C) E :=
    Nat.mul_le_mul_right _ hk
  have hout := tmRi_wt_pcs (q := tmRiQ (gens gs)) (Zv := Zv) (i := L.length) hk (by omega)
  have hct : (Val.list [encGroup gs, .list Zv]).wt = c.wt := rfl
  have h1 : (Val.list [c]).wt ≤ 2 * c.wt + 5 := wt_list1_le c
  have hlist3 := wt_list3_le c (.nat L.length) (.list [])
  have hE3 : (E + 1) ^ 2 ≤ (E + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  unfold tmRiPcsC
  omega


end GI.Impl
