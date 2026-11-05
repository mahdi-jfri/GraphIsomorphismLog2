module

public import Workspace.Impl.GMPConjRows

@[expose] public section

/-! # Conjugation tables for a list of generators -/

namespace GI.Impl

open GI.Lang GI.Cited Equiv

/-- Adapt `[[gv, reps], h]` to the row-map input. -/
def gmpConjTableStepF (row : ℕ) : Expr :=
  .call row (mk2 (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (arg 1))
    (.get (arg 0) (.nat 1)))

def gmpConjTableFuns (b jm : ℕ) : List Expr :=
  mapFuns b (b + 3) ++ [gmpConjTableStepF (b + 4)] ++ gmpConjRowsFuns (b + 4) jm

structure GmpConjTableAt (P : Program) (hm : Membership) (b jm : ℕ) : Prop where
  mp : P.HasAt b (mapFuns b (b + 3))
  st : P.funs[b + 3]? = some (gmpConjTableStepF (b + 4))
  rows : GmpConjRowsAt P hm (b + 4) jm

theorem gmpConjTableAt_of {P : Program} {hm : Membership} {b jm : ℕ}
    (h : P.HasAt b (gmpConjTableFuns b jm))
    (hj : P.prims[jm]? = some (membershipPrim hm)) : GmpConjTableAt P hm b jm :=
  ⟨h.block 0 rfl, (h.block 3 (gs := [gmpConjTableStepF (b + 4)]) rfl).single,
    gmpConjRowsAt_of (h.block 4 rfl) hj⟩

noncomputable def gmpConjTableStepCost (hm : Membership) (Y L : ℕ) : ℕ :=
  gmpConjRowCost hm (100 * Y) L + 10 ^ 6 * (Y + (L + 1) ^ 2)

noncomputable def gmpConjTableCost (hm : Membership) (Y L S : ℕ) : ℕ :=
  S * gmpConjTableStepCost hm Y L +
    mapK * (S + 1) * (Y + 20 * ((S + 1) * ((L + 1) ^ 2)) + 10)

theorem gmpConjTableStep_spec {P : Program} {hm : Membership} {b jm n : ℕ}
    (hp : GmpConjTableAt P hm b jm) {gv : Val} {V : Subgroup (Perm (Fin n))}
    (hV : GroupVal n gv V) (rs : List (Perm (Fin n))) (h : Perm (Fin n))
    {Y : ℕ} (hY : (n + 1) ^ 4 ≤ Y)
    (hin : (Val.list [.list [gv, .list (rs.map encPerm)], encPerm h]).wt ≤ Y) :
    FunDet P (b + 3) (.list [.list [gv, .list (rs.map encPerm)], encPerm h])
      (natList (rs.map fun r => gmpCosetIndex V rs (h * r * h⁻¹)))
      (gmpConjTableStepCost hm Y rs.length) := by
  let ctx := Val.list [gv, .list (rs.map encPerm)]
  have hc : ctx.wt ≤ Y := (wt_le_wt_list (by simp) : ctx.wt <
    (Val.list [ctx, encPerm h]).wt).le.trans hin
  have hv : gv.wt ≤ Y := (wt_le_wt_list (by simp) : gv.wt < ctx.wt).le.trans hc
  have hr : (Val.list (rs.map encPerm)).wt ≤ Y :=
    (wt_le_wt_list (by simp) : (Val.list (rs.map encPerm)).wt < ctx.wt).le.trans hc
  have hh : (encPerm h).wt ≤ Y := (wt_le_wt_list (by simp) : (encPerm h).wt <
    (Val.list [ctx, encPerm h]).wt).le.trans hin
  have hY1 : 1 ≤ Y := (Nat.one_le_pow 4 (n + 1) (by omega)).trans hY
  have hw3 := wt_list3_le gv (.list (rs.map encPerm)) (encPerm h)
  have hctx : (Val.list [gv, .list (rs.map encPerm), encPerm h]).wt ≤ 100 * Y := by omega
  have row := gmpConjRow_spec hp.rows hV rs h
    (hY.trans (Nat.le_mul_of_pos_left _ (by decide))) hctx
  have d0 := Det.arg' (P := P) (vs := [ctx, encPerm h]) (rest := []) (j := 0) rfl
  have d1 := Det.arg' (P := P) (vs := [ctx, encPerm h]) (rest := []) (j := 1) rfl
  have dg := Det.get' d0 (Det.nat 0) rfl
  have dr := Det.get' d0 (Det.nat 1) rfl
  have d := Det.call (Det.mk2 (Det.mk3 dg dr d1) dr) row
  refine FunDet.intro hp.st (d.mono ?_)
  have hout : (natList (rs.map fun r => gmpCosetIndex V rs (h * r * h⁻¹))).wt ≤
      5 * (rs.length + 1) ^ 2 := by
    apply wt_natList_le_sq (B := rs.length)
    · intro x hx
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hx
      exact List.findIdx_le_length.trans (by rw [List.length_map])
    · simp
  have hw2 := wt_list2_le (.list [gv, .list (rs.map encPerm), encPerm h])
    (.list (rs.map encPerm))
  have hn0 := wt_nat_le 0
  have hn1 := wt_nat_le 1
  have heq : (Val.list [gv, .list (rs.map encPerm)]).wt = ctx.wt := rfl
  have heqin : (Val.list [ctx, encPerm h]).wt =
      (Val.list [.list [gv, .list (rs.map encPerm)], encPerm h]).wt := rfl
  unfold gmpConjTableStepCost
  omega

/-- All rows, in the same order as the supplied generators. -/
theorem gmpConjTable_spec {P : Program} {hm : Membership} {b jm n : ℕ}
    (hp : GmpConjTableAt P hm b jm) {gv : Val} {V : Subgroup (Perm (Fin n))}
    (hV : GroupVal n gv V) (rs hs : List (Perm (Fin n)))
    {Y : ℕ} (hY : (n + 1) ^ 4 ≤ Y)
    (hin : (Val.list [.list [gv, .list (rs.map encPerm)], .list (hs.map encPerm)]).wt ≤ Y) :
    FunDet P b (.list [.list [gv, .list (rs.map encPerm)], .list (hs.map encPerm)])
      (.list (hs.map fun h => natList (rs.map fun r => gmpCosetIndex V rs (h * r * h⁻¹))))
      (gmpConjTableCost hm (100 * Y) rs.length hs.length) := by
  let ctx := Val.list [gv, .list (rs.map encPerm)]
  let f := fun h : Perm (Fin n) => natList (rs.map fun r => gmpCosetIndex V rs (h * r * h⁻¹))
  have hc : ctx.wt ≤ Y := (wt_le_wt_list (by simp) : ctx.wt <
    (Val.list [ctx, .list (hs.map encPerm)]).wt).le.trans hin
  have hhs : (Val.list (hs.map encPerm)).wt ≤ Y :=
    (wt_le_wt_list (by simp) : (Val.list (hs.map encPerm)).wt <
      (Val.list [ctx, .list (hs.map encPerm)]).wt).le.trans hin
  have hY1 : 1 ≤ Y := (Nat.one_le_pow 4 (n + 1) (by omega)).trans hY
  have step : ∀ x ∈ hs.map encPerm, FunAll P (b + 3) (.list [ctx, x])
      (fun w c => (∃ h ∈ hs, x = encPerm h ∧ w = f h) ∧
        c ≤ gmpConjTableStepCost hm (100 * Y) rs.length) := by
    intro x hx
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hx
    have hw : (encPerm h).wt ≤ Y :=
      (wt_le_wt_list (List.mem_map.mpr ⟨h, hh, rfl⟩)).le.trans hhs
    have hw2 := wt_list2_le ctx (encPerm h)
    have ha : (Val.list [ctx, encPerm h]).wt ≤ 100 * Y := by omega
    exact FunAll.mono (gmpConjTableStep_spec hp hV rs h
      (hY.trans (Nat.le_mul_of_pos_left _ (by decide))) ha) fun w c hw =>
        ⟨⟨h, hh, rfl, hw.1⟩, hw.2⟩
  refine FunAll.mono (map_spec hp.mp step) fun w c ⟨ws, hw, hws, hcost⟩ => ?_
  subst w
  have he : ws = hs.map f := forall₂_map_eq (fun h hh w ⟨h', _, he, hw⟩ => by
    cases encPerm_injective he; exact hw) hws
  subst ws
  refine ⟨rfl, ?_⟩
  have hout : (Val.list (hs.map f)).wt ≤ 20 * ((hs.length + 1) * ((rs.length + 1) ^ 2)) := by
    have hb : ∀ h, (f h).wt ≤ 5 * (rs.length + 1) ^ 2 := by
      intro h
      apply wt_natList_le_sq (B := rs.length)
      · intro x hx
        obtain ⟨r, _, rfl⟩ := List.mem_map.mp hx
        exact List.findIdx_le_length.trans (by rw [List.length_map])
      · simp
    have hw := wt_list_le (hs.map f)
    have hsum : ((hs.map f).map Val.wt).sum ≤ hs.length * (5 * (rs.length + 1) ^ 2) := by
      simpa only [List.length_map, smul_eq_mul] using
        List.sum_le_card_nsmul ((hs.map f).map Val.wt) (5 * (rs.length + 1) ^ 2) (by
          intro x hx
          obtain ⟨h, _, rfl⟩ := List.mem_map.mp (by simpa only [List.map_map] using hx)
          exact hb h)
    simp only [List.length_map] at hw
    nlinarith [Nat.one_le_pow 2 (rs.length + 1) (by omega)]
  simp only [List.map_const', List.length_map, List.sum_replicate, smul_eq_mul] at hcost
  exact hcost.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _
    (Nat.add_le_add (Nat.add_le_add (hin.trans (by omega)) hout) (by omega))) _)

end GI.Impl
