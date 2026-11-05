module

public import Workspace.Impl.GMPConjIndex

@[expose] public section

/-! # Building a conjugation-action row on the enumerated cosets -/

namespace GI.Impl

open GI.Lang GI.Cited Equiv

/-- Adapt a map step `[[gv, reps, h], r]` to the four-argument label function. -/
def gmpConjRowStepF (cf : ℕ) : Expr :=
  .call cf (mk4 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))
    (.get (arg 0) (.nat 2)) (arg 1))

def gmpConjRowsFuns (b jm : ℕ) : List Expr :=
  mapFuns b (b + 3) ++ [gmpConjRowStepF (b + 4), gmpConjIndexF (b + 5) (b + 9) (b + 13)] ++
    findFuns (b + 5) (b + 8) ++ [tmRpPredF jm (b + 9) (b + 13)] ++
      composeFuns (b + 9) ++ invFuns (b + 13)

structure GmpConjRowsAt (P : Program) (hm : Membership) (b jm : ℕ) : Prop where
  mp : P.HasAt b (mapFuns b (b + 3))
  st : P.funs[b + 3]? = some (gmpConjRowStepF (b + 4))
  conj : P.funs[b + 4]? = some (gmpConjIndexF (b + 5) (b + 9) (b + 13))
  fd : P.HasAt (b + 5) (findFuns (b + 5) (b + 8))
  pred : P.funs[b + 8]? = some (tmRpPredF jm (b + 9) (b + 13))
  mem : P.prims[jm]? = some (membershipPrim hm)
  comp : P.HasAt (b + 9) (composeFuns (b + 9))
  inv : P.HasAt (b + 13) (invFuns (b + 13))

theorem gmpConjRowsAt_of {P : Program} {hm : Membership} {b jm : ℕ}
    (h : P.HasAt b (gmpConjRowsFuns b jm))
    (hjm : P.prims[jm]? = some (membershipPrim hm)) : GmpConjRowsAt P hm b jm :=
  ⟨h.block 0 rfl, (h.block 3 (gs := [gmpConjRowStepF (b + 4)]) rfl).single,
    (h.block 4 (gs := [gmpConjIndexF (b + 5) (b + 9) (b + 13)]) rfl).single,
    h.block 5 rfl, (h.block 8 (gs := [tmRpPredF jm (b + 9) (b + 13)]) rfl).single,
    hjm, h.block 9 rfl, h.block 13 rfl⟩

noncomputable def gmpConjRowStepCost (hm : Membership) (Y L : ℕ) : ℕ :=
  gmpConjIndexCost hm (100 * Y) L + 100000 * Y

noncomputable def gmpConjRowCost (hm : Membership) (Y L : ℕ) : ℕ :=
  L * gmpConjRowStepCost hm Y L +
    mapK * (L + 1) * (10 * Y + 5 * (L + 1) ^ 2 + 10)

theorem gmpConjRowStep_spec {P : Program} {hm : Membership} {b jm n : ℕ}
    (hp : GmpConjRowsAt P hm b jm) {gv : Val} {V : Subgroup (Perm (Fin n))}
    (hV : GroupVal n gv V) (rs : List (Perm (Fin n))) (h r : Perm (Fin n))
    (hr : r ∈ rs) {Y : ℕ} (hY : (n + 1) ^ 4 ≤ Y)
    (hctx : (Val.list [gv, .list (rs.map encPerm), encPerm h]).wt ≤ Y) :
    FunDet P (b + 3) (.list [.list [gv, .list (rs.map encPerm), encPerm h], encPerm r])
      (.nat (gmpCosetIndex V rs (h * r * h⁻¹))) (gmpConjRowStepCost hm Y rs.length) := by
  let ctx := Val.list [gv, .list (rs.map encPerm), encPerm h]
  let a := Val.list [ctx, encPerm r]
  have hY1 : 1 ≤ Y := (Nat.one_le_pow 4 (n + 1) (by omega)).trans hY
  have hv : gv.wt ≤ Y := (wt_le_wt_list (by simp) : gv.wt < ctx.wt).le.trans hctx
  have hrs : (Val.list (rs.map encPerm)).wt ≤ Y :=
    (wt_le_wt_list (by simp) : (Val.list (rs.map encPerm)).wt < ctx.wt).le.trans hctx
  have hh : (encPerm h).wt ≤ Y :=
    (wt_le_wt_list (by simp) : (encPerm h).wt < ctx.wt).le.trans hctx
  have hrw : (encPerm r).wt ≤ Y :=
    (wt_le_wt_list (List.mem_map.mpr ⟨r, hr, rfl⟩)).le.trans hrs
  have hw4 := wt_list4_le gv (.list (rs.map encPerm)) (encPerm h) (encPerm r)
  have hin : (Val.list [gv, .list (rs.map encPerm), encPerm h, encPerm r]).wt ≤ 100 * Y := by omega
  have hc := gmpConjIndex_spec hm hp.conj hp.fd hp.pred hp.mem hp.comp hp.inv hV rs h r
    (hY.trans (Nat.le_mul_of_pos_left _ (by decide))) hin
  have d0 := Det.arg' (P := P) (vs := [ctx, encPerm r]) (rest := []) (j := 0) rfl
  have d1 := Det.arg' (P := P) (vs := [ctx, encPerm r]) (rest := []) (j := 1) rfl
  have dg := Det.get' d0 (Det.nat 0) rfl
  have drs := Det.get' d0 (Det.nat 1) rfl
  have dh := Det.get' d0 (Det.nat 2) rfl
  have d := Det.call (Det.mk4 dg drs dh d1) hc
  refine FunDet.intro hp.st (d.mono ?_)
  have ha := wt_list2_le ctx (encPerm r)
  have hw3 := wt_list3_le gv (.list (rs.map encPerm)) (encPerm h)
  have hw12 := wt_list2_le gv (.list (rs.map encPerm))
  have hn0 := wt_nat_le 0
  have hn1 := wt_nat_le 1
  have hn2 := wt_nat_le 2
  have hl : rs.length ≤ Y := by
    have := length_lt_wt_list (rs.map encPerm)
    simp only [List.length_map] at this
    omega
  have hi : gmpCosetIndex V rs (h * r * h⁻¹) ≤ rs.length :=
    List.findIdx_le_length.trans (by rw [List.length_map])
  have hn := (wt_nat_le (gmpCosetIndex V rs (h * r * h⁻¹))).trans
    (show gmpCosetIndex V rs (h * r * h⁻¹) + 2 ≤ Y + 2 by omega)
  have hctxeq : (Val.list [gv, .list (rs.map encPerm), encPerm h]).wt = ctx.wt := rfl
  unfold gmpConjRowStepCost
  omega

/-- A complete table row, in the order of the coset representatives. -/
theorem gmpConjRow_spec {P : Program} {hm : Membership} {b jm n : ℕ}
    (hp : GmpConjRowsAt P hm b jm) {gv : Val} {V : Subgroup (Perm (Fin n))}
    (hV : GroupVal n gv V) (rs : List (Perm (Fin n))) (h : Perm (Fin n))
    {Y : ℕ} (hY : (n + 1) ^ 4 ≤ Y)
    (hctx : (Val.list [gv, .list (rs.map encPerm), encPerm h]).wt ≤ Y) :
    FunDet P b (.list [.list [gv, .list (rs.map encPerm), encPerm h], .list (rs.map encPerm)])
      (natList (rs.map fun r => gmpCosetIndex V rs (h * r * h⁻¹)))
      (gmpConjRowCost hm Y rs.length) := by
  let f := fun r : Perm (Fin n) => Val.nat (gmpCosetIndex V rs (h * r * h⁻¹))
  have hstep : ∀ x ∈ rs.map encPerm, FunAll P (b + 3)
      (.list [.list [gv, .list (rs.map encPerm), encPerm h], x])
      (fun w cost => (∃ r ∈ rs, x = encPerm r ∧ w = f r) ∧
        cost ≤ gmpConjRowStepCost hm Y rs.length) := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    exact FunAll.mono (gmpConjRowStep_spec hp hV rs h r hr hY hctx) fun w c hw =>
      ⟨⟨r, hr, rfl, hw.1⟩, hw.2⟩
  have hm := map_spec hp.mp hstep
  have hlist : ∀ ws, List.Forall₂ (fun x w => ∃ r ∈ rs, x = encPerm r ∧ w = f r)
      (rs.map encPerm) ws → ws = rs.map f := by
    intro ws hws
    exact forall₂_map_eq (fun r hr w ⟨r', hr', he, hw⟩ =>
      by cases encPerm_injective he; exact hw) hws
  refine FunAll.mono hm fun w c ⟨ws, hw, hws, hcost⟩ => ?_
  subst w
  have hws' := hlist ws hws
  subst ws
  have he : Val.list (rs.map f) = natList (rs.map fun r => gmpCosetIndex V rs (h * r * h⁻¹)) := by
    simp only [f, natList, List.map_map, Function.comp_def]
  refine ⟨he, ?_⟩
  have hout : (Val.list (rs.map f)).wt ≤ 5 * (rs.length + 1) ^ 2 := by
    rw [he]
    apply wt_natList_le_sq
    · intro x hx
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
      exact List.findIdx_le_length.trans (by rw [List.length_map])
    · simp only [List.length_map]; exact le_rfl
  have hrs : (Val.list (rs.map encPerm)).wt ≤ Y :=
    (wt_le_wt_list (by simp) : (Val.list (rs.map encPerm)).wt <
      (Val.list [gv, .list (rs.map encPerm), encPerm h]).wt).le.trans hctx
  have harg := wt_list2_le (.list [gv, .list (rs.map encPerm), encPerm h])
    (.list (rs.map encPerm))
  have hY1 : 1 ≤ Y := (Nat.one_le_pow 4 (n + 1) (by omega)).trans hY
  have harg' : (Val.list [.list [gv, .list (rs.map encPerm), encPerm h], .list (rs.map encPerm)]).wt ≤
      10 * Y := by omega
  simp only [List.map_const', List.length_map, List.sum_replicate, smul_eq_mul] at hcost
  exact hcost.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.add_le_add harg' hout) (by omega))) _)

theorem gmpConjRowCost_poly (hm : Membership) : PBU (fun L Y _ => gmpConjRowCost hm Y L) := by
  have hp : PBU (fun L Y _ => gmpIndexCost hm (100 * Y) L) := by
    have hY := PBU.W.smul 100
    have hpred : PBU (fun _ Y _ => tmRpPredC hm (100 * Y)) :=
      (hY.smul (10 ^ 6)).add
        ((((hY.smul 20).addc 2).pow (membershipPrim hm).k).smul (membershipPrim hm).c)
    exact (PBU.k.mul hpred).add ((((PBU.k.addc 1).pow 2).smul (10 ^ 6)).mul (hY.addc 1))
  have hs : PBU (fun L Y _ => gmpConjRowStepCost hm Y L) := by
    convert (hp.add (PBU.W.smul (10 ^ 9))).add (PBU.W.smul 100000) using 1
    funext L Y B
    unfold gmpConjRowStepCost gmpConjIndexCost
    ring
  exact (PBU.k.mul hs).add
    (((PBU.k.addc 1).smul mapK).mul (((PBU.W.smul 10).add (((PBU.k.addc 1).pow 2).smul 5)).addc 10))

end GI.Impl
