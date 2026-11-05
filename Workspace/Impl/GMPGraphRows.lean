module

public import Workspace.Impl.GMPSumPerm
public import Workspace.Proved.GMPConjLabels
public import Workspace.Proved.GMPGraphKernel

@[expose] public section

/-! # Computing the graph generators of the conjugation action -/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

def gmpGraphRowF (row sum : ℕ) : Expr :=
  .letE (.call row (.var 0)) (.call sum (mk2 (arg 1) (.var 1)))

def gmpGraphRowsFuns (b jm : ℕ) : List Expr :=
  mapFuns b (b + 3) ++ [gmpGraphRowF (b + 7) (b + 33)] ++
    gmpConjTableFuns (b + 4) jm ++ gmpSumPermFuns (b + 33)

structure GmpGraphRowsAt (P : Program) (hm : Membership) (b jm : ℕ) : Prop where
  mp : P.HasAt b (mapFuns b (b + 3))
  st : P.funs[b + 3]? = some (gmpGraphRowF (b + 7) (b + 33))
  tb : GmpConjTableAt P hm (b + 4) jm
  sum : P.HasAt (b + 33) (gmpSumPermFuns (b + 33))

theorem gmpGraphRowsAt_of {P : Program} {hm : Membership} {b jm : ℕ}
    (h : P.HasAt b (gmpGraphRowsFuns b jm))
    (hj : P.prims[jm]? = some (membershipPrim hm)) : GmpGraphRowsAt P hm b jm :=
  ⟨h.block 0 rfl, (h.block 3 (gs := [gmpGraphRowF (b + 7) (b + 33)]) rfl).single,
    gmpConjTableAt_of (h.block 4 rfl) hj, h.block 33 rfl⟩

noncomputable def gmpGraphRowCost (hm : Membership) (Y L : ℕ) : ℕ :=
  gmpConjTableStepCost hm Y L + 10 ^ 9 * (Y + L + 1) ^ 3

/-- One graph generator consists of the original permutation and the
computed permutation of coset labels. -/
theorem gmpGraphRow_spec {P : Program} {hm : Membership} {b jm n : ℕ}
    (hp : GmpGraphRowsAt P hm b jm)
    {H U V : Subgroup (Perm (Fin n))} {gv : Val} (hgv : GroupVal n gv V)
    {rs : List (Perm (Fin n))} (hrs : GmpCosetReps U V rs)
    (hU : GI.Multicoset.Normalizes H U) (hV : GI.Multicoset.Normalizes H V)
    (h : H) {Y : ℕ} (hY : (n + 1) ^ 4 ≤ Y)
    (hin : (Val.list [.list [gv, .list (rs.map encPerm)], encPerm (h : Perm (Fin n))]).wt ≤ Y) :
    FunDet P (b + 3) (.list [.list [gv, .list (rs.map encPerm)], encPerm (h : Perm (Fin n))])
      (encPerm (sumToFin (sumCongr (h : Perm (Fin n)) (gmpConjLabelAction hrs hU hV h))))
      (gmpGraphRowCost hm Y rs.length) := by
  let p := gmpConjLabelAction hrs hU hV h
  have hrow := gmpConjTableStep_spec hp.tb hgv rs (h : Perm (Fin n)) hY hin
  rw [gmpConjLabelAction_encPerm hrs hU hV h] at hrow
  let a := Val.list [.list [gv, .list (rs.map encPerm)], encPerm (h : Perm (Fin n))]
  have hn1 : n + 1 ≤ Y := (Nat.le_self_pow (by decide) (n + 1)).trans hY
  let X := Y + rs.length + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hn : n + rs.length + 1 ≤ X := by dsimp [X]; omega
  have hsum := (gmpSumPerm_spec hp.sum (h : Perm (Fin n)) p).mono
    (Nat.mul_le_mul_left (10 ^ 7) (Nat.pow_le_pow_left hn 3))
  have d0 := Det.var' (P := P) (env := [a]) (i := 0) rfl
  have dr := Det.call d0 hrow
  have dh := Det.arg' (P := P)
    (vs := [.list [gv, .list (rs.map encPerm)], encPerm (h : Perm (Fin n))])
    (rest := [encPerm p]) (j := 1) rfl
  have dp := Det.var' (P := P) (env := [a, encPerm p]) (i := 1) rfl
  have ds := Det.call (Det.mk2 dh dp) hsum
  refine FunDet.intro hp.st ((Det.letE dr ds).mono ?_)
  have haeq : (Val.list [.list [gv, .list (rs.map encPerm)], encPerm (h : Perm (Fin n))]).wt = a.wt := rfl
  have hw : (encPerm (h : Perm (Fin n))).wt ≤ Y :=
    (wt_le_wt_list (by simp) : (encPerm (h : Perm (Fin n))).wt < a.wt).le.trans hin
  have hpwt : (encPerm p).wt ≤ 4 * X ^ 2 :=
    (wt_encPerm_le p).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [X]; omega) 2))
  have hout : (encPerm (sumToFin (sumCongr (h : Perm (Fin n)) p))).wt ≤ 4 * X ^ 2 :=
    (wt_encPerm_le _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn 2))
  have hmk := wt_list2_le (encPerm (h : Perm (Fin n))) (encPerm p)
  have hxx : X ≤ X ^ 2 := Nat.le_self_pow (by decide) X
  have hxxx : X ^ 2 ≤ X ^ 3 := Nat.pow_le_pow_right hX (by decide)
  have hyx : Y ≤ X := by dsimp [X]; omega
  have heqp : (encPerm (gmpConjLabelAction hrs hU hV h)).wt = (encPerm p).wt := rfl
  unfold gmpGraphRowCost
  change _ ≤ gmpConjTableStepCost hm Y rs.length + 10 ^ 9 * X ^ 3
  omega

theorem gmpGraphRowCost_poly (hm : Membership) : PBU (fun L Y _ => gmpGraphRowCost hm Y L) :=
  (gmpConjTableStepCost_poly hm).add ((((PBU.W.add PBU.k).addc 1).pow 3).smul (10 ^ 9))

noncomputable def gmpGraphRowsCost (hm : Membership) (Y L S : ℕ) : ℕ :=
  S * gmpGraphRowCost hm (100 * Y) L +
    mapK * (S + 1) * (Y + 20 * ((S + 1) * (Y + L + 1) ^ 2) + 10)

/-- The graph table, ready to encode the group for the preimage call. -/
theorem gmpGraphRows_spec {P : Program} {hm : Membership} {b jm n : ℕ}
    (hp : GmpGraphRowsAt P hm b jm)
    {H U V : Subgroup (Perm (Fin n))} {gv : Val} (hgv : GroupVal n gv V)
    {rs : List (Perm (Fin n))} (hrs : GmpCosetReps U V rs)
    (hU : GI.Multicoset.Normalizes H U) (hV : GI.Multicoset.Normalizes H V)
    (hs : List (Perm (Fin n))) (hhs : ∀ h ∈ hs, h ∈ H)
    {Y : ℕ} (hY : (n + 1) ^ 4 ≤ Y)
    (hin : (Val.list [.list [gv, .list (rs.map encPerm)], .list (hs.map encPerm)]).wt ≤ Y) :
    FunDet P b (.list [.list [gv, .list (rs.map encPerm)], .list (hs.map encPerm)])
      (.list ((hs.map fun h => sumToFin (gmpGraphPerm H (gmpConjLabelAction hrs hU hV) h)).map encPerm))
      (gmpGraphRowsCost hm Y rs.length hs.length) := by
  let ctx := Val.list [gv, .list (rs.map encPerm)]
  let f := fun h : Perm (Fin n) => encPerm (sumToFin (gmpGraphPerm H (gmpConjLabelAction hrs hU hV) h))
  have hc : ctx.wt ≤ Y := (wt_le_wt_list (by simp) : ctx.wt <
    (Val.list [ctx, .list (hs.map encPerm)]).wt).le.trans hin
  have hhswt : (Val.list (hs.map encPerm)).wt ≤ Y :=
    (wt_le_wt_list (by simp) : (Val.list (hs.map encPerm)).wt <
      (Val.list [ctx, .list (hs.map encPerm)]).wt).le.trans hin
  have hY1 : 1 ≤ Y := (Nat.one_le_pow 4 (n + 1) (by omega)).trans hY
  have hn1 : n + 1 ≤ Y := (Nat.le_self_pow (by decide) (n + 1)).trans hY
  have step : ∀ x ∈ hs.map encPerm, FunAll P (b + 3) (.list [ctx, x])
      (fun w c => (∃ h ∈ hs, x = encPerm h ∧ w = f h) ∧
        c ≤ gmpGraphRowCost hm (100 * Y) rs.length) := by
    intro x hx
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hx
    have hw : (encPerm h).wt ≤ Y :=
      (wt_le_wt_list (List.mem_map.mpr ⟨h, hh, rfl⟩)).le.trans hhswt
    have hw2 := wt_list2_le ctx (encPerm h)
    have ha : (Val.list [ctx, encPerm h]).wt ≤ 100 * Y := by omega
    have hg := gmpGraphRow_spec hp hgv hrs hU hV ⟨h, hhs h hh⟩
      (hY.trans (Nat.le_mul_of_pos_left _ (by decide))) ha
    exact FunAll.mono hg fun w c hw => ⟨⟨h, hh, rfl, hw.1.trans (by
      dsimp only [f]; rw [gmpGraphPerm_of_mem H _ (hhs h hh)])⟩, hw.2⟩
  refine FunAll.mono (map_spec hp.mp step) fun w c ⟨ws, hw, hws, hcost⟩ => ?_
  subst w
  have he : ws = hs.map f := forall₂_map_eq (fun h hh w ⟨h', _, he, hw⟩ => by
    cases encPerm_injective he; exact hw) hws
  subst ws
  refine ⟨by simp only [List.map_map]; rfl, ?_⟩
  have hout : (Val.list (hs.map f)).wt ≤ 20 * ((hs.length + 1) * (Y + rs.length + 1) ^ 2) := by
    have hb : ∀ h, (f h).wt ≤ 4 * (Y + rs.length + 1) ^ 2 := by
      intro h
      exact (wt_encPerm_le _).trans (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left (by omega : n + rs.length + 1 ≤ Y + rs.length + 1) 2))
    have hw := wt_list_le (hs.map f)
    have hsum : ((hs.map f).map Val.wt).sum ≤ hs.length * (4 * (Y + rs.length + 1) ^ 2) := by
      simpa only [List.length_map, smul_eq_mul] using
        List.sum_le_card_nsmul ((hs.map f).map Val.wt) (4 * (Y + rs.length + 1) ^ 2) (by
          intro x hx
          obtain ⟨h, _, rfl⟩ := List.mem_map.mp (by simpa only [List.map_map] using hx)
          exact hb h)
    simp only [List.length_map] at hw
    nlinarith [Nat.one_le_pow 2 (Y + rs.length + 1) (by omega)]
  simp only [List.map_const', List.length_map, List.sum_replicate, smul_eq_mul] at hcost
  exact hcost.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _
    (Nat.add_le_add (Nat.add_le_add hin hout) (by omega))) _)

theorem gmpGraphRowsCost_poly (hm : Membership) : PBU (fun L Y S => gmpGraphRowsCost hm Y L S) :=
  (PBU.B.mul (gmpPBU_comp (gmpGraphRowCost_poly hm) PBU.k (PBU.W.smul 100) (PBU.const 0))).add
    (((PBU.B.addc 1).smul mapK).mul ((PBU.W.add
      (((PBU.B.addc 1).mul (((PBU.W.add PBU.k).addc 1).pow 2)).smul 20)).addc 10))

end GI.Impl
