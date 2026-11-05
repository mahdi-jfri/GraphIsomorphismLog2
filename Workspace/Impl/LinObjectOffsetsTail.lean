module

public import Workspace.Impl.LinObjectOffsetsAnswer
public import Workspace.Impl.GenNormGlue

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset

def linObjectOffsetsTailE (coords flat range : ℕ) : Expr :=
  .letE (.call coords (mk2 (arg 0) (.var 4)))
    (.letE (.call range (.length (arg 2)))
      (.letE (.call range (.arith .sub (.length (.get (arg 0) (.nat 1))) (.nat 1)))
        (.call flat (mk3 (.var 6) (.var 7) (.var 5)))))

noncomputable def linObjectOffsetsTailCost (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (W : ℕ) : ℕ :=
  1000000 * ((W + 1) ^ 2 + W + linObjectOffsetsRowsBudget hs hm W +
    linObjectOffsetsCoordsBudget hs hm hc W + linObjectOffsetsRangeBudget W +
    linObjectOffsetsFlatBudget hs hm hc W + 1)

set_option maxHeartbeats 50000 in
set_option maxRecDepth 200 in
theorem linObjectOffsets_tail_spec {P : Program} {b jsci jder jmem jm n : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership}
    {hc : ConstructiveMembership} (h : linObjectOffsetsAt P b jsci jder jmem jm hs hd hm hc)
    {Q : Type*} [CommGroup Q] (as ns gs : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (refs targets : List (List (TmRiO n))) (Z : Multiset (CObj ℕ (Equiv.Perm (Fin n))))
    (hgs : List.Forall₂ (fun S a => a ∈ gens as ∧
      tmGlMs S ↼ a = partAt (gens as) Z (tmGlMs S)) refs gs)
    (allv tabv rowsv : Val)
    (wgs : (Val.list (gs.map encPerm)).wt ≤ linObjectOffsetsRowsBudget hs hm
      (Val.list [encGroup as, encGroup ns, .list (refs.map tmGlObjsVal), .list (targets.map tmGlObjsVal)]).wt) :
    let input := Val.list [encGroup as, encGroup ns, .list (refs.map tmGlObjsVal), .list (targets.map tmGlObjsVal)]
    EvalAll P [input, allv, tabv, rowsv, .list (gs.map encPerm)]
      (linObjectOffsetsTailE (b + 119) (b + 164) (b + 173)) (fun out cost =>
        linObjectOffsetsOut as π refs Z out ∧ cost ≤ linObjectOffsetsTailCost hs hm hc input.wt) := by
  let input := Val.list [encGroup as, encGroup ns, .list (refs.map tmGlObjsVal), .list (targets.map tmGlObjsVal)]
  let W := input.wt
  let gv := Val.list (gs.map encPerm)
  let EB := linObjectOffsetsCoordsBudget hs hm hc W
  let RB := linObjectOffsetsRangeBudget W
  let FB := linObjectOffsetsFlatBudget hs hm hc W
  have wa : (encGroup as).wt < W := wt_le_wt_list (by simp [input, W])
  have wr : (Val.list (refs.map tmGlObjsVal)).wt < W := wt_le_wt_list (by simp [input, W])
  have hp : refs.length ≤ W := by
    have hh := length_lt_wt_list (refs.map tmGlObjsVal)
    simp only [List.length_map] at hh
    omega
  have ht : as.length ≤ W := by
    have hh := length_lt_wt_list ((1 :: as).map encPerm)
    have hw : (Val.list ((1 :: as).map encPerm)).wt < (encGroup as).wt :=
      wt_le_wt_list (by simp [encGroup, encPerms])
    simp only [List.length_map, List.length_cons] at hh
    omega
  have hmem : ∀ a ∈ gs, a ∈ gens as := by
    intro a ha
    obtain ⟨S, _, hS⟩ := linForall₂_mem_right hgs ha
    exact hS.1
  have harg : (Val.list [encGroup as, gv]).wt ≤ linObjectOffsetsCoordsArg hs hm W := by
    have hh := wt_list2_le (encGroup as) gv
    unfold linObjectOffsetsCoordsArg
    dsimp only [gv, input, W] at *
    nlinarith
  have hscoords : FunAll P (b + 119) (.list [encGroup as, gv]) (fun out cost =>
      (∃ M : Matrix (Fin gs.length) (Fin as.length) ℤ, out = encIntMatrix M ∧
        ∀ i : Fin gs.length,
          linCoordHom (fun j : Fin as.length => π (linIntoSubgroup (gens as) (as.get j)))
            (Multiplicative.ofAdd (M i)) = π (linIntoSubgroup (gens as) (gs.get i))) ∧ cost ≤ EB) :=
    (linElementList_spec hc h.coords as gs hmem π).mono fun out cost ho =>
      ⟨ho.1, ho.2.trans (linPolyEnvelope_bound (linElementListCost_poly hc)
        (Nat.zero_le _) harg (Nat.zero_le _))⟩
  have da := Det.arg' (P := P)
    (vs := [encGroup as, encGroup ns, .list (refs.map tmGlObjsVal), .list (targets.map tmGlObjsVal)])
    (rest := [allv, tabv, rowsv, gv]) (j := 0) rfl
  have dg := Det.var' (P := P) (env := [input, allv, tabv, rowsv, gv]) (i := 4) rfl
  apply EvalAll.letE (normBound_call (Det.mk2 da dg) hscoords)
  intro mv ce hmval
  obtain ⟨⟨M, rfl, hM⟩, wm, hce⟩ := hmval
  let C := linMatrixCastRows hgs.length_eq.symm M
  have henc : encIntMatrix C = encIntMatrix M := linMatrixCastRows_encoding _ M
  have hr : FunDet P (b + 173) (.nat refs.length)
      (encFun (fun i : Fin refs.length => i.val)) RB :=
    (linRange_spec h.range refs.length).mono
      (linPolyEnvelope_bound linObjectOffsetsRangePoly hp (Nat.zero_le _) (Nat.zero_le _))
  have hr' : FunDet P (b + 173) (.nat as.length)
      (encFun (fun i : Fin as.length => i.val)) RB :=
    (linRange_spec h.range as.length).mono
      (linPolyEnvelope_bound linObjectOffsetsRangePoly ht (Nat.zero_le _) (Nat.zero_le _))
  have widr := hr.wt_lt.le
  have widc := hr'.wt_lt.le
  have dp := Det.length (Det.arg' (P := P)
    (vs := [encGroup as, encGroup ns, .list (refs.map tmGlObjsVal), .list (targets.map tmGlObjsVal)])
    (rest := [allv, tabv, rowsv, gv, encIntMatrix M]) (j := 2) rfl)
  simp only [List.length_map] at dp
  have dr := Det.call dp hr
  apply EvalAll.letE dr
  intro v cp hv
  obtain ⟨rfl, hcp⟩ := hv
  let ids := encFun (fun i : Fin refs.length => i.val)
  have dA := Det.arg' (P := P)
    (vs := [encGroup as, encGroup ns, .list (refs.map tmGlObjsVal), .list (targets.map tmGlObjsVal)])
    (rest := [allv, tabv, rowsv, gv, encIntMatrix M, ids]) (j := 0) rfl
  have dt := Det.arith' (op := .sub) (Det.length (Det.get' dA (Det.nat 1) rfl)) (Det.nat 1)
    (z := as.length) (by simp)
  have dc := Det.call dt hr'
  apply EvalAll.letE dc
  intro v ct hv
  obtain ⟨rfl, hct⟩ := hv
  let cols := encFun (fun i : Fin as.length => i.val)
  have hflatarg : (linObjectCoordsInput C).wt ≤ linObjectOffsetsFlatArg hs hm hc W := by
    have hh := wt_list3_le ids cols (encIntMatrix M)
    unfold linObjectOffsetsFlatArg
    change (Val.list [ids, cols, encIntMatrix C]).wt ≤ _
    rw [henc]
    dsimp only [ids, cols, RB, EB] at *
    nlinarith
  have hsflat := (linObjectFlattenCoords_spec h.flat C).mono
    (linPolyEnvelope_bound linObjectFlattenCoordsCost_poly (Nat.zero_le _) hflatarg (Nat.zero_le _))
  have ds := Det.call (Det.mk3
    (Det.var' (P := P) (env := [input, allv, tabv, rowsv, gv, encIntMatrix M, ids, cols]) (i := 6) rfl)
    (Det.var' (P := P) (env := [input, allv, tabv, rowsv, gv, encIntMatrix M, ids, cols]) (i := 7) rfl)
    (Det.var' (P := P) (env := [input, allv, tabv, rowsv, gv, encIntMatrix M, ids, cols]) (i := 5) rfl))
    (by simpa only [linObjectCoordsInput, henc] using hsflat)
  refine ds.post fun cost hcost => ⟨linObjectOffsetsOut_of_rows as gs π refs Z hgs M hM, ?_⟩
  have wo := hsflat.wt_lt.le
  have wca := wt_list2_le (encGroup as) gv
  have wfa := wt_list3_le ids cols (encIntMatrix M)
  have hn := wt_nat_le as.length
  have wraw : (Val.list ((1 :: as).map encPerm)).wt < (encGroup as).wt :=
    wt_le_wt_list (by simp [encGroup, encPerms])
  have h1 : (Val.nat 1).wt = 3 := rfl
  change _ ≤ linObjectOffsetsTailCost hs hm hc W
  unfold linObjectOffsetsTailCost
  dsimp only [input, W, gv, EB, RB, FB, C, ids, cols, encGroup, encPerms, linObjectOffsetsFlatBudget] at *
  simp only [List.length_map, List.length_cons] at *
  omega

end GI.Impl
