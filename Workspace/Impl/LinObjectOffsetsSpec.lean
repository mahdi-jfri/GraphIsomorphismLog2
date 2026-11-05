module

public import Workspace.Impl.LinObjectOffsetsTail

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset

set_option maxHeartbeats 300000 in
set_option maxRecDepth 500 in
theorem linObjectOffsets_spec {P : Program} {b jsci jder jmem jm n M : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership}
    {hc : ConstructiveMembership} (h : linObjectOffsetsAt P b jsci jder jmem jm hs hd hm hc)
    {Q : Type*} [CommGroup Q] (as ns : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (Y Z : Multiset (CObj ℕ (Equiv.Perm (Fin n)))) (hZ : Conf (gens as) Y Z)
    (refs targets : List (List (TmRiO n)))
    (hsol : TmRiListNorm (gens as) (refs ++ targets).flatten) (hNA : gens ns ≤ gens as)
    (hNn : GI.Multicoset.Normalizes (gens as) (gens ns))
    (hcomm : ∀ a ∈ gens as, ∀ b ∈ gens as, a * b * a⁻¹ * b⁻¹ ∈ gens ns)
    (hal : as.length ≤ n ^ 2) (hPs : ∀ S ∈ refs ++ targets, TmRiPc as ns M S)
    (hlen : (refs ++ targets).length ≤ M) (hok : TmRecObjOK M (refs ++ targets).flatten)
    (hRef : ∀ S ∈ refs, tmGlMs S ∈ pieces (gens as) Y)
    (hTar : ∀ T ∈ targets, tmGlMs T ∈ pieces (gens as) Z)
    (hCover : ∀ T ∈ pieces (gens as) Z, ∃ Tl ∈ targets, tmGlMs Tl = T)
    (hMsize : M ≤ (Val.list [encGroup as, encGroup ns, .list (refs.map tmGlObjsVal),
      .list (targets.map tmGlObjsVal)]).wt) :
    let input := Val.list [encGroup as, encGroup ns, .list (refs.map tmGlObjsVal), .list (targets.map tmGlObjsVal)]
    FunAll P b input (fun out cost => linObjectOffsetsOut as π refs Z out ∧
      cost ≤ linObjectOffsetsCost hs hm hc input.wt) := by
  let input := Val.list [encGroup as, encGroup ns, .list (refs.map tmGlObjsVal), .list (targets.map tmGlObjsVal)]
  let W := input.wt
  let all := refs ++ targets
  let AB := linObjectOffsetsAppendBudget W
  let TB := linObjectOffsetsTableBudget hs hm W
  let SB := linObjectOffsetsSliceBudget hs hm W
  let RB := linObjectOffsetsRowsBudget hs hm W
  have wa : (encGroup as).wt < W := wt_le_wt_list (by simp [input, W])
  have wn : (encGroup ns).wt < W := wt_le_wt_list (by simp [input, W])
  have wr : (Val.list (refs.map tmGlObjsVal)).wt < W := wt_le_wt_list (by simp [input, W])
  have wt : (Val.list (targets.map tmGlObjsVal)).wt < W := wt_le_wt_list (by simp [input, W])
  have hn : n ≤ W := by
    have hh := S_le_wt_encGroup as
    nlinarith
  have hp : refs.length ≤ W := by
    have hh := length_lt_wt_list (refs.map tmGlObjsVal)
    simp only [List.length_map] at hh
    omega
  have hq : targets.length ≤ W := by
    have hh := length_lt_wt_list (targets.map tmGlObjsVal)
    simp only [List.length_map] at hh
    omega
  have hmW : M ≤ W := hMsize
  have habarg : (Val.list [.list (refs.map tmGlObjsVal), .list (targets.map tmGlObjsVal)]).wt ≤
      100 * (W + 1) := by
    have hh := wt_list2_le (.list (refs.map tmGlObjsVal)) (.list (targets.map tmGlObjsVal))
    omega
  have hab : FunDet P (b + 1) (.list [.list (refs.map tmGlObjsVal), .list (targets.map tmGlObjsVal)])
      (.list (all.map tmGlObjsVal)) AB := by
    simpa only [AB, linObjectOffsetsAppendBudget, all, List.map_append] using
      (linAppend_spec h.append (refs.map tmGlObjsVal) (targets.map tmGlObjsVal)).mono
        (linPolyEnvelope_bound linObjectOffsetsAppendPoly (Nat.zero_le _) habarg (Nat.zero_le _))
  have wall : (Val.list (all.map tmGlObjsVal)).wt ≤ AB := hab.wt_lt.le
  have htabarg : (Val.list [encGroup as, encGroup ns, .list (all.map tmGlObjsVal)]).wt ≤
      linObjectOffsetsTableArg W := by
    have hh := wt_list3_le (encGroup as) (encGroup ns) (.list (all.map tmGlObjsVal))
    unfold linObjectOffsetsTableArg
    dsimp only [AB] at *
    nlinarith
  have hWT : W ≤ linObjectOffsetsTableArg W := by unfold linObjectOffsetsTableArg; nlinarith
  have ht : FunAll P (b + 4) (.list [encGroup as, encGroup ns, .list (all.map tmGlObjsVal)])
      (fun out cost => (∃ tab, out = .list tab ∧ TmRiTab (gens as) all tab) ∧ cost ≤ TB) :=
    (linObjectPairTable_spec h.table as ns all hsol hNA hNn hcomm hal hPs hlen hok).mono
      fun out cost ho => ⟨ho.1, ho.2.trans
        (linPolyEnvelope_bound (linObjectPairTableCost_poly hs hm) (hn.trans hWT)
          (hmW.trans hWT) htabarg)⟩
  have darg (k : ℕ) {v : Val}
      (hv : [encGroup as, encGroup ns, .list (refs.map tmGlObjsVal), .list (targets.map tmGlObjsVal)][k]? = some v) :=
    Det.arg' (P := P)
      (vs := [encGroup as, encGroup ns, .list (refs.map tmGlObjsVal), .list (targets.map tmGlObjsVal)])
      (rest := []) (j := k) hv
  have dab := Det.call (Det.mk2 (darg 2 rfl) (darg 3 rfl)) hab
  apply FunAll.intro h.entry
  apply EvalAll.letE dab
  intro allv cab hv
  obtain ⟨rfl, hcab⟩ := hv
  let av := Val.list (all.map tmGlObjsVal)
  have dtA := Det.arg' (P := P)
    (vs := [encGroup as, encGroup ns, .list (refs.map tmGlObjsVal), .list (targets.map tmGlObjsVal)])
    (rest := [av]) (j := 0) rfl
  have dtN := Det.arg' (P := P)
    (vs := [encGroup as, encGroup ns, .list (refs.map tmGlObjsVal), .list (targets.map tmGlObjsVal)])
    (rest := [av]) (j := 1) rfl
  have dtAll := Det.var' (P := P) (env := [input, av]) (i := 1) rfl
  apply EvalAll.letE (normBound_call (Det.mk3 dtA dtN dtAll) ht)
  intro tabv ctab htabv
  obtain ⟨⟨tab, rfl, htab⟩, wtab, hctab⟩ := htabv
  obtain ⟨allrows, heTab, hAllRows⟩ := linObjectPairTable_rows htab
  subst tab
  let tv := Val.list (allrows.map Val.list)
  let selected := allrows.take refs.length
  have hSelected : List.Forall₂ (linObjectTableRow (gens as) all) refs selected := by
    simpa only [all, List.take_left] using linForall₂_take hAllRows refs.length
  have hTablen : refs.length ≤ (allrows.map Val.list).length := by
    have hl := hAllRows.length_eq
    simp only [all, List.length_append, List.length_map] at *
    omega
  have hsliceArg : (Val.list [.nat 0, .nat refs.length, tv]).wt ≤ linObjectOffsetsSliceArg hs hm W := by
    have hh := wt_list3_le (.nat 0) (.nat refs.length) tv
    have hpw := wt_nat_le refs.length
    have hz : (Val.nat 0).wt = 2 := rfl
    unfold linObjectOffsetsSliceArg
    dsimp only [tv, TB] at *
    nlinarith
  have hslice : FunDet P (b + 102) (.list [.nat 0, .nat refs.length, tv])
      (.list (selected.map Val.list)) SB := by
    simpa only [SB, linObjectOffsetsSliceBudget, tv, selected, List.drop_zero, ← List.map_take] using
      (linSlice_spec h.slice (allrows.map Val.list) 0 refs.length (by simpa using hTablen)).mono
        (linPolyEnvelope_bound linSliceCost_poly (Nat.zero_le _) hsliceArg (Nat.zero_le _))
  have wselected : (Val.list (selected.map Val.list)).wt ≤ SB := hslice.wt_lt.le
  have hRowMember : ∀ row ∈ selected, ∃ S ∈ refs, linObjectTableRow (gens as) all S row :=
    fun row hr => linForall₂_mem_right hSelected hr
  have hsafe : ∀ row ∈ selected, refs.length + targets.length ≤ row.length := by
    intro row hr
    obtain ⟨S, _, hsrow⟩ := hRowMember row hr
    have hh := hsrow.length_eq
    simpa only [all, List.length_append] using hh.le
  have hRowsArg : (Val.list [.list [.nat refs.length, .nat targets.length], .list (selected.map Val.list)]).wt ≤
      linObjectOffsetsRowsArg hs hm W := by
    have hcxt := wt_list2_le (.nat refs.length) (.nat targets.length)
    have hh := wt_list2_le (.list [.nat refs.length, .nat targets.length]) (.list (selected.map Val.list))
    have hpw := wt_nat_le refs.length
    have hqw := wt_nat_le targets.length
    unfold linObjectOffsetsRowsArg
    dsimp only [SB] at *
    nlinarith
  have hsrows : FunAll P (b + 105)
      (.list [.list [.nat refs.length, .nat targets.length], .list (selected.map Val.list)])
      (fun out cost => (∃ gs : List (Equiv.Perm (Fin n)), out = .list (gs.map encPerm) ∧
        List.Forall₂ (linObjectOffsetRowRel (gens as) refs targets Z) selected gs) ∧ cost ≤ RB) :=
    (linObjectOffsetRows_spec h.rows selected (linObjectOffsetRowRel (gens as) refs targets Z)
      hsafe (fun row hr => linObjectOffsetRow_shapes (gens as) Y Z refs targets row hRef hTar (hRowMember row hr))
      (fun row hr => by
        obtain ⟨S, hS, hsrow⟩ := hRowMember row hr
        exact linObjectOffsetRow_exists (gens as) Y Z hZ refs targets S row (hRef S hS) hCover hsrow)).mono
      fun out cost ho => ⟨ho.1, ho.2.trans
        (linPolyEnvelope_bound linObjectOffsetRowsCost_poly (Nat.zero_le _) hRowsArg (Nat.zero_le _))⟩
  have drPs := Det.length (Det.arg' (P := P)
    (vs := [encGroup as, encGroup ns, .list (refs.map tmGlObjsVal), .list (targets.map tmGlObjsVal)])
    (rest := [av, tv]) (j := 2) rfl)
  simp only [List.length_map] at drPs
  have ds := Det.call (Det.mk3 (Det.nat 0) drPs
    (Det.var' (P := P) (env := [input, av, tv]) (i := 2) rfl)) hslice
  apply EvalAll.letE ds
  intro v cs hv
  obtain ⟨rfl, hcs⟩ := hv
  let sv := Val.list (selected.map Val.list)
  have drR := Det.length (Det.arg' (P := P)
    (vs := [encGroup as, encGroup ns, .list (refs.map tmGlObjsVal), .list (targets.map tmGlObjsVal)])
    (rest := [av, tv, sv]) (j := 2) rfl)
  have drT := Det.length (Det.arg' (P := P)
    (vs := [encGroup as, encGroup ns, .list (refs.map tmGlObjsVal), .list (targets.map tmGlObjsVal)])
    (rest := [av, tv, sv]) (j := 3) rfl)
  simp only [List.length_map] at drR drT
  have drArg := Det.mk2 (Det.mk2 drR drT)
    (Det.var' (P := P) (env := [input, av, tv, sv]) (i := 3) rfl)
  apply EvalAll.letE (normBound_call drArg hsrows)
  intro gv cr hgv
  obtain ⟨⟨gs, rfl, hgs⟩, wgs, hcr⟩ := hgv
  have hgs' := linObjectOffsetRows_sound hSelected hgs
  refine (linObjectOffsets_tail_spec h as ns gs π refs targets Z hgs' av tv sv wgs).wt_lt.mono
    fun out cost ho => ⟨ho.1.1, ?_⟩
  have htail := ho.1.2
  have wout := ho.2
  have wAB := wt_list2_le (.list (refs.map tmGlObjsVal)) (.list (targets.map tmGlObjsVal))
  have wTab := wt_list3_le (encGroup as) (encGroup ns) av
  have wSlice := wt_list3_le (.nat 0) (.nat refs.length) tv
  have wCtx := wt_list2_le (.nat refs.length) (.nat targets.length)
  have wRows := wt_list2_le (.list [.nat refs.length, .nat targets.length]) sv
  have hpw := wt_nat_le refs.length
  have hqw := wt_nat_le targets.length
  have hz : (Val.nat 0).wt = 2 := rfl
  change _ ≤ linObjectOffsetsCost hs hm hc W
  unfold linObjectOffsetsCost linObjectOffsetsTailCost at *
  dsimp only [input, W, AB, TB, SB, RB, av, tv, sv] at *
  omega

theorem linObjectOffsets_uniform (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) : ∃ K D : ℕ, ∀ W,
      linObjectOffsetsCost hs hm hc W ≤ K * (W + 1) ^ D := by
  obtain ⟨K, D, hKD⟩ := linPoly_source_bound (linObjectOffsetsCost_poly hs hm hc)
  exact ⟨K, D, fun W => hKD 0 W W (Nat.zero_le _) le_rfl⟩

theorem linObjectOffsets_coordinate {n : ℕ} {Q : Type*} [CommGroup Q]
    (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (refs : List (List (TmRiO n))) (Y Z : Multiset (CObj ℕ (Equiv.Perm (Fin n))))
    (hZ : Conf (gens as) Y Z) (hRef : ∀ S ∈ refs, tmGlMs S ∈ pieces (gens as) Y)
    (hker : ∀ T ∈ pieces (gens as) Y, π.ker ≤ (Aut (gens as) T).subgroupOf (gens as))
    {out : Val} (hout : linObjectOffsetsOut as π refs Z out) :
    ∃ w : Fin (as.length * refs.length) → ℤ, out = linVecVal w ∧
      ∀ i : Fin refs.length,
        (linObjectGroupImage (gens as) π (Aut (gens as) (tmGlMs (refs.get i)))).mkQ
          (linObjectLiftCoord as π (linObjectUnflatten refs.length as.length w i)) =
            linObjectConfigCoord (gens as) π Y Z ⟨tmGlMs (refs.get i), hRef _ (List.get_mem _ _)⟩ := by
  obtain ⟨w, rfl, hw⟩ := hout
  refine ⟨w, rfl, ?_⟩
  intro i
  obtain ⟨a, he, hi⟩ := hw i
  rw [hi]
  exact linObjectOffsetRow_coordinate (gens as) π Y Z _ hZ (hRef _ (List.get_mem _ _))
    (hker _ (hRef _ (List.get_mem _ _))) a.val a.property he

end GI.Impl
