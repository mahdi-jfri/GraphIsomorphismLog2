module

public import Workspace.Proved.GMPNormalCentralizer
public import Workspace.Lang.Prims.Blocks
public import Workspace.Lang.Lib.Tabulate

@[expose] public section

/-!
# Representative labeling for equality classes of `N`-point stabilizers

Given a list `ws` of encoded point stabilizers `pointwiseStab N [i]` (`i : Fin n`), each of weight
at most `320 * (n + 1) ^ 6` (`GMPStabList N ws`), `gmpStabReprFuns` computes representative labels
`rv` satisfying `ReprVal n rv (gmpStabRel N)` in time polynomial in `n`.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {n : ℕ}

/-! ### Lists of encoded point stabilizers -/

/-- `ws` is a list of `n` group values encoding `pointwiseStab N [i]` (`i : Fin n`), each of weight
at most `320 * (n + 1) ^ 6`. -/
def GMPStabList (N : Subgroup (Perm (Fin n))) (ws : List Val) : Prop :=
  ∃ f : Fin n → Val, ws = (List.finRange n).map f ∧
    ∀ i : Fin n, GroupVal n (f i) (pointwiseStab N [i]) ∧ (f i).wt ≤ 320 * (n + 1) ^ 6

theorem GMPStabList.length_eq {N : Subgroup (Perm (Fin n))} {ws : List Val}
    (hws : GMPStabList N ws) : ws.length = n := by
  obtain ⟨f, rfl, -⟩ := hws
  simp

theorem GMPStabList.mem_info {N : Subgroup (Perm (Fin n))} {ws : List Val}
    (hws : GMPStabList N ws) {v : Val} (hv : v ∈ ws) :
    ∃ i : Fin n, GroupVal n v (pointwiseStab N [i]) ∧ v.wt ≤ 320 * (n + 1) ^ 6 := by
  obtain ⟨f, rfl, hf⟩ := hws
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hv
  exact ⟨i, (hf i).1, (hf i).2⟩

theorem GMPStabList.wt_le {N : Subgroup (Perm (Fin n))} {ws : List Val}
    (hws : GMPStabList N ws) :
    (Val.list ws).wt ≤ 650 * (n + 1) ^ 7 := by
  have hlen := hws.length_eq
  have h1 := wt_list_le ws
  have h2 : (ws.map Val.wt).sum ≤ ws.length * (320 * (n + 1) ^ 6) := by
    have hcard := List.sum_le_card_nsmul (ws.map Val.wt) (320 * (n + 1) ^ 6) (by
      intro x hx
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
      obtain ⟨_, -, hvw⟩ := hws.mem_info hv
      exact hvw)
    simpa using hcard
  have h3 : ws.length * (320 * (n + 1) ^ 6) ≤ (n + 1) * (320 * (n + 1) ^ 6) :=
    Nat.mul_le_mul_right _ (by omega)
  have h4 : (n + 1) * (320 * (n + 1) ^ 6) = 320 * (n + 1) ^ 7 := by ring
  have h5 : n + 1 ≤ (n + 1) ^ 7 := Nat.le_self_pow (by omega) _
  omega

/-! ### Subgroup equality test -/

/-- On `[gv, hv]`: whether `gv ≤ hv` and `hv ≤ gv`. -/
def gmpEqGroupEntry (le : ℕ) : Expr :=
  .ite (.call le (mk2 (arg 0) (arg 1))) (.call le (mk2 (arg 1) (arg 0))) (.nat 0)

/-- Subgroup equality test, at base `b` (6 functions), with membership at `jm`. -/
def gmpEqGroupFuns (b jm : ℕ) : List Expr :=
  [gmpEqGroupEntry (b + 1)] ++ leFuns (b + 1) jm

@[simp] theorem length_gmpEqGroupFuns (b jm : ℕ) : (gmpEqGroupFuns b jm).length = 6 := rfl

open Classical in
/-- Total boolean predicate testing whether `v` encodes a group equal to `G`. -/
noncomputable def gmpSameGroupTest (G : Subgroup (Perm (Fin n))) (v : Val) : Bool :=
  decide (∃ H : Subgroup (Perm (Fin n)), GroupVal n v H ∧ G = H)

open Classical in
theorem gmpSameGroupTest_of_groupVal {G H : Subgroup (Perm (Fin n))} {hv : Val}
    (hH : GroupVal n hv H) :
    gmpSameGroupTest G hv = decide (G = H) := by
  rw [Bool.eq_iff_iff]
  simp only [gmpSameGroupTest, decide_eq_true_iff]
  exact ⟨fun ⟨H', hH', hGH'⟩ => hGH'.trans (GroupVal.unique hH' hH), fun h => ⟨H, hH, h⟩⟩

/-- Cost bound for `gmpEqGroupFuns` on two group values of weight at most `320 * (n + 1) ^ 6`. -/
noncomputable def gmpEqGroupCost (hm : Membership) (n : ℕ) : ℕ :=
  2600 * ((n + 1) ^ 6 * (membershipPrim hm).boundSize (700 * (n + 1) ^ 6)) +
    10 ^ 14 * (n + 1) ^ 18

open Classical in
theorem gmpEqGroup_spec (hm : Membership) {P : Program} {b jm : ℕ}
    (hb : P.HasAt b (gmpEqGroupFuns b jm))
    (hj : P.prims[jm]? = some (membershipPrim hm))
    {gv hv : Val} {G H : Subgroup (Perm (Fin n))}
    (hG : GroupVal n gv G) (hgw : gv.wt ≤ 320 * (n + 1) ^ 6)
    (hH : GroupVal n hv H) (hhw : hv.wt ≤ 320 * (n + 1) ^ 6) :
    FunDet P b (.list [gv, hv]) (boolVal (gmpSameGroupTest G hv)) (gmpEqGroupCost hm n) := by
  simp only [gmpEqGroupFuns] at hb
  have hentry : P.funs[b]? = some (gmpEqGroupEntry (b + 1)) := hb.left.single
  have hle : P.HasAt (b + 1) (leFuns (b + 1) jm) := hb.right
  rw [gmpSameGroupTest_of_groupVal hH]
  obtain ⟨gs, rfl, rfl⟩ := hG
  obtain ⟨hs, rfl, rfl⟩ := hH
  have d0 := Det.arg' (P := P) (vs := [encGroup gs, encGroup hs]) (rest := []) (j := 0) rfl
  have d1 := Det.arg' (P := P) (vs := [encGroup gs, encGroup hs]) (rest := []) (j := 1) rfl
  have c1 := Det.call (Det.mk2 d0 d1) (le_spec hm hle hj ⟨gs, rfl, rfl⟩ hs)
  have c2 := Det.call (Det.mk2 d1 d0) (le_spec hm hle hj ⟨hs, rfl, rfl⟩ gs)
  have hite := Det.ite_sum c1 c2 (Det.nat 0)
  have heq : (if (decide (gens hs ≤ gens gs)).toNat = 0 then Val.nat 0
      else boolVal (decide (gens gs ≤ gens hs))) = boolVal (decide (gens gs = gens hs)) := by
    by_cases h1 : gens hs ≤ gens gs <;> by_cases h2 : gens gs ≤ gens hs
    · have he : gens gs = gens hs := le_antisymm h2 h1
      simp [he]
    · have hne : gens gs ≠ gens hs := fun he => h2 (le_of_eq he)
      simp [h1, h2, hne]
    · have hne : gens gs ≠ gens hs := fun he => h1 (le_of_eq he.symm)
      simp [h1, hne]
    · have hne : gens gs ≠ gens hs := fun he => h1 (le_of_eq he.symm)
      simp [h1, hne]
  rw [heq] at hite
  refine FunDet.intro hentry (hite.mono ?_)
  have h1_6 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h2_6 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hT1 : (Val.list [encGroup gs, encGroup hs]).wt ≤ 1300 * (n + 1) ^ 6 := by
    have := wt_list2_le (encGroup gs) (encGroup hs)
    omega
  have hT2 : (Val.list [encGroup hs, encGroup gs]).wt ≤ 1300 * (n + 1) ^ 6 := by
    have := wt_list2_le (encGroup hs) (encGroup gs)
    omega
  have hw1 := wt_encPerm_le (1 : Perm (Fin n))
  have hsz1 : (Val.list [encGroup gs, encPerm (1 : Perm (Fin n))]).size ≤ 700 * (n + 1) ^ 6 := by
    have := (Val.list [encGroup gs, encPerm (1 : Perm (Fin n))]).size_le_wt
    have := wt_list2_le (encGroup gs) (encPerm (1 : Perm (Fin n)))
    omega
  have hsz2 : (Val.list [encGroup hs, encPerm (1 : Perm (Fin n))]).size ≤ 700 * (n + 1) ^ 6 := by
    have := (Val.list [encGroup hs, encPerm (1 : Perm (Fin n))]).size_le_wt
    have := wt_list2_le (encGroup hs) (encPerm (1 : Perm (Fin n)))
    omega
  have hb1 := (membershipPrim hm).bound_le hsz1
  have hb2 := (membershipPrim hm).bound_le hsz2
  have hm1 : (Val.list [encGroup gs, encGroup hs]).wt *
      (membershipPrim hm).bound (.list [encGroup gs, encPerm (1 : Perm (Fin n))]) ≤
      1300 * ((n + 1) ^ 6 * (membershipPrim hm).boundSize (700 * (n + 1) ^ 6)) := by
    calc (Val.list [encGroup gs, encGroup hs]).wt *
          (membershipPrim hm).bound (.list [encGroup gs, encPerm (1 : Perm (Fin n))])
        ≤ (1300 * (n + 1) ^ 6) * (membershipPrim hm).boundSize (700 * (n + 1) ^ 6) :=
          Nat.mul_le_mul hT1 hb1
      _ = 1300 * ((n + 1) ^ 6 * (membershipPrim hm).boundSize (700 * (n + 1) ^ 6)) := by ring
  have hm2 : (Val.list [encGroup hs, encGroup gs]).wt *
      (membershipPrim hm).bound (.list [encGroup hs, encPerm (1 : Perm (Fin n))]) ≤
      1300 * ((n + 1) ^ 6 * (membershipPrim hm).boundSize (700 * (n + 1) ^ 6)) := by
    calc (Val.list [encGroup hs, encGroup gs]).wt *
          (membershipPrim hm).bound (.list [encGroup hs, encPerm (1 : Perm (Fin n))])
        ≤ (1300 * (n + 1) ^ 6) * (membershipPrim hm).boundSize (700 * (n + 1) ^ 6) :=
          Nat.mul_le_mul hT2 hb2
      _ = 1300 * ((n + 1) ^ 6 * (membershipPrim hm).boundSize (700 * (n + 1) ^ 6)) := by ring
  have hp1 : (Val.list [encGroup gs, encGroup hs]).wt ^ 3 ≤ 1300 ^ 3 * (n + 1) ^ 18 :=
    calc (Val.list [encGroup gs, encGroup hs]).wt ^ 3
        ≤ (1300 * (n + 1) ^ 6) ^ 3 := Nat.pow_le_pow_left hT1 3
      _ = 1300 ^ 3 * (n + 1) ^ 18 := by ring
  have hp2 : (Val.list [encGroup hs, encGroup gs]).wt ^ 3 ≤ 1300 ^ 3 * (n + 1) ^ 18 :=
    calc (Val.list [encGroup hs, encGroup gs]).wt ^ 3
        ≤ (1300 * (n + 1) ^ 6) ^ 3 := Nat.pow_le_pow_left hT2 3
      _ = 1300 ^ 3 * (n + 1) ^ 18 := by ring
  have h6_18 : (n + 1) ^ 6 ≤ (n + 1) ^ 18 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1_18 : 1 ≤ (n + 1) ^ 18 := Nat.one_le_pow _ _ (by omega)
  have hbw1 := wt_boolVal_le (decide (gens hs ≤ gens gs))
  have hbw2 := wt_boolVal_le (decide (gens gs ≤ gens hs))
  have hnw0 : (Val.nat 0).wt = 2 := rfl
  unfold gmpEqGroupCost
  generalize (n + 1) ^ 6 * (membershipPrim hm).boundSize (700 * (n + 1) ^ 6) = QBS at hm1 hm2 ⊢
  generalize (Val.list [encGroup gs, encGroup hs]).wt *
      (membershipPrim hm).bound (.list [encGroup gs, encPerm (1 : Perm (Fin n))]) = M1 at hm1 ⊢
  generalize (Val.list [encGroup hs, encGroup gs]).wt *
      (membershipPrim hm).bound (.list [encGroup hs, encPerm (1 : Perm (Fin n))]) = M2 at hm2 ⊢
  generalize (Val.list [encGroup gs, encGroup hs]).wt ^ 3 = P1 at hp1 ⊢
  generalize (Val.list [encGroup hs, encGroup gs]).wt ^ 3 = P2 at hp2 ⊢
  generalize (n + 1) ^ 18 = Q18 at hp1 hp2 h6_18 h1_18 ⊢
  generalize (n + 1) ^ 6 = Q6 at hT1 hT2 h6_18 ⊢
  omega

/-! ### Finding the first matching stabilizer index -/

/-- On `[ws, gv]`: call `fd` on `[gv, ws]`. -/
def gmpFindSwapF (fd : ℕ) : Expr := .call fd (mk2 (arg 1) (arg 0))

/-- Finding the first stabilizer equal to `gv` in `ws`, at base `b` (10 functions). -/
def gmpFindStabFuns (b jm : ℕ) : List Expr :=
  [gmpFindSwapF (b + 1)] ++ findFuns (b + 1) (b + 4) ++ gmpEqGroupFuns (b + 4) jm

@[simp] theorem length_gmpFindStabFuns (b jm : ℕ) : (gmpFindStabFuns b jm).length = 10 := rfl

/-- Cost bound for `gmpFindStabFuns`. -/
noncomputable def gmpFindStabCost (hm : Membership) (n : ℕ) : ℕ :=
  (n + 1) * gmpEqGroupCost hm n + 10 ^ 10 * (n + 1) ^ 8

theorem gmpFindStab_spec (hm : Membership) {P : Program} {b jm : ℕ}
    (hb : P.HasAt b (gmpFindStabFuns b jm))
    (hj : P.prims[jm]? = some (membershipPrim hm))
    {N G : Subgroup (Perm (Fin n))} {ws : List Val} {gv : Val}
    (hws : GMPStabList N ws) (hG : GroupVal n gv G) (hgw : gv.wt ≤ 320 * (n + 1) ^ 6) :
    FunDet P b (.list [.list ws, gv]) (.nat (ws.findIdx (gmpSameGroupTest G)))
      (gmpFindStabCost hm n) := by
  simp only [gmpFindStabFuns] at hb
  have hentry : P.funs[b]? = some (gmpFindSwapF (b + 1)) := hb.left.left.single
  have hfd : P.HasAt (b + 1) (findFuns (b + 1) (b + 4)) := by simpa using hb.left.right
  have heq : P.HasAt (b + 4) (gmpEqGroupFuns (b + 4) jm) := by
    simpa [findFuns, loopFuns, Nat.add_assoc] using hb.right
  have hlen := hws.length_eq
  have hp : ∀ x ∈ ws, FunDet P (b + 4) (.list [gv, x]) (boolVal (gmpSameGroupTest G x))
      (gmpEqGroupCost hm n) := by
    intro x hx
    obtain ⟨i, hxG, hxw⟩ := hws.mem_info hx
    exact gmpEqGroup_spec hm heq hj hG hgw hxG hxw
  have hfind : FunDet P (b + 1) (.list [gv, .list ws]) (.nat (ws.findIdx (gmpSameGroupTest G)))
      ((ws.map fun _ => gmpEqGroupCost hm n).sum +
        loopModK * (ws.length + 1) * ((Val.list [gv, .list ws]).wt + 2 * ws.length + 3)) :=
    find_spec hfd hp
  have d0 := Det.arg' (P := P) (vs := [Val.list ws, gv]) (rest := []) (j := 0) rfl
  have d1 := Det.arg' (P := P) (vs := [Val.list ws, gv]) (rest := []) (j := 1) rfl
  have dcall := Det.call (Det.mk2 d1 d0) hfind
  refine FunDet.intro hentry (dcall.mono ?_)
  have hsum : (ws.map fun _ => gmpEqGroupCost hm n).sum = n * gmpEqGroupCost hm n := by
    rw [List.map_const', List.sum_replicate, smul_eq_mul, hlen]
  rw [hsum]
  have hn_mul : n * gmpEqGroupCost hm n ≤ (n + 1) * gmpEqGroupCost hm n :=
    Nat.mul_le_mul_right _ (by omega)
  have hw_ws := hws.wt_le
  have hw_pair1 := wt_list2_le gv (.list ws)
  have hw_pair2 := wt_list2_le (.list ws) gv
  have hidx_le : ws.findIdx (gmpSameGroupTest G) ≤ n := List.findIdx_le_length.trans hlen.le
  have hw_out := wt_nat_le (ws.findIdx (gmpSameGroupTest G))
  have h6_7 : (n + 1) ^ 6 ≤ (n + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1_7 : n + 1 ≤ (n + 1) ^ 7 := Nat.le_self_pow (by omega) _
  have hloop : loopModK * (ws.length + 1) * ((Val.list [gv, .list ws]).wt + 2 * ws.length + 3) ≤
      2000000 * (n + 1) ^ 8 := by
    have hmid : (Val.list [gv, .list ws]).wt + 2 * ws.length + 3 ≤ 2000 * (n + 1) ^ 7 := by omega
    calc loopModK * (ws.length + 1) * ((Val.list [gv, .list ws]).wt + 2 * ws.length + 3)
        ≤ 1000 * (n + 1) * (2000 * (n + 1) ^ 7) :=
          Nat.mul_le_mul (by simp [loopModK]; omega) hmid
      _ = 2000000 * (n + 1) ^ 8 := by ring
  have h7_8 : (n + 1) ^ 7 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1_8 : 1 ≤ (n + 1) ^ 8 := Nat.one_le_pow _ _ (by omega)
  unfold gmpFindStabCost
  generalize (n + 1) * gmpEqGroupCost hm n = EC at hn_mul ⊢
  generalize n * gmpEqGroupCost hm n = EC0 at hn_mul ⊢
  generalize loopModK * (ws.length + 1) * ((Val.list [gv, .list ws]).wt + 2 * ws.length + 3) = LP at hloop ⊢
  generalize (n + 1) ^ 8 = Q8 at hloop h7_8 h1_8 ⊢
  generalize (n + 1) ^ 7 = Q7 at hw_ws h6_7 h1_7 h7_8 ⊢
  generalize (n + 1) ^ 6 = Q6 at hgw h6_7 ⊢
  omega

/-! ### Representative labeling of all `n` point stabilizers -/

/-- On `ws`: map `gmpFindStabFuns` over `[ws, ws]`. -/
def gmpStabReprEntry (mp : ℕ) : Expr := .call mp (mk2 (.var 0) (.var 0))

/-- Computing `ReprVal n rv (gmpStabRel N)` from `ws`, at base `b` (14 functions). -/
def gmpStabReprFuns (b jm : ℕ) : List Expr :=
  [gmpStabReprEntry (b + 1)] ++ mapFuns (b + 1) (b + 4) ++ gmpFindStabFuns (b + 4) jm

@[simp] theorem length_gmpStabReprFuns (b jm : ℕ) : (gmpStabReprFuns b jm).length = 14 := rfl

/-- Cost bound for `gmpStabReprFuns`. -/
noncomputable def gmpStabReprCost (hm : Membership) (n : ℕ) : ℕ :=
  (n + 1) * gmpFindStabCost hm n + 10 ^ 10 * (n + 1) ^ 8

open Classical in
theorem gmpStabRepr_spec (hm : Membership) {P : Program} {b jm : ℕ}
    (hb : P.HasAt b (gmpStabReprFuns b jm))
    (hj : P.prims[jm]? = some (membershipPrim hm))
    {N : Subgroup (Perm (Fin n))} {ws : List Val} (hws : GMPStabList N ws) :
    FunAll P b (.list ws) (fun rv cost =>
      ReprVal n rv (gmpStabRel N) ∧ cost ≤ gmpStabReprCost hm n) := by
  simp only [gmpStabReprFuns] at hb
  have hentry : P.funs[b]? = some (gmpStabReprEntry (b + 1)) := hb.left.left.single
  have hmp : P.HasAt (b + 1) (mapFuns (b + 1) (b + 4)) := by simpa using hb.left.right
  have hfs : P.HasAt (b + 4) (gmpFindStabFuns (b + 4) jm) := by
    simpa [mapFuns, loopFuns, Nat.add_assoc] using hb.right
  have hws' := hws
  obtain ⟨f, hws_eq, hf⟩ := hws
  have hlen : ws.length = n := by simp [hws_eq]
  have hex : ∀ i : Fin n, ws.findIdx (gmpSameGroupTest (pointwiseStab N [i])) < n := by
    intro i
    have hmem : f i ∈ ws := by
      rw [hws_eq]
      exact List.mem_map_of_mem (List.mem_finRange i)
    have htrue : gmpSameGroupTest (pointwiseStab N [i]) (f i) = true := by
      rw [gmpSameGroupTest_of_groupVal (hf i).1, decide_eq_true_iff]
    have hlt := List.findIdx_lt_length_of_exists ⟨f i, hmem, htrue⟩
    rwa [hlen] at hlt
  let r : Fin n → Fin n := fun i => ⟨ws.findIdx (gmpSameGroupTest (pointwiseStab N [i])), hex i⟩
  have hr_rel : ∀ i : Fin n, pointwiseStab N [r i] = pointwiseStab N [i] := by
    intro i
    have hget := List.findIdx_getElem (p := gmpSameGroupTest (pointwiseStab N [i])) (xs := ws)
      (w := hlen.symm ▸ hex i)
    have hget_f : ws[(r i).val]'(hlen.symm ▸ (r i).isLt) = f (r i) := by
      simp [hws_eq]
    rw [hget_f, gmpSameGroupTest_of_groupVal (hf (r i)).1, decide_eq_true_iff] at hget
    exact hget.symm
  have hr_iff : ∀ i j : Fin n, r i = r j ↔ gmpStabRel N i j := by
    intro i j
    unfold gmpStabRel
    constructor
    · intro hij
      rw [← hr_rel i, hij, hr_rel j]
    · intro hij
      ext
      change ws.findIdx (gmpSameGroupTest (pointwiseStab N [i])) =
        ws.findIdx (gmpSameGroupTest (pointwiseStab N [j]))
      rw [hij]
  have hr_idem : ∀ i : Fin n, r (r i) = r i := fun i => (hr_iff (r i) i).mpr (hr_rel i)
  have hRepr : ReprVal n (encFun fun i => (r i : ℕ)) (gmpStabRel N) :=
    ⟨r, rfl, hr_iff, hr_idem⟩
  let R : Val → Val → Prop := fun x w => ∀ i : Fin n, x = f i → w = .nat (r i : ℕ)
  have hmap_call := map_spec (c := .list ws) (xs := ws) hmp (R := R)
    (B := fun _ => gmpFindStabCost hm n) (by
      intro x hx
      rw [hws_eq] at hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      refine FunAll.mono (gmpFindStab_spec hm hfs hj hws' (hf i).1 (hf i).2) fun w c hw =>
        ⟨fun j hj' => ?_, hw.2⟩
      have hG_eq : pointwiseStab N [i] = pointwiseStab N [j] := by
        have h1 := (hf i).1
        have h2 := (hf j).1
        rw [← hj'] at h2
        exact GroupVal.unique h1 h2
      rw [hw.1]
      change Val.nat (ws.findIdx (gmpSameGroupTest (pointwiseStab N [i]))) =
        Val.nat (ws.findIdx (gmpSameGroupTest (pointwiseStab N [j])))
      rw [hG_eq])
  have d0 := Det.var' (P := P) (env := [Val.list ws]) (i := 0) rfl
  obtain ⟨ca, da, hca_le⟩ : ∃ ca, Det P [Val.list ws] (mk2 (.var 0) (.var 0))
      (.list [.list ws, .list ws]) ca ∧ ca ≤ 10 * (Val.list ws).wt + 25 := by
    refine ⟨_, Det.mk2 d0 d0, ?_⟩
    have := wt_list2_le (.list ws) (.list ws)
    omega
  have dcall := EvalAll.call_funAll (f := b + 1) da
    (Q := fun w cost => ∃ out, w = .list out ∧ List.Forall₂ R ws out ∧
      cost ≤ ca + ((ws.map fun _ => gmpFindStabCost hm n).sum +
        mapK * (ws.length + 1) * ((Val.list [.list ws, .list ws]).wt + w.wt + 1)) + w.wt + 1)
    fun v ca' hv => by
      obtain ⟨rfl, hca'⟩ := hv
      exact hmap_call.mono fun w cb ⟨out, hw_eq, hrel, hcb⟩ =>
        ⟨out, hw_eq, hrel, by omega⟩
  refine FunAll.intro hentry (dcall.mono ?_)
  rintro w cost ⟨out, rfl, hrel, htot⟩
  have hout_eq : out = (List.finRange n).map (fun i : Fin n => Val.nat (r i : ℕ)) := by
    rw [hws_eq] at hrel
    exact forall₂_map_eq (fun i _ w hw => hw i rfl) hrel
  rw [hout_eq] at htot ⊢
  refine ⟨hRepr, ?_⟩
  have hsum : (ws.map fun _ => gmpFindStabCost hm n).sum = n * gmpFindStabCost hm n := by
    rw [List.map_const', List.sum_replicate, smul_eq_mul, hlen]
  rw [hsum] at htot
  have hn_mul : n * gmpFindStabCost hm n ≤ (n + 1) * gmpFindStabCost hm n :=
    Nat.mul_le_mul_right _ (by omega)
  have hw_ws := hws'.wt_le
  have hw_pair := wt_list2_le (.list ws) (.list ws)
  have hw_out : (Val.list ((List.finRange n).map fun i : Fin n => Val.nat (r i : ℕ))).wt ≤
      4 * (n + 1) ^ 2 := wt_encRepr_le r
  have h1_7 : 1 ≤ (n + 1) ^ 7 := Nat.one_le_pow _ _ (by omega)
  have h2_7 : (n + 1) ^ 2 ≤ (n + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have h7_8 : (n + 1) ^ 7 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1_8 : 1 ≤ (n + 1) ^ 8 := Nat.one_le_pow _ _ (by omega)
  have hmap_overhead : mapK * (ws.length + 1) *
      ((Val.list [.list ws, .list ws]).wt +
        (Val.list ((List.finRange n).map fun i : Fin n => Val.nat (r i : ℕ))).wt + 1) ≤
      3000000 * (n + 1) ^ 8 := by
    have hmid : (Val.list [.list ws, .list ws]).wt +
        (Val.list ((List.finRange n).map fun i : Fin n => Val.nat (r i : ℕ))).wt + 1 ≤
        3000 * (n + 1) ^ 7 := by omega
    calc mapK * (ws.length + 1) * ((Val.list [.list ws, .list ws]).wt +
          (Val.list ((List.finRange n).map fun i : Fin n => Val.nat (r i : ℕ))).wt + 1)
        ≤ 1000 * (n + 1) * (3000 * (n + 1) ^ 7) :=
          Nat.mul_le_mul (by simp [mapK]; omega) hmid
      _ = 3000000 * (n + 1) ^ 8 := by ring
  unfold gmpStabReprCost
  generalize (n + 1) * gmpFindStabCost hm n = FC at hn_mul ⊢
  generalize n * gmpFindStabCost hm n = FC0 at hn_mul htot ⊢
  generalize mapK * (ws.length + 1) * ((Val.list [.list ws, .list ws]).wt + (Val.list ((List.finRange n).map fun i : Fin n => Val.nat (r i : ℕ))).wt + 1) = MO at hmap_overhead htot
  generalize (Val.list ((List.finRange n).map fun i : Fin n => Val.nat (r i : ℕ))).wt = OW at hw_out htot ⊢
  generalize (n + 1) ^ 8 = Q8 at hmap_overhead h7_8 h1_8 ⊢
  generalize (n + 1) ^ 7 = Q7 at hw_ws h1_7 h2_7 h7_8 ⊢
  generalize (n + 1) ^ 2 = Q2 at hw_out h2_7 ⊢
  omega

end GI.Impl
