module

public import Workspace.Proved.NInt
public import Workspace.Proved.SSMembership
public import Workspace.MulticosetModel

@[expose] public section

/-!
# Coset intersection with a normalizing subgroup

Given `G = ⟨gs⟩`, `H = ⟨hs⟩` with `Normalizes H G` (`H` normalizes `G`) and `x`, we compute
`G x ∩ H`:
1. Since `H` normalizes `G`, `H G = ⟨hs ++ 1 :: gs⟩`, and `∃ g ∈ G, g x ∈ H` holds if and only if
   `x⁻¹ ∈ H G`.
2. Test `x⁻¹ ∈ ⟨hs ++ 1 :: gs⟩` using `Membership`.
3. If false, return `0`.
4. If true, factor `x⁻¹ = u g` (`u ∈ H`, `g ∈ G`) using `NormalizedFactor` and compute
   `H ∩ G = G ∩ H` using `NormalizedIntersection`, returning `[u⁻¹, L]`.
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved Equiv

theorem normCoset_mem_gens {n : ℕ} {hs gs : List (Perm (Fin n))}
    (hn : GI.Lang.Normalizes (gens hs) (gens gs)) (x : Perm (Fin n)) :
    x ∈ gens (hs ++ 1 :: gs) ↔ ∃ u ∈ gens hs, ∃ g ∈ gens gs, x = u * g := by
  constructor
  · intro hx
    refine GI.Multicoset.closure_mem_mul hn (fun γ hγ => ?_) x hx
    rcases List.mem_append.1 hγ with h | h
    · exact ⟨γ, Subgroup.subset_closure h, 1, (gens gs).one_mem, by simp⟩
    · rcases List.mem_cons.1 h with rfl | h
      · exact ⟨1, (gens hs).one_mem, 1, (gens gs).one_mem, by simp⟩
      · exact ⟨1, (gens hs).one_mem, γ, Subgroup.subset_closure h, by simp⟩
  · rintro ⟨u, hu, g, hg, rfl⟩
    have hH : gens hs ≤ gens (hs ++ 1 :: gs) :=
      Subgroup.closure_mono fun γ hγ => List.mem_append_left _ hγ
    have hG : gens gs ≤ gens (hs ++ 1 :: gs) :=
      Subgroup.closure_mono fun γ hγ => List.mem_append_right _ (List.mem_cons_of_mem _ hγ)
    exact Subgroup.mul_mem _ (hH hu) (hG hg)

theorem normCoset_nonempty_iff {n : ℕ} {G H : Subgroup (Perm (Fin n))} (x : Perm (Fin n)) :
    (∃ u ∈ H, ∃ g ∈ G, x⁻¹ = u * g) ↔ ∃ g ∈ G, g * x ∈ H := by
  constructor
  · rintro ⟨u, hu, g, hg, he⟩
    refine ⟨g, hg, ?_⟩
    have : g * x = u⁻¹ := by
      calc g * x = u⁻¹ * (u * g) * x := by group
        _ = u⁻¹ * x⁻¹ * x := by rw [← he]
        _ = u⁻¹ := by group
    rw [this]
    exact H.inv_mem hu
  · rintro ⟨g, hg, hgx⟩
    refine ⟨(g * x)⁻¹, H.inv_mem hgx, g, hg, ?_⟩
    group

theorem normCoset_encGroup {n : ℕ} (hs gs : List (Perm (Fin n))) :
    encGroup (hs ++ 1 :: gs) =
      .list [.nat n, .list (((1 :: hs).map encPerm) ++ ((1 :: gs).map encPerm))] := by
  simp [encGroup, encPerms]

/-- An instance of normalized coset intersection: `H = ⟨hs⟩` normalizes `G = ⟨gs⟩`. -/
structure NormCosetInst where
  n : ℕ
  gs : List (Perm (Fin n))
  hs : List (Perm (Fin n))
  norm : GI.Lang.Normalizes (gens hs) (gens gs)
  x : Perm (Fin n)

/-- The task of computing `G x ∩ H` when `H` normalizes `G`. -/
def NormCosetTask : GI.Cited.Task NormCosetInst :=
  GI.Cited.Task.ofVal (fun I => .list [encGroup I.gs, encGroup I.hs, encPerm I.x])
    (fun I w => CosetIntOut (gens I.gs) (gens I.hs) I.x w)

/-- The entry function, on `[encGroup gs, encGroup hs, encPerm x]`.
Environment: `[input, encPerm x⁻¹, encGroup (hs ++ 1 :: gs), [encPerm u, encPerm g], L]`. -/
def normCosetEntry : Expr :=
  .letE (.call 4 (arg 2))
  (.letE (mk2 (.get (arg 1) (.nat 0))
      (.call 1 (mk2 (.get (arg 1) (.nat 1)) (.get (arg 0) (.nat 1)))))
    (.ite (.prim 0 (mk2 (.var 2) (.var 1)))
      (.letE (.prim 1 (mk3 (arg 1) (arg 0) (.var 1)))
      (.letE (.prim 2 (mk2 (arg 1) (arg 0)))
        (mk2 (.call 4 (.get (.var 3) (.nat 0))) (.var 4))))
      (.nat 0)))

def normCosetFuns : List Expr :=
  [normCosetEntry] ++ appendFuns 1 ++ invFuns 4

noncomputable def normCosetProgram (hm : Membership) (hfac : NormalizedFactor)
    (hni : NormalizedIntersection) : Program :=
  ⟨normCosetFuns, [membershipPrim hm, normalizedFactorPrim hfac, normalizedIntersectionPrim hni]⟩

section Layout

variable (hm : Membership) (hfac : NormalizedFactor) (hni : NormalizedIntersection)

theorem normCoset_hasAt : (normCosetProgram hm hfac hni).HasAt 0 normCosetFuns := by
  simpa [normCosetProgram] using Program.hasAt_append [] normCosetFuns []
    [membershipPrim hm, normalizedFactorPrim hfac, normalizedIntersectionPrim hni]

theorem normCoset_entry : (normCosetProgram hm hfac hni).funs[0]? = some normCosetEntry := rfl

theorem normCoset_append : (normCosetProgram hm hfac hni).HasAt 1 (appendFuns 1) :=
  (normCoset_hasAt hm hfac hni).block 1 rfl

theorem normCoset_inv : (normCosetProgram hm hfac hni).HasAt 4 (invFuns 4) :=
  (normCoset_hasAt hm hfac hni).block 4 rfl

theorem normCoset_p0 : (normCosetProgram hm hfac hni).prims[0]? = some (membershipPrim hm) := rfl
theorem normCoset_p1 :
    (normCosetProgram hm hfac hni).prims[1]? = some (normalizedFactorPrim hfac) := rfl
theorem normCoset_p2 :
    (normCosetProgram hm hfac hni).prims[2]? = some (normalizedIntersectionPrim hni) := rfl

end Layout

/-- Bound on argument weights inside `normCosetEntry`. -/
def normCosetS (X : ℕ) : ℕ := 10 ^ 8 * (X + 1) ^ 6

/-- Total cost bound for `normCosetProgram`. -/
noncomputable def normCosetCost (hm : Membership) (hfac : NormalizedFactor)
    (hni : NormalizedIntersection) (X : ℕ) : ℕ :=
  1000 * normCosetS X +
    (membershipPrim hm).boundSize (normCosetS X) +
    (normalizedFactorPrim hfac).boundSize (normCosetS X) +
    (normalizedIntersectionPrim hni).boundSize (normCosetS X)

theorem normCosetCost_poly (hm : Membership) (hfac : NormalizedFactor)
    (hni : NormalizedIntersection) :
    PBU (fun _ X _ => normCosetCost hm hfac hni X) := by
  unfold normCosetCost normCosetS Prim.boundSize
  norm_poly

section Steps

variable (hm : Membership) (hfac : NormalizedFactor) (hni : NormalizedIntersection)
  {n : ℕ} (gs hs : List (Perm (Fin n))) (x : Perm (Fin n))

/-- Step 1: `encPerm x⁻¹`. -/
theorem normCoset_d1 {X : ℕ} (_hX : (Val.list [encGroup gs, encGroup hs, encPerm x]).wt = X)
    (hw : NIntFacW gs hs x X) :
    Det (normCosetProgram hm hfac hni)
      [Val.list [encGroup gs, encGroup hs, encPerm x]]
      (.call 4 (arg 2)) (encPerm x⁻¹) (10 ^ 6 * (X + 1) ^ 4) := by
  have hx := Det.arg' (P := normCosetProgram hm hfac hni)
    (vs := [encGroup gs, encGroup hs, encPerm x]) (rest := []) (j := 2) rfl
  refine (Det.call hx (inv_spec (normCoset_inv hm hfac hni) x)).mono ?_
  have := hw.wGA; have := hw.hn
  have := wt_encPerm_le x⁻¹
  have hn4 : (n + 1) ^ 4 ≤ (X + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have hn2 : (n + 1) ^ 2 ≤ (X + 1) ^ 4 := (nint_pow_mono (by omega) (by decide)).trans hn4
  have q1 : X + 1 ≤ (X + 1) ^ 4 := Nat.le_self_pow (by decide) _
  unfold invK
  omega

/-- Step 2: `encGroup (hs ++ 1 :: gs)`. -/
theorem normCoset_d2 {X : ℕ} (_hX : (Val.list [encGroup gs, encGroup hs, encPerm x]).wt = X)
    (hw : NIntFacW gs hs x X) :
    Det (normCosetProgram hm hfac hni)
      [Val.list [encGroup gs, encGroup hs, encPerm x], encPerm x⁻¹]
      (mk2 (.get (arg 1) (.nat 0)) (.call 1 (mk2 (.get (arg 1) (.nat 1)) (.get (arg 0) (.nat 1)))))
      (encGroup (hs ++ 1 :: gs)) (10 ^ 6 * (X + 1) ^ 2) := by
  rw [normCoset_encGroup]
  have a0 := Det.arg' (P := normCosetProgram hm hfac hni)
    (vs := [encGroup gs, encGroup hs, encPerm x]) (rest := [encPerm x⁻¹]) (j := 0) rfl
  have a1 := Det.arg' (P := normCosetProgram hm hfac hni)
    (vs := [encGroup gs, encGroup hs, encPerm x]) (rest := [encPerm x⁻¹]) (j := 1) rfl
  have dn := Det.encPerms_size (gs := 1 :: hs) a1
  have dhs := Det.encPerms_gens (gs := 1 :: hs) a1
  have dgs := Det.encPerms_gens (gs := 1 :: gs) a0
  have dapp := Det.call (Det.mk2 dhs dgs)
    (nint_append (normCoset_append hm hfac hni) ((1 :: hs).map encPerm) ((1 :: gs).map encPerm))
  refine (Det.mk2 dn dapp).mono ?_
  have := hw.wGA; have := hw.wA; have := hw.wB; have := hw.hn; have := hw.wn
  have h1 := wt_list2_le (.list ((1 :: hs).map encPerm)) (.list ((1 :: gs).map encPerm))
  have h2 := nint_wt_append ((1 :: hs).map encPerm) ((1 :: gs).map encPerm)
  have h3 := wt_list2_le (.nat n) (.list (((1 :: hs).map encPerm) ++ ((1 :: gs).map encPerm)))
  have h4 := nint_pow_le
    (W := (Val.list [.list ((1 :: hs).map encPerm), .list ((1 :: gs).map encPerm)]).wt)
    (c := 7) (Y := X + 1) (by omega) 2
  have h5 : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by decide) _
  omega

/-- Step 3: argument of the membership call. -/
theorem normCoset_d3 {X : ℕ} (_hX : (Val.list [encGroup gs, encGroup hs, encPerm x]).wt = X)
    (hw : NIntFacW gs hs x X)
    (wP : (encGroup (hs ++ 1 :: gs)).wt < 10 ^ 6 * (X + 1) ^ 2) :
    Det (normCosetProgram hm hfac hni)
      [Val.list [encGroup gs, encGroup hs, encPerm x], encPerm x⁻¹, encGroup (hs ++ 1 :: gs)]
      (mk2 (.var 2) (.var 1))
      (.list [encGroup (hs ++ 1 :: gs), encPerm x⁻¹]) (10 ^ 7 * (X + 1) ^ 2) := by
  have dv2 : Det (normCosetProgram hm hfac hni)
    [Val.list [encGroup gs, encGroup hs, encPerm x], encPerm x⁻¹, encGroup (hs ++ 1 :: gs)]
    (.var 2) (encGroup (hs ++ 1 :: gs)) _ := Det.var' rfl
  have dv1 : Det (normCosetProgram hm hfac hni)
    [Val.list [encGroup gs, encGroup hs, encPerm x], encPerm x⁻¹, encGroup (hs ++ 1 :: gs)]
    (.var 1) (encPerm x⁻¹) _ := Det.var' rfl
  refine (Det.mk2 dv2 dv1).mono ?_
  have := hw.wGA; have := hw.hn
  have wx := wt_encPerm_le x⁻¹
  have hn2 : (n + 1) ^ 2 ≤ (X + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h1 := wt_list2_le (encGroup (hs ++ 1 :: gs)) (encPerm x⁻¹)
  have h2 : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by decide) _
  omega

/-- Step 4: argument of the factorization call. -/
theorem normCoset_d4 {X : ℕ} (_hX : (Val.list [encGroup gs, encGroup hs, encPerm x]).wt = X)
    (hw : NIntFacW gs hs x X) :
    Det (normCosetProgram hm hfac hni)
      [Val.list [encGroup gs, encGroup hs, encPerm x], encPerm x⁻¹, encGroup (hs ++ 1 :: gs)]
      (mk3 (arg 1) (arg 0) (.var 1))
      (.list [encGroup hs, encGroup gs, encPerm x⁻¹]) (10 ^ 5 * (X + 1) ^ 2) := by
  have da1 := Det.arg' (P := normCosetProgram hm hfac hni)
    (vs := [encGroup gs, encGroup hs, encPerm x])
    (rest := [encPerm x⁻¹, encGroup (hs ++ 1 :: gs)]) (j := 1) rfl
  have da0 := Det.arg' (P := normCosetProgram hm hfac hni)
    (vs := [encGroup gs, encGroup hs, encPerm x])
    (rest := [encPerm x⁻¹, encGroup (hs ++ 1 :: gs)]) (j := 0) rfl
  have dv1 : Det (normCosetProgram hm hfac hni)
    [Val.list [encGroup gs, encGroup hs, encPerm x], encPerm x⁻¹, encGroup (hs ++ 1 :: gs)]
    (.var 1) (encPerm x⁻¹) _ := Det.var' rfl
  refine (Det.mk3 da1 da0 dv1).mono ?_
  have := hw.wGA; have := hw.hn
  have wx := wt_encPerm_le x⁻¹
  have hn2 : (n + 1) ^ 2 ≤ (X + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h1 := wt_list3_le (encGroup hs) (encGroup gs) (encPerm x⁻¹)
  have h2 : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by decide) _
  omega

/-- Step 5: argument of the intersection call. -/
theorem normCoset_d5 {X : ℕ} (_hX : (Val.list [encGroup gs, encGroup hs, encPerm x]).wt = X)
    (hw : NIntFacW gs hs x X) (r : Val) :
    Det (normCosetProgram hm hfac hni)
      [Val.list [encGroup gs, encGroup hs, encPerm x], encPerm x⁻¹, encGroup (hs ++ 1 :: gs), r]
      (mk2 (arg 1) (arg 0))
      (.list [encGroup hs, encGroup gs]) (10 ^ 5 * (X + 1) ^ 2) := by
  have da1 := Det.arg' (P := normCosetProgram hm hfac hni)
    (vs := [encGroup gs, encGroup hs, encPerm x])
    (rest := [encPerm x⁻¹, encGroup (hs ++ 1 :: gs), r]) (j := 1) rfl
  have da0 := Det.arg' (P := normCosetProgram hm hfac hni)
    (vs := [encGroup gs, encGroup hs, encPerm x])
    (rest := [encPerm x⁻¹, encGroup (hs ++ 1 :: gs), r]) (j := 0) rfl
  refine (Det.mk2 da1 da0).mono ?_
  have := hw.wGA
  have h1 := wt_list2_le (encGroup hs) (encGroup gs)
  have h2 : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by decide) _
  omega

/-- Step 6: final output `[encPerm u⁻¹, L]`. -/
theorem normCoset_d6 {X : ℕ} (_hX : (Val.list [encGroup gs, encGroup hs, encPerm x]).wt = X)
    (hw : NIntFacW gs hs x X) (u g : Perm (Fin n)) (L : Val)
    (wL : L.wt ≤ 13 * (n + 1) ^ 6) :
    Det (normCosetProgram hm hfac hni)
      [Val.list [encGroup gs, encGroup hs, encPerm x], encPerm x⁻¹, encGroup (hs ++ 1 :: gs),
        .list [encPerm u, encPerm g], L]
      (mk2 (.call 4 (.get (.var 3) (.nat 0))) (.var 4))
      (.list [encPerm u⁻¹, L]) (10 ^ 6 * (X + 1) ^ 6) := by
  have dv3 : Det (normCosetProgram hm hfac hni)
    [Val.list [encGroup gs, encGroup hs, encPerm x], encPerm x⁻¹, encGroup (hs ++ 1 :: gs),
      .list [encPerm u, encPerm g], L]
    (.var 3) (.list [encPerm u, encPerm g]) _ := Det.var' rfl
  have dv4 : Det (normCosetProgram hm hfac hni)
    [Val.list [encGroup gs, encGroup hs, encPerm x], encPerm x⁻¹, encGroup (hs ++ 1 :: gs),
      .list [encPerm u, encPerm g], L]
    (.var 4) L _ := Det.var' rfl
  have du := Det.get' dv3 (Det.nat 0) rfl
  have duinv := Det.call du (inv_spec (normCoset_inv hm hfac hni) u)
  refine (Det.mk2 duinv dv4).mono ?_
  have := hw.wGA; have := hw.hn
  have wu := wt_encPerm_le u
  have wg := wt_encPerm_le g
  have wuinv := wt_encPerm_le u⁻¹
  have wug := wt_list2_le (encPerm u) (encPerm g)
  have wout := wt_list2_le (encPerm u⁻¹) L
  have hn6 : (n + 1) ^ 6 ≤ (X + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have hn2 : (n + 1) ^ 2 ≤ (X + 1) ^ 6 := (nint_pow_mono (by omega) (by decide)).trans hn6
  have hn4 : (n + 1) ^ 4 ≤ (X + 1) ^ 6 := (nint_pow_mono (by omega) (by decide)).trans hn6
  have q1 : 1 ≤ (X + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  unfold invK
  omega

end Steps

theorem normCoset_spec (hm : Membership) (hfac : NormalizedFactor)
    (hni : NormalizedIntersection) (I : NormCosetInst) :
    FunAll (normCosetProgram hm hfac hni) 0 (.list [encGroup I.gs, encGroup I.hs, encPerm I.x])
      (fun v c => CosetIntOut (gens I.gs) (gens I.hs) I.x v ∧
        c ≤ normCosetCost hm hfac hni
          (Val.list [encGroup I.gs, encGroup I.hs, encPerm I.x]).wt) := by
  obtain ⟨n, gs, hs, hnorm, x⟩ := I
  dsimp only
  have hw := nintFacW_of gs hs x
  obtain ⟨X, hX⟩ : ∃ X, (Val.list [encGroup gs, encGroup hs, encPerm x]).wt = X := ⟨_, rfl⟩
  rw [hX] at hw ⊢
  have d1 := normCoset_d1 hm hfac hni gs hs x hX hw
  have d2 := normCoset_d2 hm hfac hni gs hs x hX hw
  have wP := d2.wt_lt
  have d3 := normCoset_d3 hm hfac hni gs hs x hX hw wP
  have h1X : X + 1 ≤ (X + 1) ^ 6 := Nat.le_self_pow (by decide) _
  have h2X : (X + 1) ^ 2 ≤ (X + 1) ^ 6 := nint_pow_mono (by omega) (by decide)
  have h4X : (X + 1) ^ 4 ≤ (X + 1) ^ 6 := nint_pow_mono (by omega) (by decide)
  have hnX := hw.hn; have wGA := hw.wGA
  have hn2 : (n + 1) ^ 2 ≤ (X + 1) ^ 6 :=
    (Nat.pow_le_pow_left (by omega) 2).trans h2X
  have hn6 : (n + 1) ^ 6 ≤ (X + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have hmem_bd : (membershipPrim hm).bound (.list [encGroup (hs ++ 1 :: gs), encPerm x⁻¹]) ≤
      (membershipPrim hm).boundSize (normCosetS X) := by
    refine Prim.bound_le _ ?_
    have hwt := d3.wt_lt
    have hsz := (Val.list [encGroup (hs ++ 1 :: gs), encPerm x⁻¹]).size_le_wt
    unfold normCosetS; omega
  apply FunAll.intro (normCoset_entry hm hfac hni)
  refine EvalAll.letE d1 fun v1 c1 h1 => ?_
  obtain ⟨rfl, hc1⟩ := h1
  refine EvalAll.letE d2 fun v2 c2 h2 => ?_
  obtain ⟨rfl, hc2⟩ := h2
  refine EvalAll.ite (membership_call hm (normCoset_p0 hm hfac hni) d3 ⟨hs ++ 1 :: gs, rfl, rfl⟩)
    (fun vc cc hc => by
      rcases hc.1 with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩)
    fun b cb hmem_call => ?_
  obtain ⟨hb, hcb⟩ := hmem_call
  rcases hb with ⟨he, hmem⟩ | ⟨he, hnmem⟩
  · cases he
    rw [ite_eq_right_iff.mpr fun h => absurd h one_ne_zero]
    have hfac_ex : ∃ u ∈ gens hs, ∃ g ∈ gens gs, x⁻¹ = u * g :=
      (normCoset_mem_gens hnorm x⁻¹).mp hmem
    have d4 := normCoset_d4 hm hfac hni gs hs x hX hw
    have hfac_bd : (normalizedFactorPrim hfac).bound (.list [encGroup hs, encGroup gs, encPerm x⁻¹]) ≤
        (normalizedFactorPrim hfac).boundSize (normCosetS X) := by
      refine Prim.bound_le _ ?_
      have hwt := d4.wt_lt
      have hsz := (Val.list [encGroup hs, encGroup gs, encPerm x⁻¹]).size_le_wt
      unfold normCosetS; omega
    refine EvalAll.letE (normalizedFactor_call hfac (normCoset_p1 hm hfac hni) d4
      ⟨hs, rfl, rfl⟩ ⟨gs, rfl, rfl⟩ hnorm hfac_ex) fun w3 c3 hw3_call => ?_
    obtain ⟨hw3, hc3⟩ := hw3_call
    obtain ⟨u, hu, g, hg, hxinv, rfl⟩ := hw3
    have d5 := normCoset_d5 hm hfac hni gs hs x hX hw (.list [encPerm u, encPerm g])
    have hni_bd : (normalizedIntersectionPrim hni).bound (.list [encGroup hs, encGroup gs]) ≤
        (normalizedIntersectionPrim hni).boundSize (normCosetS X) := by
      refine Prim.bound_le _ ?_
      have hwt := d5.wt_lt
      have hsz := (Val.list [encGroup hs, encGroup gs]).size_le_wt
      unfold normCosetS; omega
    refine EvalAll.letE (normalizedIntersection_call hni (normCoset_p2 hm hfac hni) d5
      ⟨hs, rfl, rfl⟩ ⟨gs, rfl, rfl⟩ hnorm) fun L c4 h4_call => ?_
    obtain ⟨hL, hc4⟩ := h4_call
    have wL := GensVal.wt_le hL
    have d6 := normCoset_d6 hm hfac hni gs hs x hX hw u g L wL
    refine d6.post fun c5 hc5 => ⟨?_, ?_⟩
    · right
      refine ⟨u⁻¹, ⟨g, hg, ?_⟩, (gens hs).inv_mem hu, L, rfl, ?_⟩
      · calc u⁻¹ = u⁻¹ * x⁻¹ * x := by group
          _ = u⁻¹ * (u * g) * x := by rw [hxinv]
          _ = g * x := by group
      · rwa [inf_comm] at hL
    · have wu := wt_encPerm_le u
      have wg := wt_encPerm_le g
      have wug := wt_list2_le (encPerm u) (encPerm g)
      have wxinv := wt_encPerm_le x⁻¹
      have wuinv := wt_encPerm_le u⁻¹
      have wout := wt_list2_le (encPerm u⁻¹) L
      have hS : normCosetS X = 10 ^ 8 * (X + 1) ^ 6 := rfl
      unfold normCosetCost
      omega
  · cases he
    rw [if_pos rfl]
    refine (Det.nat 0).post fun c5 hc5 => ⟨?_, ?_⟩
    · left
      refine ⟨rfl, fun g hg hgx => hnmem ?_⟩
      exact (normCoset_mem_gens hnorm x⁻¹).mpr ((normCoset_nonempty_iff x).mpr ⟨g, hg, hgx⟩)
    · have wxinv := wt_encPerm_le x⁻¹
      have : (Val.nat 0).wt = 2 := by decide
      have hS : normCosetS X = 10 ^ 8 * (X + 1) ^ 6 := rfl
      unfold normCosetCost
      omega

/-- **Normalized coset intersection in polynomial time.** -/
theorem normCosetIntersection : ∃ p, PolyTimeAt NormCosetTask p := by
  obtain ⟨K, D, hK⟩ := nint_poly_bound (normCosetCost_poly
    GI.Proved.membership GI.Proved.normalizedFactor GI.Proved.normalizedIntersection)
  refine polyTimeAt_ofVal_of_lang_cells
    (normCosetProgram GI.Proved.membership GI.Proved.normalizedFactor GI.Proved.normalizedIntersection)
    0 K D 1 1 (fun I => nint_cells_bound (nint_cells_list (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      · exact nint_cells_group _
      · exact nint_cells_group _
      · exact nint_cells_perm _))) fun I => ?_
  exact (normCoset_spec GI.Proved.membership GI.Proved.normalizedFactor
    GI.Proved.normalizedIntersection I).mono fun v c h => ⟨h.1, h.2.trans (hK _)⟩

end GI.Impl

namespace GI.Lang

open GI.Cited Equiv

variable {n : ℕ}

/-- **Coset intersection with a normalizing subgroup** as a primitive (retaining the name
`solvableCosetIntersectionPrim` for layout compatibility). -/
noncomputable def solvableCosetIntersectionPrim (_h : SolvableCosetIntersection) : Prim :=
  Prim.ofHyp _ _ GI.Impl.normCosetIntersection

theorem solvableCosetIntersectionPrim_spec (h : SolvableCosetIntersection) {gv hv : Val}
    {G H : Subgroup (Perm (Fin n))} (hG : GroupVal n gv G) (hnorm : Normalizes H G)
    (hH : GroupVal n hv H) (x : Perm (Fin n)) :
    PrimSpec (solvableCosetIntersectionPrim h) (.list [gv, hv, encPerm x]) (CosetIntOut G H x) := by
  obtain ⟨gs, rfl, rfl⟩ := hG
  obtain ⟨hs, rfl, rfl⟩ := hH
  refine (Prim.ofHyp_spec GI.Impl.normCosetIntersection
    (⟨n, gs, hs, hnorm, x⟩ : GI.Impl.NormCosetInst) ?_).mono fun _ hw => hw
  rintro ⟨n', gs', hs', _, x'⟩ hy
  simp only [Val.list.injEq, List.cons.injEq, and_true] at hy
  obtain rfl := encGroup_deg hy.1
  obtain rfl := encGroup_injective hy.1
  obtain rfl := encGroup_injective hy.2.1
  obtain rfl := encPerm_injective hy.2.2
  rfl

theorem solvableCosetIntersection_call (h : SolvableCosetIntersection) {P : Program}
    {env : List Val} {j : ℕ} {a : Expr} {ca : ℕ} {gv hv : Val} {G H : Subgroup (Perm (Fin n))}
    {x : Perm (Fin n)} (hj : P.prims[j]? = some (solvableCosetIntersectionPrim h))
    (ha : Det P env a (.list [gv, hv, encPerm x]) ca)
    (hG : GroupVal n gv G) (hnorm : Normalizes H G) (hH : GroupVal n hv H) :
    EvalAll P env (.prim j a) (fun w c => CosetIntOut G H x w ∧
      c ≤ ca + (solvableCosetIntersectionPrim h).bound (.list [gv, hv, encPerm x]) + 40 * (n + 1) ^ 6 + 1) :=
  EvalAll.prim_spec_le hj ha (solvableCosetIntersectionPrim_spec h hG hnorm hH x)
    fun w hw => CosetIntOut.wt_le hw

end GI.Lang
