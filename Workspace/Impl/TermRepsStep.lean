import Workspace.Impl.TermRepsLoop

/-!
# One round of the coset enumeration as a program (T3)

The context of the rounds is `c = [gR, hl]`: the group value `gR = encGroup hs` of `R` and the
list `hl` of the generators of `H`. The accumulator is the list of representatives.

* `tmRpPredF` on `[[gR, y], r']`: whether `y r'⁻¹ ∈ R` (one call of the cited **Membership**).
* `tmRpTestF` on `[[c, r], acc, g]`: the test of `y = r g` (`tmRpAdd`): `any` of the predicate
  over the list; keep the list, or add `y`.
* `tmRpStepF` on `[c, i, acc]`: `foldl` of the test over the generators, with `r = acc[i]`
  (`tmRpProc`).

The costs are stated for a bound `Y ≥ (m + 1)⁴` on the weight of `gR`; the round costs a
polynomial in `Y` times the length of the list and the number of generators.
-/

namespace GI.Impl

open GI.Lang Equiv
open GI.Machine (BinOp)
open GI.Cited (Val encPerm encGroup gens Membership)

variable {m : ℕ}

/-- The test of one listed element: on `[[gR, y], r']`, membership of `y r'⁻¹` in `R`. -/
def tmRpPredF (jm comp inv : ℕ) : Expr :=
  .prim jm (mk2 (.get (arg 0) (.nat 0))
    (.call comp (mk2 (.get (arg 0) (.nat 1)) (.call inv (arg 1)))))

/-- The cost bound of the predicate. -/
noncomputable def tmRpPredC (hm : Membership) (Y : ℕ) : ℕ :=
  10 ^ 6 * Y + tmPrimC (membershipPrim hm) (20 * Y)

/-- The Boolean `y r⁻¹ ∈ R` read on the value of `r`. -/
noncomputable def tmRpB (R : Subgroup (Perm (Fin m))) (y : Perm (Fin m)) (v : Val) : Bool := by
  classical
  exact decide (∃ r : Perm (Fin m), v = encPerm r ∧ y * r⁻¹ ∈ R)

theorem tmRpB_encPerm (R : Subgroup (Perm (Fin m))) (y r : Perm (Fin m)) :
    tmRpB R y (encPerm r) = true ↔ y * r⁻¹ ∈ R := by
  classical
  unfold tmRpB
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨r', h, hr'⟩
    rwa [encPerm_injective h]
  · exact fun h => ⟨r, rfl, h⟩

/-- **The predicate.** -/
theorem tmRpPred_spec (hm : Membership) {P : Program} {pt jm comp inv : ℕ}
    (hpt : P.funs[pt]? = some (tmRpPredF jm comp inv))
    (hjm : P.prims[jm]? = some (membershipPrim hm))
    (hcomp : P.HasAt comp (composeFuns comp)) (hinv : P.HasAt inv (invFuns inv))
    {gR : Val} {R : Subgroup (Perm (Fin m))} (hR : GroupVal m gR R) {Y : ℕ}
    (hY : (m + 1) ^ 4 ≤ Y) (hgY : gR.wt ≤ Y) (y r : Perm (Fin m)) :
    FunDet P pt (.list [.list [gR, encPerm y], encPerm r]) (boolVal (tmRpB R y (encPerm r)))
      (tmRpPredC hm Y) := by
  have w1 := wt_encPerm_le y
  have w2 := wt_encPerm_le r
  have w3 := wt_encPerm_le (y * r⁻¹)
  have w4 := wt_encPerm_le r⁻¹
  have h1 : 1 ≤ (m + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h2 : (m + 1) ^ 2 ≤ (m + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : (m + 1) ^ 3 ≤ (m + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  set A := Val.list [.list [gR, encPerm y], encPerm r] with hA
  have a1 := wt_list2_le gR (encPerm y)
  have a2 := wt_list2_le (.list [gR, encPerm y]) (encPerm r)
  have d0 := Det.arg' (P := P) (vs := [.list [gR, encPerm y], encPerm r]) (rest := []) (j := 0)
    (v := .list [gR, encPerm y]) rfl
  have d1 := Det.arg' (P := P) (vs := [.list [gR, encPerm y], encPerm r]) (rest := []) (j := 1)
    (v := encPerm r) rfl
  have dg := Det.get' d0 (Det.nat 0) (show [gR, encPerm y][0]? = some gR from rfl)
  have dy := Det.get' d0 (Det.nat 1) (show [gR, encPerm y][1]? = some (encPerm y) from rfl)
  have di := Det.call d1 (inv_spec hinv r)
  have dc := Det.call (Det.mk2 dy di) (compose_spec hcomp y r⁻¹)
  have da := Det.mk2 dg dc
  have hb : (Val.list [gR, encPerm (y * r⁻¹)]).wt ≤ 20 * Y := by
    have := wt_list2_le gR (encPerm (y * r⁻¹)); omega
  have hbound := prim_bound_le (membershipPrim hm) hb
  refine FunAll.intro hpt ((membership_call hm hjm da hR).mono fun w c hw => ?_)
  obtain ⟨hw, hc⟩ := hw
  refine ⟨?_, ?_⟩
  · rcases hw with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · rw [(tmRpB_encPerm R y r).2 h]; rfl
    · have : tmRpB R y (encPerm r) = false := by
        rw [Bool.eq_false_iff]; exact fun h' => h ((tmRpB_encPerm R y r).1 h')
      rw [this]; rfl
  · have e1 : (Val.list [.list [gR, encPerm y], encPerm r]).wt = A.wt := rfl
    have w5 := wt_list2_le (encPerm y) (encPerm r⁻¹)
    unfold tmRpPredC
    simp only [invK, permK] at hc
    omega

/-- **The test of `y = r g`**, on `[[c, r], acc, g]` with `c = [gR, hl]`: keep `acc` if some
listed `r'` has `y r'⁻¹ ∈ R`, else add `y`. -/
def tmRpTestF (ab comp : ℕ) : Expr :=
  .letE (.call comp (mk2 (.get (arg 0) (.nat 1)) (arg 2)))
    (.ite (.call ab (mk2 (mk2 (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.var 1)) (arg 1)))
      (arg 1)
      (.snoc (arg 1) (.var 1)))


/-- The cost bound of the test, for lists of fewer than `L` entries. -/
noncomputable def tmRpTestC (hm : Membership) (Y L : ℕ) : ℕ :=
  L * tmRpPredC hm Y + 10 ^ 8 * (L * L * Y)

/-- The weight of a list of fewer than `L` permutations, for `Y ≥ (m + 1)⁴`. -/
theorem tmRp_wt_reps {Y L : ℕ} (hY : (m + 1) ^ 4 ≤ Y) (reps : List (Perm (Fin m)))
    (hL : reps.length < L) : (Val.list (reps.map encPerm)).wt ≤ 10 * (L * Y) := by
  have h1 : 1 ≤ (m + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h2 : (m + 1) ^ 2 ≤ (m + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have := wt_list_map_le reps encPerm (W := 4 * Y) fun r _ => (wt_encPerm_le r).trans (by omega)
  have h3 : reps.length * (2 * (4 * Y) + 1) ≤ (L - 1) * (9 * Y) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h4 : (L - 1) * (9 * Y) + 9 * Y = L * (9 * Y) := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
  have h5 : L * (9 * Y) + L * Y = 10 * (L * Y) := by ring
  have h6 : 1 ≤ L * Y := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  omega

/-- **The test of `y = r g`.** On a list `reps` of fewer than `L - 1` entries, the test gives
the list `tmRpAdd R (r g) reps`. -/
theorem tmRpTest_spec (hm : Membership) {P : Program} {gt ab pt jm comp inv : ℕ}
    (hgt : P.funs[gt]? = some (tmRpTestF ab comp))
    (hab : P.HasAt ab (anyFuns ab pt))
    (hpt : P.funs[pt]? = some (tmRpPredF jm comp inv))
    (hjm : P.prims[jm]? = some (membershipPrim hm))
    (hcomp : P.HasAt comp (composeFuns comp)) (hinv : P.HasAt inv (invFuns inv))
    {gR hl : Val} {R : Subgroup (Perm (Fin m))} (hR : GroupVal m gR R) {Y L : ℕ}
    (hY : (m + 1) ^ 4 ≤ Y) (hcY : (Val.list [gR, hl]).wt ≤ Y) (r g : Perm (Fin m))
    (reps : List (Perm (Fin m))) (hL : reps.length + 1 < L) :
    FunDet P gt (.list [.list [.list [gR, hl], encPerm r], .list (reps.map encPerm), encPerm g])
      (.list ((tmRpAdd R (r * g) reps).map encPerm)) (tmRpTestC hm Y L) := by
  have hgY : gR.wt ≤ Y := (wt_le_wt_list (by simp)).le.trans hcY
  have h1 : 1 ≤ (m + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h2 : (m + 1) ^ 2 ≤ (m + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : (m + 1) ^ 3 ≤ (m + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have wr := wt_encPerm_le r
  have wg := wt_encPerm_le g
  have wy := wt_encPerm_le (r * g)
  have wR := tmRp_wt_reps hY reps (show reps.length < L by omega)
  have wR' := tmRp_wt_reps hY (reps ++ [r * g]) (by simp; omega)
  set c := Val.list [gR, hl] with hc
  set acc := Val.list (reps.map encPerm) with hacc
  set vs : List Val := [.list [c, encPerm r], acc, encPerm g] with hvs
  have a1 := wt_list2_le c (encPerm r)
  have a2 := wt_list3_le (.list [c, encPerm r]) acc (encPerm g)
  have d0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) (v := .list [c, encPerm r]) rfl
  have d1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) (v := acc) rfl
  have d2 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) (v := encPerm g) rfl
  have dr := Det.get' d0 (Det.nat 1) (show [c, encPerm r][1]? = some (encPerm r) from rfl)
  have dy := Det.call (Det.mk2 dr d2) (compose_spec hcomp r g)
  set y := r * g with hy
  set ey := encPerm y with hey
  set vs2 : List Val := [.list vs, ey] with hvs2
  have e0 := Det.arg' (P := P) (vs := vs) (rest := [ey]) (j := 0) (v := .list [c, encPerm r]) rfl
  have e1 := Det.arg' (P := P) (vs := vs) (rest := [ey]) (j := 1) (v := acc) rfl
  have eg := Det.get' (Det.get' e0 (Det.nat 0) (show [c, encPerm r][0]? = some c from rfl))
    (Det.nat 0) (show [gR, hl][0]? = some gR from rfl)
  have ev := Det.var' (P := P) (env := Val.list vs :: [ey]) (i := 1) (v := ey) rfl
  have hany := any_spec hab (c := .list [gR, ey]) (xs := reps.map encPerm) (q := tmRpB R y)
    (B := fun _ => tmRpPredC hm Y) (fun x hx => by
      obtain ⟨r', -, rfl⟩ := List.mem_map.1 hx
      exact tmRpPred_spec hm hpt hjm hcomp hinv hR hY hgY y r')
  have dany := Det.call (Det.mk2 (Det.mk2 eg ev) e1) (hany.mono fun w c h => h)
  have dite := Det.ite' dany e1 (Det.snoc e1 ev)
  have hval : (if (Bool.toNat ((reps.map encPerm).any (tmRpB R y)) = 0) then
      Val.list (reps.map encPerm ++ [ey]) else acc) =
      .list ((tmRpAdd R y reps).map encPerm) := by
    by_cases hcov : TmRpCov R reps y
    · rw [tmRpAdd_of_cov hcov]
      have : (reps.map encPerm).any (tmRpB R y) = true := by
        obtain ⟨r', hr', h⟩ := hcov
        exact List.any_eq_true.2 ⟨encPerm r', List.mem_map_of_mem hr', (tmRpB_encPerm R y r').2 h⟩
      rw [this]; rfl
    · rw [tmRpAdd_of_not_cov hcov]
      have : (reps.map encPerm).any (tmRpB R y) = false := by
        rw [Bool.eq_false_iff]
        intro ha
        obtain ⟨x, hx, hq⟩ := List.any_eq_true.1 ha
        obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hx
        exact hcov ⟨r', hr', (tmRpB_encPerm R y r').1 hq⟩
      rw [this, List.map_append]; rfl
  rw [hval] at dite
  refine FunDet.intro hgt ((Det.letE dy dite).mono ?_)
  clear dite dany hany hval
  have hlen : (reps.map encPerm).length = reps.length := List.length_map _
  have hsum : ((reps.map encPerm).map fun _ => tmRpPredC hm Y).sum =
      reps.length * tmRpPredC hm Y := by rw [tm_sum_map_const, hlen]
  rw [hsum, hlen]
  have wadd := wt_list_snoc_le (reps.map encPerm) ey
  have b1 := wt_list2_le gR ey
  have b2 := wt_list2_le (.list [gR, ey]) acc
  have b3 := wt_list2_le (encPerm r) (encPerm g)
  have wA : (Val.list ((tmRpAdd R y reps).map encPerm)).wt ≤ 10 * (L * Y) := by
    by_cases hcov : TmRpCov R reps y
    · rw [tmRpAdd_of_cov hcov]; exact wR
    · rw [tmRpAdd_of_not_cov hcov]; exact wR'
  have eV : (Val.list vs).wt = (Val.list [.list [c, encPerm r], acc, encPerm g]).wt := rfl
  have hLY : L ≤ L * Y := Nat.le_mul_of_pos_right _ (by omega)
  have hYLY : Y ≤ L * Y := Nat.le_mul_of_pos_left _ (by omega)
  have eacc : acc.wt = (Val.list (reps.map encPerm)).wt := rfl
  have hLL : L * Y ≤ L * L * Y := by
    rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hlen2 : reps.length * tmRpPredC hm Y ≤ L * tmRpPredC hm Y := Nat.mul_le_mul_right _ (by omega)
  have eB : (Val.list [Val.list [gR, ey], acc]).wt =
      (Val.list [Val.list [gR, ey], Val.list (List.map encPerm reps)]).wt := rfl
  have hlp : loopModK * (reps.length + 1) * ((Val.list [Val.list [gR, ey],
      Val.list (List.map encPerm reps)]).wt + reps.length + 4) ≤ 10 ^ 5 * (L * L * Y) := by
    have : (reps.length + 1) * ((Val.list [Val.list [gR, ey], Val.list (List.map encPerm reps)]).wt
        + reps.length + 4) ≤
        L * (80 * (L * Y)) := Nat.mul_le_mul (by omega) (by omega)
    have e : L * (80 * (L * Y)) = 80 * (L * L * Y) := by ring
    simp only [loopModK]
    nlinarith
  have hb := wt_boolVal_le ((List.map encPerm reps).any (tmRpB R y))
  have hM1 : ∀ a b : ℕ, max a b ≤ a + b := fun a b => max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  have m1 := hM1 (2 * (Val.list vs).wt + 1 + 5)
    (2 * (Val.list vs).wt + 1 + 5 + (ey.wt + 1) + (Val.list (List.map encPerm reps ++ [ey])).wt + 1)
  have m2 := hM1 acc.wt (Val.list (List.map encPerm reps ++ [ey])).wt
  have hpm : permK * (m + 1) ^ 3 ≤ permK * Y := Nat.mul_le_mul_left _ (by omega)
  unfold tmRpTestC
  simp only [permK] at hpm
  have ec : (Val.list [gR, hl]).wt = c.wt := rfl
  generalize max (2 * (Val.list vs).wt + 1 + 5)
    (2 * (Val.list vs).wt + 1 + 5 + (ey.wt + 1) + (Val.list (List.map encPerm reps ++ [ey])).wt + 1) = M1 at m1 ⊢
  generalize max acc.wt (Val.list (List.map encPerm reps ++ [ey])).wt = M2 at m2 ⊢
  simp only [permK]
  omega

/-- **One round**, on `[c, i, acc]`: fold the test over the generators with `r = acc[i]`. -/
def tmRpStepF (fb : ℕ) : Expr :=
  .call fb (mk3 (mk2 (arg 0) (.get (arg 2) (arg 1))) (.get (arg 0) (.nat 1)) (arg 2))

/-- The cost bound of one round. -/
noncomputable def tmRpRoundC (hm : Membership) (Y L : ℕ) : ℕ :=
  Y * tmRpTestC hm Y L + 10 ^ 7 * (Y * (L * Y))

/-- Where the functions of the rounds sit. -/
structure TmRpRoundAt (P : Program) (hm : Membership) (st fb gt ab pt jm comp inv : ℕ) :
    Prop where
  step : P.funs[st]? = some (tmRpStepF fb)
  fold : P.HasAt fb (foldlFuns fb gt)
  test : P.funs[gt]? = some (tmRpTestF ab comp)
  any : P.HasAt ab (anyFuns ab pt)
  pred : P.funs[pt]? = some (tmRpPredF jm comp inv)
  mem : P.prims[jm]? = some (membershipPrim hm)
  comp : P.HasAt comp (composeFuns comp)
  inv : P.HasAt inv (invFuns inv)

/-- **One round.** With `reps` in `H` with distinct cosets of `R ≤ H`, and `L = [H : R] + 2`,
the round on `r = reps[i]` gives `tmRpProc R r gs reps`. -/
theorem tmRpStep_spec (hm : Membership) {P : Program} {st fb gt ab pt jm comp inv : ℕ}
    (h : TmRpRoundAt P hm st fb gt ab pt jm comp inv)
    {gR : Val} {H R : Subgroup (Perm (Fin m))} (hR : GroupVal m gR R) {gs : List (Perm (Fin m))}
    (hgs : ∀ g ∈ gs, g ∈ H) {Y : ℕ} (hY : (m + 1) ^ 4 ≤ Y)
    (hcY : (Val.list [gR, .list (gs.map encPerm)]).wt ≤ Y)
    (reps : List (Perm (Fin m))) (hsub : ∀ r ∈ reps, r ∈ H)
    (hd : reps.Pairwise (fun a b => a * b⁻¹ ∉ R)) (i : ℕ) (hi : i < reps.length) :
    FunDet P st (.list [.list [gR, .list (gs.map encPerm)], .nat i, .list (reps.map encPerm)])
      (.list ((tmRpProc R reps[i] gs reps).map encPerm))
      (tmRpRoundC hm Y ((R.subgroupOf H).index + 2)) := by
  set L := (R.subgroupOf H).index + 2 with hLdef
  set c := Val.list [gR, .list (gs.map encPerm)] with hc
  set r := reps[i] with hr
  have hrH : r ∈ H := hsub _ (List.getElem_mem hi)
  have h1 : 1 ≤ (m + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h2 : (m + 1) ^ 2 ≤ (m + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  -- the lists along the fold
  have hlen : ∀ j, (tmRpProc R r (gs.take j) reps).length + 1 < L := by
    intro j
    have hs := tmRpProc_sub (R := R) hrH (gs := gs.take j)
      (fun g hg => hgs g (List.mem_of_mem_take hg)) hsub
    have := tmRp_len_le hs (tmRpProc_distinct r _ hd)
    omega
  have hxs : ∀ j (hj : j < (gs.map encPerm).length), (gs.map encPerm)[j] = encPerm (gs[j]'(by simpa using hj)) :=
    fun j hj => List.getElem_map _
  have hfold := foldl_spec h.fold (c := .list [c, encPerm r]) (xs := gs.map encPerm)
    (acc0 := .list (reps.map encPerm)) (M := 10 * (L * Y)) (B := fun _ => tmRpTestC hm Y L)
    (Inv := fun j acc => acc = .list ((tmRpProc R r (gs.take j) reps).map encPerm))
    (by simp [tmRpProc]) (fun j acc _ hacc => by
      rw [hacc]; exact tmRp_wt_reps hY _ (by have := hlen j; omega))
    (fun j acc hj hacc => by
      rw [hacc, hxs j hj]
      have hj' : j < gs.length := by simpa using hj
      refine FunAll.mono (tmRpTest_spec hm h.test h.any h.pred h.mem h.comp h.inv hR hY hcY r gs[j] _
        (hlen j)) fun w cost hw => ⟨?_, hw.2⟩
      show _ = _
      rw [hw.1, tmRpProc_take_succ r gs reps hj'])
  simp only [List.length_map, List.take_length] at hfold
  set vs : List Val := [c, .nat i, .list (reps.map encPerm)] with hvs
  have d0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) (v := c) rfl
  have d1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) (v := .nat i) rfl
  have d2 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) (v := .list (reps.map encPerm)) rfl
  have dr := Det.get' d2 d1 (v := encPerm r) (by simp [hr, hi])
  have dh := Det.get' d0 (Det.nat 1)
    (show [gR, Val.list (gs.map encPerm)][1]? = some (.list (gs.map encPerm)) from rfl)
  have da := Det.mk3 (Det.mk2 d0 dr) dh d2
  refine FunDet.intro h.step ((Det.call da (hfold.mono fun w c hw => hw)).mono ?_)
  clear da dr dh d0 d1 d2 hfold
  have wr := wt_encPerm_le r
  have wreps := tmRp_wt_reps hY reps (show reps.length < L by have := hlen 0; simp [tmRpProc] at this; omega)
  have wres := tmRp_wt_reps hY (tmRpProc R r gs reps)
    (show _ < L by have := hlen gs.length; rw [List.take_length] at this; omega)
  have hgsl := length_lt_wt_list (gs.map encPerm)
  have hgw : (Val.list (gs.map encPerm)).wt < c.wt := wt_le_wt_list (by simp)
  simp only [List.length_map] at hgsl
  have a1 := wt_list2_le c (encPerm r)
  have a2 := wt_list3_le (.list [c, encPerm r]) (.list (gs.map encPerm)) (.list (reps.map encPerm))
  have a3 := wt_list3_le c (.nat i) (.list (reps.map encPerm))
  have hni := wt_nat_le i
  have hiL : i < L := by have := hlen 0; simp [tmRpProc] at this; omega
  have hLY : L ≤ L * Y := Nat.le_mul_of_pos_right _ (by omega)
  have hYLY : Y ≤ L * Y := Nat.le_mul_of_pos_left _ (by omega)
  have hsum : (Finset.range gs.length).sum (fun _ => tmRpTestC hm Y L) ≤ Y * tmRpTestC hm Y L := by
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    exact Nat.mul_le_mul_right _ (by omega)
  have hlp : loopModK * (gs.length + 1) * ((Val.list [Val.list [c, encPerm r],
      Val.list (gs.map encPerm), Val.list (reps.map encPerm)]).wt + gs.length + 10 * (L * Y) + 1)
      ≤ 10 ^ 6 * (Y * (L * Y)) := by
    have : (gs.length + 1) * ((Val.list [Val.list [c, encPerm r],
        Val.list (gs.map encPerm), Val.list (reps.map encPerm)]).wt + gs.length + 10 * (L * Y) + 1)
        ≤ (2 * Y) * (100 * (L * Y)) := Nat.mul_le_mul (by omega) (by omega)
    have e : (2 * Y) * (100 * (L * Y)) = 200 * (Y * (L * Y)) := by ring
    simp only [loopModK]
    nlinarith
  have hYY : L * Y ≤ Y * (L * Y) := Nat.le_mul_of_pos_left _ (by omega)
  have ec : (Val.list [gR, .list (gs.map encPerm)]).wt = c.wt := rfl
  have ev : (Val.list vs).wt = (Val.list [c, .nat i, .list (reps.map encPerm)]).wt := rfl
  unfold tmRpRoundC
  omega

/-- **The coset enumeration.** From the list `[1]`, the loop of the rounds ends with a list
`reps` that satisfies the invariant with every entry processed. -/
theorem tmRpLoop_spec (hm : Membership) {P : Program} {wh st fb gt ab pt jm comp inv : ℕ}
    (hwh : P.funs[wh]? = some (tmRpWhileF wh st))
    (h : TmRpRoundAt P hm st fb gt ab pt jm comp inv)
    {gR : Val} {H R : Subgroup (Perm (Fin m))} (hR : GroupVal m gR R) {gs : List (Perm (Fin m))}
    (hgs : ∀ g ∈ gs, g ∈ H) {Y : ℕ} (hY : (m + 1) ^ 4 ≤ Y)
    (hcY : (Val.list [gR, .list (gs.map encPerm)]).wt ≤ Y) :
    FunAll P wh (.list [.list [gR, .list (gs.map encPerm)], .nat 0, .list [encPerm (1 : Perm (Fin m))]])
      (fun w cost => ∃ reps : List (Perm (Fin m)), w = .list (reps.map encPerm) ∧
        (∃ j, TmRpInv H R gs j reps ∧ reps.length ≤ j) ∧
        cost ≤ ((R.subgroupOf H).index + 1) *
          (tmRpRoundC hm Y ((R.subgroupOf H).index + 2) + tmRpWK * (Y +
            (R.subgroupOf H).index + 10 * (((R.subgroupOf H).index + 2) * Y) + 10))) := by
  have := tmRpWhile_spec hwh (c := .list [gR, .list (gs.map encPerm)])
    (Inv := fun i l => ∃ reps : List (Perm (Fin m)), l = reps.map encPerm ∧ TmRpInv H R gs i reps)
    (K := (R.subgroupOf H).index) (M := 10 * (((R.subgroupOf H).index + 2) * Y))
    (D := tmRpRoundC hm Y ((R.subgroupOf H).index + 2))
    (fun i l ⟨reps, hl, hinv⟩ => by
      subst hl; simp only [List.length_map]; exact ⟨hinv.le, hinv.length_le⟩)
    (fun i l ⟨reps, hl, hinv⟩ => by
      subst hl; exact tmRp_wt_reps hY reps (by have := hinv.length_le; omega))
    (fun i l ⟨reps, hl, hinv⟩ hi => by
      subst hl
      simp only [List.length_map] at hi
      refine FunAll.mono (tmRpStep_spec hm h hR hgs hY hcY reps hinv.sub hinv.distinct i hi)
        fun w cb hw => ⟨_, hw.1, ⟨_, rfl, tmRpInv_step hgs hinv hi⟩, hw.2⟩)
    0 [encPerm (1 : Perm (Fin m))] ⟨[1], rfl, tmRpInv_start H R gs⟩
  refine this.mono fun w cost ⟨j, l, hw, ⟨reps, hl, hinv⟩, hlj, hc⟩ => ⟨reps, by rw [hw, hl],
    ⟨j, hinv, by rw [hl, List.length_map] at hlj; exact hlj⟩, ?_⟩
  refine hc.trans (Nat.mul_le_mul (by omega) (Nat.add_le_add_left
    (Nat.mul_le_mul_left _ (by omega)) _))

end GI.Impl
