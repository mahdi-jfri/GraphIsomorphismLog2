module

public import Workspace.OutbRebMath
public import Workspace.Impl.TermRepsStep
public import Workspace.Impl.TermCosetLink
public import Workspace.Impl.TermCosetRel

@[expose] public section

/-!
# Rebasing a coset table into a subgroup (the program)

Given `R = ⟨hsR⟩ ≤ H`, `r ∈ H`, and the table `vs` of canonical answers for `Iso_H(x_i, y_j)`,
`outbRebTabF` computes the table `vs'` of canonical answers for `Iso_R(x_i, y_j^{r⁻¹})`.

For each entry `v = vs[i q + j]`:
* if `v = []`, the entry is `[]`;
* if `v = [g, ⟨gs⟩]`, we conjugate `1 :: gs` by `r` (`mp_conj`), enumerate right coset
  representatives `reps` of `R ∩ K'` in `K' = r ⟨gs⟩ r⁻¹` (`tmRpWhileF`), test whether
  `y₀ = g r⁻¹` has a representative `s ∈ reps` with `y₀ s⁻¹ ∈ R` (`findFuns`), and when it does,
  set `u₀ = y₀ s⁻¹`, collect the Schreier generators of `K' ∩ R` (`outbSchGenF`, `outbSchRowF`,
  `foldlFuns`), reduce them to at most `m²` generators (`redFuns`), and return `[u₀, ⟨hs⟩]`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Multicoset Equiv
open GI.Machine (BinOp)
open GI.Cited (Val encPerm encPerms encGroup gens PointwiseStab Membership)

variable {m : ℕ}

/-! ### `findIdx` on encoded representatives -/

theorem outbReb_findIdx_congr {α : Type*} {p q : α → Bool} :
    ∀ {xs : List α}, (∀ x ∈ xs, p x = q x) → xs.findIdx p = xs.findIdx q
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.findIdx_cons, List.findIdx_cons, h x List.mem_cons_self,
      outbReb_findIdx_congr fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem outbReb_findIdx_map (R : Subgroup (Perm (Fin m))) (reps : List (Perm (Fin m)))
    (x : Perm (Fin m)) :
    (reps.map encPerm).findIdx (tmRpB R x) = outbRebIdx R reps x := by
  classical
  unfold outbRebIdx
  rw [List.findIdx_map]
  refine outbReb_findIdx_congr fun s _ => ?_
  rw [Function.comp_apply, Bool.eq_iff_iff, tmRpB_encPerm, decide_eq_true_iff]

/-! ### Schreier generators of `K' ∩ R` -/

/-- On `[[[gR, reps], s], k']`: compute `x = s k'`, find the index `idx` of `s' ∈ reps` with
`x s'⁻¹ ∈ R`, and return `x (reps[idx])⁻¹`. -/
def outbSchGenF (fnd comp inv : ℕ) : Expr :=
  .letE (.call comp (mk2 (.get (arg 0) (.nat 1)) (arg 1)))
  (.letE (.call fnd (mk2 (mk2 (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.var 1))
      (.get (.get (arg 0) (.nat 0)) (.nat 1))))
  (.call comp (mk2 (.var 1) (.call inv (.get (.get (.get (arg 0) (.nat 0)) (.nat 1)) (.var 2))))))

/-- Cost bound for one Schreier generator. -/
noncomputable def outbSchGenC (hm : Membership) (Y L : ℕ) : ℕ :=
  tmRpTestC hm Y L + 10 ^ 7 * (L * Y)

/-- **One Schreier generator.** -/
theorem outbSchGen_spec (hm : Membership) {P : Program} {sgen fnd pt jm comp inv : ℕ}
    (hsgen : P.funs[sgen]? = some (outbSchGenF fnd comp inv))
    (hfnd : P.HasAt fnd (findFuns fnd pt))
    (hpt : P.funs[pt]? = some (tmRpPredF jm comp inv))
    (hjm : P.prims[jm]? = some (membershipPrim hm))
    (hcomp : P.HasAt comp (composeFuns comp)) (hinv : P.HasAt inv (invFuns inv))
    {gR : Val} {R : Subgroup (Perm (Fin m))} (hR : GroupVal m gR R) {Y L : ℕ}
    (hY : (m + 1) ^ 4 ≤ Y) (hgY : gR.wt ≤ Y)
    (reps : List (Perm (Fin m))) (hL : reps.length < L)
    (s k' : Perm (Fin m)) (hcov : TmRpCov R reps (s * k')) :
    FunDet P sgen
      (.list [.list [.list [gR, .list (reps.map encPerm)], encPerm s], encPerm k'])
      (encPerm (outbRebElem R reps (s * k'))) (outbSchGenC hm Y L) := by
  have h1 : 1 ≤ (m + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h2 : (m + 1) ^ 2 ≤ (m + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : (m + 1) ^ 3 ≤ (m + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  set c0 := Val.list [gR, .list (reps.map encPerm)] with hc0
  set c := Val.list [c0, encPerm s] with hc
  set x := s * k' with hx
  set idx := outbRebIdx R reps x with hidx
  have hlt : idx < reps.length := (outbRebIdx_lt_iff R reps x).2 hcov
  have hget : (reps.map encPerm)[idx]? = some (encPerm (reps[idx]'hlt)) := by simp [hlt]
  have hel : outbRebElem R reps x = x * (reps[idx]'hlt)⁻¹ := by
    unfold outbRebElem; rw [dif_pos hlt]
  have d0 := Det.arg' (P := P) (vs := [c, encPerm k']) (rest := []) (j := 0) (v := c) rfl
  have d1 := Det.arg' (P := P) (vs := [c, encPerm k']) (rest := []) (j := 1) (v := encPerm k') rfl
  have ds := Det.get' d0 (Det.nat 1) (vs := [c0, encPerm s]) (v := encPerm s) rfl
  have dx := Det.call (Det.mk2 ds d1) (compose_spec hcomp s k')
  set env1 := [Val.list [c, encPerm k'], encPerm x] with henv1
  have e0 := Det.arg' (P := P) (vs := [c, encPerm k']) (rest := [encPerm x]) (j := 0) (v := c) rfl
  have ec0 := Det.get' e0 (Det.nat 0) (vs := [c0, encPerm s]) (v := c0) rfl
  have egR := Det.get' ec0 (Det.nat 0) (vs := [gR, .list (reps.map encPerm)]) (v := gR) rfl
  have ereps := Det.get' ec0 (Det.nat 1) (vs := [gR, .list (reps.map encPerm)])
    (v := .list (reps.map encPerm)) rfl
  have e1 := Det.var' (P := P) (env := env1) (i := 1) (v := encPerm x) rfl
  have hfnd' := find_spec hfnd (c := .list [gR, encPerm x]) (xs := reps.map encPerm)
    (q := tmRpB R x) (B := fun _ => tmRpPredC hm Y) (fun v hv => by
      obtain ⟨r', -, rfl⟩ := List.mem_map.1 hv
      exact tmRpPred_spec hm hpt hjm hcomp hinv hR hY hgY x r')
  rw [outbReb_findIdx_map] at hfnd'
  have dfnd := Det.call (Det.mk2 (Det.mk2 egR e1) ereps) (hfnd'.mono fun w cw hw => hw)
  set env2 := env1 ++ [.nat idx] with henv2
  have f0 := Det.arg' (P := P) (vs := [c, encPerm k']) (rest := [encPerm x, .nat idx]) (j := 0)
    (v := c) rfl
  have fc0 := Det.get' f0 (Det.nat 0) (vs := [c0, encPerm s]) (v := c0) rfl
  have freps := Det.get' fc0 (Det.nat 1) (vs := [gR, .list (reps.map encPerm)])
    (v := .list (reps.map encPerm)) rfl
  have f1 := Det.var' (P := P) (env := env2) (i := 1) (v := encPerm x) rfl
  have f2 := Det.var' (P := P) (env := env2) (i := 2) (v := .nat idx) rfl
  have fs' := Det.get' freps f2 hget
  have finv := Det.call fs' (inv_spec hinv (reps[idx]'hlt))
  have fcomp := Det.call (Det.mk2 f1 finv) (compose_spec hcomp x (reps[idx]'hlt)⁻¹)
  rw [← hel] at fcomp
  refine FunDet.intro hsgen ((Det.letE dx (Det.letE dfnd fcomp)).mono ?_)
  clear fcomp finv fs' f2 f1 freps fc0 f0 dfnd hfnd' e1 ereps egR ec0 e0 dx ds d1 d0
  have hlen : (reps.map encPerm).length = reps.length := List.length_map _
  have hsum : ((reps.map encPerm).map fun _ => tmRpPredC hm Y).sum =
      reps.length * tmRpPredC hm Y := by rw [tm_sum_map_const, hlen]
  rw [hsum, hlen]
  have wreps := tmRp_wt_reps hY reps hL
  have ws := wt_encPerm_le s
  have wk' := wt_encPerm_le k'
  have wx := wt_encPerm_le x
  have ws' := wt_encPerm_le (reps[idx]'hlt)
  have wsi := wt_encPerm_le (reps[idx]'hlt)⁻¹
  have wel := wt_encPerm_le (outbRebElem R reps x)
  have widx := wt_nat_le idx
  have wc0 := wt_list2_le gR (.list (reps.map encPerm))
  have wc := wt_list2_le c0 (encPerm s)
  have wa := wt_list2_le c (encPerm k')
  have w1 := wt_list2_le (encPerm s) (encPerm k')
  have w2 := wt_list2_le gR (encPerm x)
  have w3 := wt_list2_le (.list [gR, encPerm x]) (.list (reps.map encPerm))
  have w4 := wt_list2_le (encPerm x) (encPerm (reps[idx]'hlt)⁻¹)
  rw [← hc0] at wc0; rw [← hc] at wc; rw [← hx, ← hidx]
  have hLY : L ≤ L * Y := Nat.le_mul_of_pos_right _ (by omega)
  have hYLY : Y ≤ L * Y := Nat.le_mul_of_pos_left _ (by omega)
  have hLL : L * Y ≤ L * L * Y := by
    rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hlen2 : reps.length * tmRpPredC hm Y ≤ L * tmRpPredC hm Y :=
    Nat.mul_le_mul_right _ (by omega)
  have hlp : loopModK * (reps.length + 1) *
      ((Val.list [Val.list [gR, encPerm x], Val.list (List.map encPerm reps)]).wt +
        2 * reps.length + 3) ≤ 10 ^ 5 * (L * L * Y) := by
    have : (reps.length + 1) *
        ((Val.list [Val.list [gR, encPerm x], Val.list (List.map encPerm reps)]).wt +
          2 * reps.length + 3) ≤ L * (80 * (L * Y)) := Nat.mul_le_mul (by omega) (by omega)
    have e : L * (80 * (L * Y)) = 80 * (L * L * Y) := by ring
    simp only [loopModK]
    nlinarith
  have hpm : permK * (m + 1) ^ 3 ≤ permK * Y := Nat.mul_le_mul_left _ (by omega)
  have hinvK : invK * (m + 1) ^ 3 ≤ invK * Y := Nat.mul_le_mul_left _ (by omega)
  unfold outbSchGenC tmRpTestC
  simp only [permK, invK] at hpm hinvK ⊢
  omega

/-- On `[[[gR, reps], σ], acc, s]`: append the row `outbSchreierRow R reps σ s` to `acc`. -/
def outbSchRowF (mg app : ℕ) : Expr :=
  .call app (mk2 (arg 1) (.call mg (mk2 (mk2 (.get (arg 0) (.nat 0)) (arg 2)) (.get (arg 0) (.nat 1)))))

/-- Cost bound for one row of Schreier generators. -/
noncomputable def outbSchRowC (hm : Membership) (Y L : ℕ) : ℕ :=
  Y * outbSchGenC hm Y L + 10 ^ 8 * (Y * (Y * (L * Y)))

/-- **One row of Schreier generators.** -/
theorem outbSchRow_spec (hm : Membership) {P : Program} {srow mg sgen app fnd pt jm comp inv : ℕ}
    (hsrow : P.funs[srow]? = some (outbSchRowF mg app))
    (hmg : P.HasAt mg (mapFuns mg sgen))
    (hsgen : P.funs[sgen]? = some (outbSchGenF fnd comp inv))
    (happ : P.HasAt app (appendFuns app))
    (hfnd : P.HasAt fnd (findFuns fnd pt))
    (hpt : P.funs[pt]? = some (tmRpPredF jm comp inv))
    (hjm : P.prims[jm]? = some (membershipPrim hm))
    (hcomp : P.HasAt comp (composeFuns comp)) (hinv : P.HasAt inv (invFuns inv))
    {gR : Val} {R : Subgroup (Perm (Fin m))} (hR : GroupVal m gR R) {Y L : ℕ}
    (hY : (m + 1) ^ 4 ≤ Y) (hgY : gR.wt ≤ Y)
    (reps : List (Perm (Fin m))) (hL : reps.length < L)
    (σ : List (Perm (Fin m))) (hσ : σ.length < Y)
    (prev : List (Perm (Fin m))) (hprev : prev.length + σ.length < L * Y)
    (s : Perm (Fin m)) (hcov : ∀ k' ∈ σ, TmRpCov R reps (s * k')) :
    FunDet P srow
      (.list [.list [.list [gR, .list (reps.map encPerm)], .list (σ.map encPerm)],
        .list (prev.map encPerm), encPerm s])
      (.list ((prev ++ outbSchreierRow R reps σ s).map encPerm))
      (outbSchRowC hm Y L) := by
  have h1 : 1 ≤ (m + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h2 : (m + 1) ^ 2 ≤ (m + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  set c0 := Val.list [gR, .list (reps.map encPerm)] with hc0
  set c1 := Val.list [c0, .list (σ.map encPerm)] with hc1
  set row := outbSchreierRow R reps σ s with hrow
  have hM := map_spec hmg (c := .list [c0, encPerm s]) (xs := σ.map encPerm)
    (R := fun v w => ∀ k' : Perm (Fin m), v = encPerm k' → w = encPerm (outbRebElem R reps (s * k')))
    (B := fun _ => outbSchGenC hm Y L) (by
      intro v hv
      obtain ⟨k', hk', rfl⟩ := List.mem_map.1 hv
      refine FunAll.mono (outbSchGen_spec hm hsgen hfnd hpt hjm hcomp hinv hR hY hgY reps hL s k'
        (hcov k' hk')) fun w cost hw => ⟨fun k'' hk'' => ?_, hw.2⟩
      rw [hw.1, encPerm_injective hk''])
  have hws : ∀ ws', List.Forall₂ (fun v w => ∀ k' : Perm (Fin m), v = encPerm k' →
      w = encPerm (outbRebElem R reps (s * k'))) (σ.map encPerm) ws' → ws' = row.map encPerm := by
    intro ws' h
    have := forall₂_map_eq (g := fun k' => encPerm (outbRebElem R reps (s * k')))
      (fun a _ w hw => hw a rfl) h
    rw [this, hrow, outbSchreierRow, List.map_map]
    rfl
  have wreps := tmRp_wt_reps hY reps hL
  have wσ := tmRp_wt_reps hY σ (L := Y) hσ
  have wrow := tmRp_wt_reps hY row (L := Y) (by simp [hrow, outbSchreierRow, hσ])
  have wprev := tmRp_wt_reps hY prev (L := L * Y) (by omega)
  have wapp := tmRp_wt_reps hY (prev ++ row) (L := L * Y) (by
    rw [List.length_append, hrow, outbSchreierRow, List.length_map]; exact hprev)
  have e_n : (L * Y) * Y = Y * (L * Y) := by ring
  rw [e_n] at wprev wapp
  have hYY : Y * Y ≤ Y * (L * Y) := by
    rw [← e_n]; exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (by omega))
  have hLY_YLY : L * Y ≤ Y * (L * Y) := Nat.le_mul_of_pos_left _ (by omega)
  have ws := wt_encPerm_le s
  have wc0 := wt_list2_le gR (.list (reps.map encPerm))
  have wc1 := wt_list2_le c0 (.list (σ.map encPerm))
  have wcs := wt_list2_le c0 (encPerm s)
  have wmc := wt_list2_le (.list [c0, encPerm s]) (.list (σ.map encPerm))
  rw [← hc0] at wc0; rw [← hc1] at wc1
  have hLY : L ≤ L * Y := Nat.le_mul_of_pos_right _ (by omega)
  have hYLY : Y ≤ L * Y := Nat.le_mul_of_pos_left _ (by omega)
  have h1_YLY : 1 ≤ Y * (L * Y) := Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))
  have hY_YYLY : Y * (L * Y) ≤ Y * (Y * (L * Y)) := Nat.le_mul_of_pos_left _ (by omega)
  have hsum : (((σ.map encPerm).map fun _ => outbSchGenC hm Y L).sum) ≤
      Y * outbSchGenC hm Y L := by
    rw [tm_sum_map_const, List.length_map]
    exact Nat.mul_le_mul_right _ (by omega)
  have hmloop : mapK * ((σ.map encPerm).length + 1) *
      ((Val.list [.list [c0, encPerm s], .list (σ.map encPerm)]).wt +
        (Val.list (row.map encPerm)).wt + 1) ≤ 10 ^ 6 * (Y * (Y * (L * Y))) := by
    rw [List.length_map]
    have hwt : (Val.list [.list [c0, encPerm s], .list (σ.map encPerm)]).wt +
        (Val.list (row.map encPerm)).wt + 1 ≤ 300 * (Y * (L * Y)) := by omega
    have h1' : (σ.length + 1) * ((Val.list [.list [c0, encPerm s], .list (σ.map encPerm)]).wt +
        (Val.list (row.map encPerm)).wt + 1) ≤ Y * (300 * (Y * (L * Y))) :=
      Nat.mul_le_mul (by omega) hwt
    have e : Y * (300 * (Y * (L * Y))) = 300 * (Y * (Y * (L * Y))) := by ring
    rw [e] at h1'; rw [Nat.mul_assoc]; simp only [mapK]; omega
  have hMd : FunDet P mg (.list [.list [c0, encPerm s], .list (σ.map encPerm)])
      (.list (row.map encPerm)) (Y * outbSchGenC hm Y L + 10 ^ 6 * (Y * (Y * (L * Y)))) := by
    refine FunAll.mono hM fun w cost ⟨ws', hw, h2, hcost⟩ => ?_
    have := hws ws' h2; subst this; subst hw
    exact ⟨rfl, by omega⟩
  set vs : List Val := [c1, .list (prev.map encPerm), encPerm s] with hvs
  have d0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) (v := c1) rfl
  have d1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) (v := .list (prev.map encPerm)) rfl
  have d2 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) (v := encPerm s) rfl
  have dc0 := Det.get' d0 (Det.nat 0) (vs := [c0, .list (σ.map encPerm)]) (v := c0) rfl
  have dσ := Det.get' d0 (Det.nat 1) (vs := [c0, .list (σ.map encPerm)])
    (v := .list (σ.map encPerm)) rfl
  have dmg := Det.call (Det.mk2 (Det.mk2 dc0 d2) dσ) hMd
  have happ' : FunDet P app (.list [.list (prev.map encPerm), .list (row.map encPerm)])
      (.list ((prev ++ row).map encPerm))
      (loopModK * ((row.map encPerm).length + 1) *
        ((Val.list [.list (prev.map encPerm), .list (row.map encPerm)]).wt +
          (row.map encPerm).length + (Val.list ((prev ++ row).map encPerm)).wt + 1)) := by
    rw [List.map_append]
    exact (append_spec happ _ _).mono fun w c' ⟨h1, h2⟩ => ⟨h1, by rw [h1] at h2; exact h2⟩
  have dapp := Det.call (Det.mk2 d1 dmg) happ'
  refine FunDet.intro hsrow (dapp.mono ?_)
  clear dapp happ' dmg dσ dc0 d2 d1 d0 hMd hM
  have wpr := wt_list2_le (.list (prev.map encPerm)) (.list (row.map encPerm))
  have wvs := wt_list3_le c1 (.list (prev.map encPerm)) (encPerm s)
  rw [← hvs] at wvs
  have hrowl : (row.map encPerm).length = σ.length := by
    simp [hrow, outbSchreierRow]
  rw [hrowl]
  have haloop : loopModK * (σ.length + 1) *
      ((Val.list [Val.list (List.map encPerm prev), Val.list (List.map encPerm row)]).wt +
        σ.length + (Val.list (List.map encPerm (prev ++ row))).wt + 1) ≤
      10 ^ 7 * (Y * (Y * (L * Y))) := by
    have hwt_pr : (Val.list [Val.list (List.map encPerm prev), Val.list (List.map encPerm row)]).wt +
        σ.length + (Val.list (List.map encPerm (prev ++ row))).wt + 1 ≤
        100 * (Y * (L * Y)) := by omega
    have h1' : (σ.length + 1) *
        ((Val.list [Val.list (List.map encPerm prev), Val.list (List.map encPerm row)]).wt +
          σ.length + (Val.list (List.map encPerm (prev ++ row))).wt + 1) ≤
        Y * (100 * (Y * (L * Y))) := Nat.mul_le_mul (by omega) hwt_pr
    have e : Y * (100 * (Y * (L * Y))) = 100 * (Y * (Y * (L * Y))) := by ring
    simp only [loopModK]; nlinarith
  unfold outbSchRowC
  omega

/-- Cost bound for folding the Schreier generator rows over `reps`. -/
noncomputable def outbSchFoldC (hm : Membership) (Y L : ℕ) : ℕ :=
  L * outbSchRowC hm Y L + 10 ^ 8 * (L * (L * Y * Y))

/-- Where the functions of the Schreier generator fold sit. -/
structure OutbSchAt (P : Program) (hm : Membership)
    (fb_sch srow mg sgen app fnd pt jm comp inv : ℕ) : Prop where
  hfb_sch : P.HasAt fb_sch (foldlFuns fb_sch srow)
  hsrow : P.funs[srow]? = some (outbSchRowF mg app)
  hmg : P.HasAt mg (mapFuns mg sgen)
  hsgen : P.funs[sgen]? = some (outbSchGenF fnd comp inv)
  happ : P.HasAt app (appendFuns app)
  hfnd : P.HasAt fnd (findFuns fnd pt)
  hpt : P.funs[pt]? = some (tmRpPredF jm comp inv)
  hjm : P.prims[jm]? = some (membershipPrim hm)
  hcomp : P.HasAt comp (composeFuns comp)
  hinv : P.HasAt inv (invFuns inv)

/-- **All Schreier generators across `reps` and `σ`.** -/
theorem outbSchFold_spec (hm : Membership) {P : Program}
    {fb_sch srow mg sgen app fnd pt jm comp inv : ℕ}
    (h : OutbSchAt P hm fb_sch srow mg sgen app fnd pt jm comp inv)
    {gR : Val} {R : Subgroup (Perm (Fin m))} (hR : GroupVal m gR R) {Y L : ℕ}
    (hY : (m + 1) ^ 4 ≤ Y) (hgY : gR.wt ≤ Y)
    (reps : List (Perm (Fin m))) (hL : reps.length + 1 < L)
    (σ : List (Perm (Fin m))) (hσ : σ.length + 1 < Y)
    (hcov : ∀ s ∈ reps, ∀ k' ∈ σ, TmRpCov R reps (s * k')) :
    FunDet P fb_sch
      (.list [.list [.list [gR, .list (reps.map encPerm)], .list (σ.map encPerm)],
        .list (reps.map encPerm), .list [encPerm (1 : Perm (Fin m))]])
      (.list ((1 :: outbSchreierGens R reps σ).map encPerm))
      (outbSchFoldC hm Y L) := by
  have h1 : 1 ≤ (m + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h2 : (m + 1) ^ 2 ≤ (m + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  set c0 := Val.list [gR, .list (reps.map encPerm)] with hc0
  set c1 := Val.list [c0, .list (σ.map encPerm)] with hc1
  have hlen_take : ∀ i ≤ reps.length,
      ((reps.take i).foldl (fun acc s => acc ++ outbSchreierRow R reps σ s) [1]).length +
        σ.length < L * Y := by
    intro i hi
    rw [length_foldl_append (outbSchreierRow R reps σ) σ.length
      (fun _ => by unfold outbSchreierRow; exact List.length_map _),
      List.length_singleton, List.length_take, Nat.min_eq_left hi]
    have : (i + 1) * (σ.length + 1) ≤ (L - 1) * Y := Nat.mul_le_mul (by omega) (by omega)
    have hLY : (L - 1) * Y + Y = L * Y := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
    nlinarith
  have hfold := foldl_spec h.hfb_sch (c := c1) (xs := reps.map encPerm)
    (acc0 := .list [encPerm (1 : Perm (Fin m))]) (M := 10 * (L * Y * Y))
    (B := fun _ => outbSchRowC hm Y L)
    (Inv := fun i acc => acc = .list (((reps.take i).foldl
      (fun a s => a ++ outbSchreierRow R reps σ s) [1]).map encPerm))
    rfl
    (fun i acc hi hacc => by
      rw [List.length_map] at hi
      rw [hacc]
      have := tmRp_wt_reps hY ((reps.take i).foldl (fun a s => a ++ outbSchreierRow R reps σ s) [1])
        (L := L * Y) (by have := hlen_take i hi; omega)
      simpa [Nat.mul_assoc] using this)
    (fun i acc hi hacc => by
      have hi' : i < reps.length := by simpa using hi
      have hxs : (reps.map encPerm)[i] = encPerm (reps[i]'hi') := List.getElem_map _
      rw [hacc, hxs]
      refine FunAll.mono (outbSchRow_spec hm h.hsrow h.hmg h.hsgen h.happ h.hfnd h.hpt h.hjm
        h.hcomp h.hinv hR hY hgY reps (by omega) σ (by omega)
        ((reps.take i).foldl (fun a s => a ++ outbSchreierRow R reps σ s) [1])
        (hlen_take i hi'.le) (reps[i]'hi') (hcov _ (List.getElem_mem hi'))) fun w cost hw => ⟨?_, hw.2⟩
      show _ = _
      rw [hw.1, List.take_add_one, List.getElem?_eq_getElem hi', Option.toList_some,
        List.foldl_append]
      rfl)
  simp only [List.length_map, List.take_length, outbSchreierGens_init_one] at hfold
  refine hfold.mono fun w cost ⟨hw, hcost⟩ => ⟨hw, ?_⟩
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hcost
  have hsum : reps.length * outbSchRowC hm Y L ≤ L * outbSchRowC hm Y L :=
    Nat.mul_le_mul_right _ (by omega)
  have wreps := tmRp_wt_reps hY reps (L := L) (by omega)
  have wσ := tmRp_wt_reps hY σ (L := Y) (by omega)
  have w1 := wt_list1_le (encPerm (1 : Perm (Fin m)))
  have wp1 := wt_encPerm_le (1 : Perm (Fin m))
  have wc0 := wt_list2_le gR (.list (reps.map encPerm))
  have wc1 := wt_list2_le c0 (.list (σ.map encPerm))
  have wa := wt_list3_le c1 (.list (reps.map encPerm)) (.list [encPerm (1 : Perm (Fin m))])
  rw [← hc0] at wc0; rw [← hc1] at wc1
  have hLY : L ≤ L * Y * Y := by
    have : 1 ≤ Y * Y := Nat.mul_pos (by omega) (by omega)
    rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_right _ this
  have hYY : Y ≤ L * Y * Y := by
    have : 1 ≤ L * Y := Nat.mul_pos (by omega) (by omega)
    exact Nat.le_mul_of_pos_left _ this
  have hLYY : L * Y ≤ L * Y * Y := Nat.le_mul_of_pos_right _ (by omega)
  have hYY2 : Y * Y ≤ L * Y * Y := by
    rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hfloop : loopModK * (reps.length + 1) *
      ((Val.list [c1, Val.list (List.map encPerm reps), Val.list [encPerm (1 : Perm (Fin m))]]).wt +
        reps.length + 10 * (L * Y * Y) + 1) ≤ 10 ^ 8 * (L * (L * Y * Y)) := by
    have h1_LYY : 1 ≤ L * Y * Y := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    have hwt : (Val.list [c1, Val.list (List.map encPerm reps), Val.list [encPerm (1 : Perm (Fin m))]]).wt +
        reps.length + 10 * (L * Y * Y) + 1 ≤ 300 * (L * Y * Y) := by omega
    have : (reps.length + 1) *
        ((Val.list [c1, Val.list (List.map encPerm reps), Val.list [encPerm (1 : Perm (Fin m))]]).wt +
          reps.length + 10 * (L * Y * Y) + 1) ≤ L * (300 * (L * Y * Y)) :=
      Nat.mul_le_mul (by omega) hwt
    have e : L * (300 * (L * Y * Y)) = 300 * (L * (L * Y * Y)) := by ring
    rw [e] at this; rw [Nat.mul_assoc]; simp only [loopModK]; omega
  unfold outbSchFoldC
  omega

/-! ### Rebasing one coset entry -/

/-- The context passed to `outbRebOneF`: `[encGroup hsR, m, [r, r⁻¹], 1]`. -/
def outbRebCtx (hsR : List (Perm (Fin m))) (r : Perm (Fin m)) : Val :=
  .list [encGroup hsR, .nat m, .list [encPerm r, encPerm r⁻¹], encPerm (1 : Perm (Fin m))]

/-- The hit branch of `outbRebOneF` (when `idx = var 4 < length (var 2)`). -/
def outbRebHitF (comp inv fb_sch red : ℕ) : Expr :=
  .letE (.call comp (mk2 (.var 3) (.call inv (.get (.var 2) (.var 4)))))
  (.letE (.call fb_sch (mk3 (mk2 (mk2 (.get (arg 0) (.nat 0)) (.var 2)) (.var 1))
      (.var 2) (mk1 (.get (arg 0) (.nat 3)))))
  (.letE (.call red (mk2 (.get (arg 0) (.nat 1)) (mk2 (.get (arg 0) (.nat 1)) (.var 6))))
  (mk2 (.var 5) (.var 7))))

/-- The nonempty branch of `outbRebOneF` (when `v = [encPerm g, encGroup gs]`). -/
def outbRebConsF (mp_conj wh comp fnd inv fb_sch red : ℕ) : Expr :=
  .letE (.call mp_conj (mk2 (.get (arg 0) (.nat 2)) (.get (.get (arg 1) (.nat 1)) (.nat 1))))
  (.letE (.call wh (mk3 (mk2 (.get (arg 0) (.nat 0)) (.var 1)) (.nat 0)
      (mk1 (.get (arg 0) (.nat 3)))))
  (.letE (.call comp (mk2 (.get (arg 1) (.nat 0)) (.get (.get (arg 0) (.nat 2)) (.nat 1))))
  (.letE (.call fnd (mk2 (mk2 (.get (arg 0) (.nat 0)) (.var 3)) (.var 2)))
  (.ite (.arith .lt (.var 4) (.length (.var 2)))
    (outbRebHitF comp inv fb_sch red)
    .nil))))

/-- **Rebasing one coset entry** on `[c, v]`. -/
def outbRebOneF (mp_conj wh comp fnd inv fb_sch red : ℕ) : Expr :=
  .ite (.length (arg 1))
    (outbRebConsF mp_conj wh comp fnd inv fb_sch red)
    .nil

/-- **Rebasing the full coset table** on `[encGroup hsR, m, encPerm r, vs]`. -/
def outbRebTabF (rg inv mp_reb : ℕ) : Expr :=
  .letE (mk4 (arg 0) (arg 1) (mk2 (arg 2) (.call inv (arg 2))) (.call rg (arg 1)))
  (.call mp_reb (mk2 (.var 1) (arg 3)))

/-- Cost bound for rebasing one coset entry, for `(R.subgroupOf H).index ≤ X` and `m ≤ X`. -/
noncomputable def outbOneK (p : Prim) (hm : Membership) (X : ℕ) : ℕ :=
  10 * (2 * (X + 1) * tmRpRoundC hm (10 ^ 4 * (X + 1) ^ 6) (2 * (X + 1))) +
    p.boundSize (10 ^ 4 * (X + 1) ^ 8) +
    10 ^ 22 * (X + 1) ^ 20

/-- Cost bound for rebasing the full coset table. -/
noncomputable def outbRebK (p : Prim) (hm : Membership) (X : ℕ) : ℕ :=
  (X + 1) ^ 2 * outbOneK p hm X + 10 ^ 9 * (X + 1) ^ 12

theorem tmRpRoundC_mono_L (hm : Membership) (Y : ℕ) {L₁ L₂ : ℕ} (h : L₁ ≤ L₂) :
    tmRpRoundC hm Y L₁ ≤ tmRpRoundC hm Y L₂ := by
  unfold tmRpRoundC tmRpTestC
  have h1 : L₁ * tmRpPredC hm Y ≤ L₂ * tmRpPredC hm Y := Nat.mul_le_mul_right _ h
  have h2 : L₁ * L₁ * Y ≤ L₂ * L₂ * Y :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul h h)
  have h3 : L₁ * Y ≤ L₂ * Y := Nat.mul_le_mul_right _ h
  have h4 : Y * (L₁ * tmRpPredC hm Y + 10 ^ 8 * (L₁ * L₁ * Y)) ≤
      Y * (L₂ * tmRpPredC hm Y + 10 ^ 8 * (L₂ * L₂ * Y)) :=
    Nat.mul_le_mul_left _ (Nat.add_le_add h1 (Nat.mul_le_mul_left _ h2))
  have h5 : 10 ^ 7 * (Y * (L₁ * Y)) ≤ 10 ^ 7 * (Y * (L₂ * Y)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
  omega

/-- Where the functions of `OutbReb` sit. -/
structure OutbRebAt (P : Program) (hm : Membership)
    (reb reb1 mp_reb wh st fb_rp gt ab_rp pt fnd fb_sch srow mg_sch sgen
      comp inv rg app red mp_conj conj jst jm : ℕ) : Prop where
  hreb : P.funs[reb]? = some (outbRebTabF rg inv mp_reb)
  hreb1 : P.funs[reb1]? = some (outbRebOneF mp_conj wh comp fnd inv fb_sch red)
  hmp_reb : P.HasAt mp_reb (mapFuns mp_reb reb1)
  hwh : P.funs[wh]? = some (tmRpWhileF wh st)
  hround : TmRpRoundAt P hm st fb_rp gt ab_rp pt jm comp inv
  hsch : OutbSchAt P hm fb_sch srow mg_sch sgen app fnd pt jm comp inv
  hrg : P.HasAt rg (rangeFuns rg)
  hred : P.HasAt red (redFuns red jst)
  hmp_conj : P.HasAt mp_conj (mapFuns mp_conj conj)
  hconj : P.funs[conj]? = some (tmCsConjF comp)

set_option maxHeartbeats 3200000 in
/-- **Rebasing one coset entry.** -/
theorem outbRebOne_spec (hst : PointwiseStab) (hm : Membership) {P : Program}
    {reb reb1 mp_reb wh st fb_rp gt ab_rp pt fnd fb_sch srow mg_sch sgen
      comp inv rg app red mp_conj conj jst jm : ℕ}
    (h : OutbRebAt P hm reb reb1 mp_reb wh st fb_rp gt ab_rp pt fnd fb_sch srow mg_sch sgen
      comp inv rg app red mp_conj conj jst jm)
    (hjst : P.prims[jst]? = some (pointwiseStabPrim hst))
    {H R : Subgroup (Perm (Fin m))} (hRH : R ≤ H)
    {hsR : List (Perm (Fin m))} (hlR : hsR.length ≤ m ^ 2) (hgR : gens hsR = R)
    {r : Perm (Fin m)} (hr : r ∈ H)
    {Ω : Type*} [RAct (Perm (Fin m)) Ω] {z w : Ω} {v : Val}
    (hv : AnsC (Equiv.refl (Fin m)) v (Iso H z w))
    {X : ℕ} (hmX : m ≤ X) (hidxX : (R.subgroupOf H).index ≤ X) :
    FunAll P reb1 (.list [outbRebCtx hsR r, v]) (fun w' cost =>
      AnsC (Equiv.refl (Fin m)) w' (Iso R z (w ↼ r⁻¹)) ∧
        cost ≤ outbOneK (pointwiseStabPrim hst) hm X) := by
  set c := outbRebCtx hsR r with hc
  set Y := 10 ^ 4 * (X + 1) ^ 6 with hYdef
  set L := 2 * (X + 1) with hLdef
  clear_value Y L
  have hX1 : 1 ≤ X + 1 := by omega
  have h1_6 : 1 ≤ (X + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hX_6 : X + 1 ≤ (X + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
  have hL_pos : 0 < L := by omega
  have hY_pos : 0 < Y := by omega
  have hm1 : m + 1 ≤ X + 1 := by omega
  have hmp : ∀ k, (m + 1) ^ k ≤ (X + 1) ^ k := fun k => Nat.pow_le_pow_left hm1 k
  have hXp : ∀ j k, j ≤ k → (X + 1) ^ j ≤ (X + 1) ^ k := fun j k hjk => Nat.pow_le_pow_right hX1 hjk
  have h14 : 1 ≤ (m + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h24 : (m + 1) ^ 2 ≤ (m + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have h34 : (m + 1) ^ 3 ≤ (m + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have h46 : (m + 1) ^ 4 ≤ (X + 1) ^ 6 := (hmp 4).trans (hXp 4 6 (by norm_num))
  have hY : (m + 1) ^ 4 ≤ Y := by omega
  have wgR := (wt_encGroup_le_sq hlR).trans (Nat.mul_le_mul_left 320 (hmp 6))
  have hgY : (encGroup hsR).wt ≤ Y := by omega
  have wr := (wt_encPerm_le r).trans (Nat.mul_le_mul_left 4 ((hmp 2).trans (hXp 2 6 (by norm_num))))
  have wri := (wt_encPerm_le r⁻¹).trans (Nat.mul_le_mul_left 4 ((hmp 2).trans (hXp 2 6 (by norm_num))))
  have w1 := (wt_encPerm_le (1 : Perm (Fin m))).trans
    (Nat.mul_le_mul_left 4 ((hmp 2).trans (hXp 2 6 (by norm_num))))
  have wnm : (Val.nat m).wt ≤ 3 * (X + 1) ^ 6 := (wt_nat_le m).trans (by omega)
  have wpr := wt_list2_le (encPerm r) (encPerm r⁻¹)
  have wc : c.wt ≤ Y := by
    have := wt_list4_le (encGroup hsR) (.nat m) (.list [encPerm r, encPerm r⁻¹])
      (encPerm (1 : Perm (Fin m)))
    have : c.wt = (Val.list [encGroup hsR, .nat m, .list [encPerm r, encPerm r⁻¹],
      encPerm (1 : Perm (Fin m))]).wt := rfl
    omega
  rcases hv with ⟨rfl, hemp⟩ | ⟨g, gs, rfl, hgl, hA⟩
  · -- empty entry
    have hd := Det.ite_zero (t := outbRebConsF mp_conj wh comp fnd inv fb_sch red) (P := P)
      (Det.length (Det.arg' (vs := [c, .list []]) (rest := []) (j := 1) rfl)) Det.nil
    refine FunAll.mono (FunDet.intro h.hreb1 hd) fun w' cost ⟨hw', hcost⟩ => ⟨?_, ?_⟩
    · rw [hw']
      exact Or.inl ⟨rfl, outbReb_iso_empty hRH hr hemp⟩
    · have wa := wt_list2_le c (Val.list [])
      have : (Val.list []).wt ≤ 5 := by decide
      have : (X + 1) ^ 6 ≤ (X + 1) ^ 20 := hXp 6 20 (by norm_num)
      have : 1 ≤ (X + 1) ^ 20 := Nat.one_le_pow _ _ (by omega)
      unfold outbOneK
      simp only [List.length_nil] at hcost
      omega
  · -- nonempty entry `v = [encPerm g, encGroup gs]`
    have hI : Iso H z w = (fun k => g * k) '' (gens gs : Set (Perm (Fin m))) := by
      rw [tmCs_toFin_refl] at hA; exact hA
    have hgH : g ∈ H := by
      have : g ∈ Iso H z w := by rw [hI]; exact ⟨1, (gens gs).one_mem, mul_one g⟩
      exact this.1
    have hgsH : gens gs ≤ H := by
      have : gens gs = Aut H w := SetLike.ext fun k => tmCs_gens_aut hI k
      rw [this]; exact aut_le H w
    set v := Val.list [encPerm g, encGroup gs] with hvdef
    set pairR := Val.list [encPerm r, encPerm r⁻¹] with hpairR
    set σK' := (1 :: gs).map (fun k => r * k * r⁻¹) with hσK'
    set K' := gens σK' with hK'
    have hsubK'H : ∀ k' ∈ σK', k' ∈ H := outbReb_conj_sub hr hgsH
    have hK'H : K' ≤ H := by
      rw [hK', GI.Cited.gens, Subgroup.closure_le]
      intro k' hk'; exact hsubK'H k' hk'
    have hidxK' : (R.subgroupOf K').index ≤ X := (outbReb_relIndex_le hK'H).trans hidxX
    refine FunAll.intro h.hreb1 ?_
    unfold outbRebOneF
    have dv := Det.arg' (P := P) (vs := [c, v]) (rest := []) (j := 1) (v := v) rfl
    refine EvalAll.ite (Det.length dv) (fun _ _ h => ⟨_, h.1⟩) fun z0 cz0 ⟨hz0, hcz0⟩ => ?_
    cases hz0
    simp only [hvdef, List.length_cons, Nat.succ_ne_zero, ↓reduceIte]
    unfold outbRebConsF
    -- 1. conjugate `1 :: gs` by `r`
    have d0 := Det.arg' (P := P) (vs := [c, v]) (rest := []) (j := 0) (v := c) rfl
    have dpr := Det.get' d0 (Det.nat 2)
      (vs := [encGroup hsR, .nat m, pairR, encPerm (1 : Perm (Fin m))]) (v := pairR) rfl
    have dgs := Det.get' (Det.get' dv (Det.nat 1) (vs := [encPerm g, encGroup gs])
      (v := encGroup gs) rfl) (Det.nat 1) (vs := [.nat m, .list ((1 :: gs).map encPerm)])
      (v := .list ((1 :: gs).map encPerm)) rfl
    have hMconj := map_spec h.hmp_conj (c := pairR) (xs := (1 :: gs).map encPerm)
      (R := fun u w => ∀ σ : Perm (Fin m), u = encPerm σ → w = encPerm (r * σ * r⁻¹))
      (B := fun _ => tmCsConjK m) (by
        intro u hu
        obtain ⟨σ, -, rfl⟩ := List.mem_map.1 hu
        refine FunAll.mono (tmCs_conj_spec h.hconj h.hsch.hcomp r σ) fun w cost hw =>
          ⟨fun σ' h' => by rw [hw.1, encPerm_injective h'], hw.2⟩)
    have hws_conj : ∀ ws', List.Forall₂ (fun u w => ∀ σ : Perm (Fin m), u = encPerm σ →
        w = encPerm (r * σ * r⁻¹)) ((1 :: gs).map encPerm) ws' → ws' = σK'.map encPerm := by
      intro ws' h2
      have := forall₂_map_eq (g := fun σ => encPerm (r * σ * r⁻¹)) (fun a _ w hw => hw a rfl) h2
      rw [this, hσK', List.map_map]; rfl
    have hlen_gs : (1 :: gs).length ≤ (X + 1) ^ 2 := by
      simp only [List.length_cons]
      have : m ^ 2 + 1 ≤ (m + 1) ^ 2 := by nlinarith
      have := hmp 2; omega
    have hlen_σK' : σK'.length ≤ (X + 1) ^ 2 := by rw [hσK', List.length_map]; exact hlen_gs
    have wgs := (wt_encGroup_le_sq hgl).trans (Nat.mul_le_mul_left 320 (hmp 6))
    have w1gs : (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt :=
      wt_le_wt_list (by simp)
    set gs' := gs.map (fun k => r * k * r⁻¹) with hgs'
    have hgl' : gs'.length ≤ m ^ 2 := by rw [hgs', List.length_map]; exact hgl
    have wgs' := (wt_encGroup_le_sq hgl').trans (Nat.mul_le_mul_left 320 (hmp 6))
    have wσK' : (Val.list (σK'.map encPerm)).wt < (encGroup gs').wt := by
      have : σK'.map encPerm = (1 :: gs').map encPerm := by
        simp [hσK', hgs']
      rw [this]
      exact wt_le_wt_list (by simp)
    have hconj_cost : FunDet P mp_conj (.list [pairR, .list ((1 :: gs).map encPerm)])
        (.list (σK'.map encPerm)) (10 ^ 7 * (X + 1) ^ 8) := by
      refine FunAll.mono hMconj fun w cost ⟨ws', hw, h2, hcost⟩ => ?_
      have := hws_conj ws' h2; subst this; subst hw
      refine ⟨rfl, ?_⟩
      rw [tm_sum_map_const, List.length_map] at hcost
      have h1 : (1 :: gs).length * tmCsConjK m ≤ (X + 1) ^ 2 * (10 ^ 6 * (X + 1) ^ 3) := by
        unfold tmCsConjK
        exact Nat.mul_le_mul hlen_gs (Nat.mul_le_mul_left _ (hmp 3))
      have w2 := wt_list2_le pairR (.list ((1 :: gs).map encPerm))
      have hlp : mapK * ((1 :: gs).length + 1) *
          ((Val.list [pairR, .list ((1 :: gs).map encPerm)]).wt +
            (Val.list (σK'.map encPerm)).wt + 1) ≤
          2 * 10 ^ 3 * (X + 1) ^ 2 * (2000 * (X + 1) ^ 6) := by
        simp only [mapK]
        refine Nat.mul_le_mul (by
          have : 1 ≤ (X + 1) ^ 2 := Nat.one_le_pow _ _ (by omega); omega) ?_
        omega
      have e5 : (X + 1) ^ 2 * (10 ^ 6 * (X + 1) ^ 3) = 10 ^ 6 * (X + 1) ^ 5 := by ring
      have e8 : 2 * 10 ^ 3 * (X + 1) ^ 2 * (2000 * (X + 1) ^ 6) = 4 * 10 ^ 6 * (X + 1) ^ 8 := by ring
      have h58 := hXp 5 8 (by norm_num)
      omega
    refine EvalAll.letE (Det.call (Det.mk2 dpr dgs) hconj_cost) ?_
    rintro _ c1 ⟨rfl, hc1⟩
    -- 2. enumerate right coset representatives `reps` of `R ∩ K'` in `K'`
    set env1 := [Val.list [c, v], Val.list (σK'.map encPerm)] with henv1
    have e0 := Det.arg' (P := P) (vs := [c, v]) (rest := [.list (σK'.map encPerm)]) (j := 0)
      (v := c) rfl
    have egR := Det.get' e0 (Det.nat 0)
      (vs := [encGroup hsR, .nat m, pairR, encPerm (1 : Perm (Fin m))]) (v := encGroup hsR) rfl
    have e1p := Det.get' e0 (Det.nat 3)
      (vs := [encGroup hsR, .nat m, pairR, encPerm (1 : Perm (Fin m))])
      (v := encPerm (1 : Perm (Fin m))) rfl
    have ev1 := Det.var' (P := P) (env := env1) (i := 1) (v := .list (σK'.map encPerm)) rfl
    have hRV : GroupVal m (encGroup hsR) R := ⟨hsR, rfl, hgR⟩
    have hgsK' : ∀ k' ∈ σK', k' ∈ K' := fun k' hk' => Subgroup.subset_closure hk'
    have hcY : (Val.list [encGroup hsR, .list (σK'.map encPerm)]).wt ≤ Y := by
      have := wt_list2_le (encGroup hsR) (.list (σK'.map encPerm))
      omega
    refine EvalAll.letE (EvalAll.call_spec (Det.mk3 (Det.mk2 egR ev1) (Det.nat 0) (Det.mk1 e1p))
      (tmRpLoop_spec hm h.hwh h.hround hRV hgsK' hY hcY)) ?_
    rintro _ c2 ⟨cb2, ⟨reps, rfl, ⟨j_rp, hinv, hj_rp⟩, hcb2⟩, hc2⟩
    have hcovK' : ∀ x ∈ K', TmRpCov R reps x := tmRp_cover hinv hj_rp
    have h1_reps : (1 : Perm (Fin m)) ∈ reps := by
      cases reps with
      | nil => have := hinv.head; simp at this
      | cons a l =>
        have := hinv.head
        simp only [List.head?_cons, Option.some.injEq] at this
        exact this ▸ List.mem_cons_self
    have hlen_reps : reps.length ≤ X := hinv.length_le.trans hidxK'
    -- 3. `y0 = g * r⁻¹`
    set env2 := env1 ++ [.list (reps.map encPerm)] with henv2
    have f0 := Det.arg' (P := P) (vs := [c, v])
      (rest := [.list (σK'.map encPerm), .list (reps.map encPerm)]) (j := 0) (v := c) rfl
    have f1 := Det.arg' (P := P) (vs := [c, v])
      (rest := [.list (σK'.map encPerm), .list (reps.map encPerm)]) (j := 1) (v := v) rfl
    have fg := Det.get' f1 (Det.nat 0) (vs := [encPerm g, encGroup gs]) (v := encPerm g) rfl
    have fri := Det.get' (Det.get' f0 (Det.nat 2)
      (vs := [encGroup hsR, .nat m, pairR, encPerm (1 : Perm (Fin m))]) (v := pairR) rfl)
      (Det.nat 1) (vs := [encPerm r, encPerm r⁻¹]) (v := encPerm r⁻¹) rfl
    set y0 := g * r⁻¹ with hy0
    refine EvalAll.letE (Det.call (Det.mk2 fg fri) (compose_spec h.hsch.hcomp g r⁻¹)) ?_
    rintro _ c3 ⟨rfl, hc3⟩
    -- 4. `idx = outbRebIdx R reps y0`
    set env3 := env2 ++ [encPerm y0] with henv3
    have k0 := Det.arg' (P := P) (vs := [c, v])
      (rest := [.list (σK'.map encPerm), .list (reps.map encPerm), encPerm y0])
      (j := 0) (v := c) rfl
    have kgR := Det.get' k0 (Det.nat 0)
      (vs := [encGroup hsR, .nat m, pairR, encPerm (1 : Perm (Fin m))]) (v := encGroup hsR) rfl
    have kv2 := Det.var' (P := P) (env := env3) (i := 2) (v := .list (reps.map encPerm)) rfl
    have kv3 := Det.var' (P := P) (env := env3) (i := 3) (v := encPerm y0) rfl
    have hfnd' := find_spec h.hsch.hfnd (c := .list [encGroup hsR, encPerm y0])
      (xs := reps.map encPerm) (q := tmRpB R y0) (B := fun _ => tmRpPredC hm Y)
      (fun u hu => by
        obtain ⟨r', -, rfl⟩ := List.mem_map.1 hu
        exact tmRpPred_spec hm h.hsch.hpt h.hsch.hjm h.hsch.hcomp h.hsch.hinv hRV hY hgY y0 r')
    rw [outbReb_findIdx_map] at hfnd'
    set idx := outbRebIdx R reps y0 with hidx
    refine EvalAll.letE (Det.call (Det.mk2 (Det.mk2 kgR kv3) kv2)
      (hfnd'.mono fun w cw hw => hw)) ?_
    rintro _ c4 ⟨rfl, hc4⟩
    -- weights for steps 1 to 4
    have wg := (wt_encPerm_le g).trans (Nat.mul_le_mul_left 4 ((hmp 2).trans (hXp 2 6 (by norm_num))))
    have wy0 := (wt_encPerm_le y0).trans (Nat.mul_le_mul_left 4 ((hmp 2).trans (hXp 2 6 (by norm_num))))
    have wv : v.wt ≤ Y := by
      have := wt_list2_le (encPerm g) (encGroup gs)
      have : v.wt = (Val.list [encPerm g, encGroup gs]).wt := rfl
      omega
    have wa : (Val.list [c, v]).wt ≤ 5 * Y := by
      have := wt_list2_le c v
      omega
    have wreps := tmRp_wt_reps hY reps (L := L) (by omega)
    have hcb2' : cb2 ≤ L * tmRpRoundC hm Y L + L * (tmRpWK * (Y + L + 10 * (L * Y) + 10)) := by
      rw [← Nat.mul_add]
      have hL_le : (R.subgroupOf K').index + 2 ≤ L := by omega
      have h1 := tmRpRoundC_mono_L hm Y hL_le
      refine hcb2.trans (Nat.mul_le_mul (by omega) (Nat.add_le_add h1
        (Nat.mul_le_mul_left _ (by
          have : ((R.subgroupOf K').index + 2) * Y ≤ L * Y := Nat.mul_le_mul_right _ hL_le
          omega))))
    have hc4_sum : (((reps.map encPerm).map fun _ => tmRpPredC hm Y).sum) ≤ L * tmRpPredC hm Y := by
      rw [tm_sum_map_const, List.length_map]
      exact Nat.mul_le_mul_right _ (by omega)
    have hidx_le : idx ≤ reps.length := by
      rw [hidx, ← outbReb_findIdx_map]
      exact List.findIdx_le_length.trans (by simp)
    have widx : (Val.nat idx).wt ≤ 3 * (X + 1) ^ 6 := (wt_nat_le idx).trans (by omega)
    -- 5. test `idx < reps.length`
    set env4 := env3 ++ [.nat idx] with henv4
    have m2 := Det.var' (P := P) (env := env4) (i := 2) (v := .list (reps.map encPerm)) rfl
    have m4 := Det.var' (P := P) (env := env4) (i := 4) (v := .nat idx) rfl
    have mlen := Det.length m2
    rw [List.length_map] at mlen
    have htest_le_round : tmRpTestC hm Y L ≤ tmRpRoundC hm Y L := by
      unfold tmRpRoundC
      exact (Nat.le_mul_of_pos_left _ hY_pos).trans (Nat.le_add_right _ _)
    have hpred_le_round : L * tmRpPredC hm Y ≤ tmRpRoundC hm Y L :=
      (Nat.le_add_right _ _).trans htest_le_round
    have hLY_le_round : 10 ^ 6 * (L * L * Y) ≤ tmRpRoundC hm Y L := by
      refine (le_trans ?_ (Nat.le_add_left _ _)).trans htest_le_round
      exact Nat.mul_le_mul_right _ (by norm_num)
    have hc4_bound : c4 ≤ 2 * tmRpRoundC hm Y L := by
      rw [List.length_map] at hc4
      have wgy := wt_list2_le (encGroup hsR) (encPerm y0)
      have wgvr := wt_list2_le (.list [encGroup hsR, encPerm y0]) (.list (reps.map encPerm))
      have hLY : L ≤ L * Y := Nat.le_mul_of_pos_right _ hY_pos
      have hYLY : Y ≤ L * Y := Nat.le_mul_of_pos_left _ hL_pos
      have hLL : L * Y ≤ L * L * Y := by
        rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ hL_pos
      have hlp : loopModK * (reps.length + 1) *
          ((Val.list [Val.list [encGroup hsR, encPerm y0], Val.list (List.map encPerm reps)]).wt +
            2 * reps.length + 3) ≤ 10 ^ 5 * (L * L * Y) := by
        have h1' : (reps.length + 1) *
            ((Val.list [Val.list [encGroup hsR, encPerm y0], Val.list (List.map encPerm reps)]).wt +
              2 * reps.length + 3) ≤ L * (80 * (L * Y)) := Nat.mul_le_mul (by omega) (by omega)
        have e : L * (80 * (L * Y)) = 80 * (L * L * Y) := by ring
        rw [e] at h1'; rw [Nat.mul_assoc]; simp only [loopModK]; omega
      omega
    have hpre14 : cz0 + c1 + c2 + c3 + c4 ≤
        2 * (L * tmRpRoundC hm Y L) + 10 ^ 12 * (X + 1) ^ 14 := by
      have hlen2 : [encPerm g, encGroup gs].length = 2 := rfl
      rw [hlen2] at hcz0
      rw [← hy0] at hc3
      have w1a := wt_list2_le pairR (.list ((1 :: gs).map encPerm))
      have w2a := wt_list2_le (encGroup hsR) (.list (σK'.map encPerm))
      have w2b := wt_list1_le (encPerm (1 : Perm (Fin m)))
      have w2c := wt_list3_le (.list [encGroup hsR, .list (σK'.map encPerm)]) (.nat 0)
        (.list [encPerm (1 : Perm (Fin m))])
      have w3a := wt_list2_le (encPerm g) (encPerm r⁻¹)
      have wn0 : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
      have hLY8 : L * Y ≤ 4 * 10 ^ 4 * (X + 1) ^ 8 := by
        have : L * Y = 2 * 10 ^ 4 * (X + 1) ^ 7 := by rw [hLdef, hYdef]; ring
        have := hXp 7 8 (by norm_num); omega
      have hLY14 : L * (tmRpWK * (Y + L + 10 * (L * Y) + 10)) ≤ 10 ^ 10 * (X + 1) ^ 14 := by
        simp only [tmRpWK]
        have e : L * (100 * (Y + L + 10 * (L * Y) + 10)) =
            2 * 10 ^ 6 * (X + 1) ^ 7 + 400 * (X + 1) ^ 2 + 4 * 10 ^ 7 * (X + 1) ^ 8 +
              2000 * (X + 1) := by
          rw [hLdef, hYdef]; ring
        rw [e]
        have := Nat.le_self_pow (n := 14) (by norm_num) (X + 1)
        have := hXp 2 14 (by norm_num)
        have := hXp 7 14 (by norm_num)
        have := hXp 8 14 (by norm_num)
        omega
      have h8_14 := hXp 8 14 (by norm_num)
      have h6_14 := hXp 6 14 (by norm_num)
      have h3_14 := hXp 3 14 (by norm_num)
      have h14_0 : 1 ≤ (X + 1) ^ 14 := Nat.one_le_pow _ _ (by omega)
      have hround_L : 2 * tmRpRoundC hm Y L ≤ L * tmRpRoundC hm Y L :=
        Nat.mul_le_mul_right _ (by omega)
      simp only [permK] at hc3
      omega
    by_cases hlt : idx < reps.length
    · -- hit: `idx < reps.length`
      have hcond := Det.arith' (op := .lt) m4 mlen (z := 1) (by simp [BinOp.eval, hlt])
      refine EvalAll.ite hcond (fun _ _ h => ⟨1, h.1⟩) fun x1 cx1 ⟨hx1, hcx1⟩ => ?_
      cases hx1
      simp only [one_ne_zero, ite_false]
      unfold outbRebHitF
      -- 5a. `u0 = y0 * (reps[idx])⁻¹`
      have hget : (reps.map encPerm)[idx]? = some (encPerm (reps[idx]'hlt)) := by simp [hlt]
      have n2 := Det.var' (P := P) (env := env4) (i := 2) (v := .list (reps.map encPerm)) rfl
      have n3 := Det.var' (P := P) (env := env4) (i := 3) (v := encPerm y0) rfl
      have n4 := Det.var' (P := P) (env := env4) (i := 4) (v := .nat idx) rfl
      have ns := Det.get' n2 n4 hget
      have ninv := Det.call ns (inv_spec h.hsch.hinv (reps[idx]'hlt))
      set s0 := reps[idx]'hlt with hs0
      set u0 := y0 * s0⁻¹ with hu0
      refine EvalAll.letE (Det.call (Det.mk2 n3 ninv) (compose_spec h.hsch.hcomp y0 s0⁻¹)) ?_
      rintro _ c5 ⟨rfl, hc5⟩
      -- 5b. Schreier generators `1 :: outbSchreierGens R reps σK'`
      set env5 := env4 ++ [encPerm u0] with henv5
      have p0 := Det.arg' (P := P) (vs := [c, v])
        (rest := [.list (σK'.map encPerm), .list (reps.map encPerm), encPerm y0, .nat idx,
          encPerm u0]) (j := 0) (v := c) rfl
      have pgR := Det.get' p0 (Det.nat 0)
        (vs := [encGroup hsR, .nat m, pairR, encPerm (1 : Perm (Fin m))]) (v := encGroup hsR) rfl
      have p1p := Det.get' p0 (Det.nat 3)
        (vs := [encGroup hsR, .nat m, pairR, encPerm (1 : Perm (Fin m))])
        (v := encPerm (1 : Perm (Fin m))) rfl
      have pv1 := Det.var' (P := P) (env := env5) (i := 1) (v := .list (σK'.map encPerm)) rfl
      have pv2 := Det.var' (P := P) (env := env5) (i := 2) (v := .list (reps.map encPerm)) rfl
      have hcov_sch : ∀ s ∈ reps, ∀ k' ∈ σK', TmRpCov R reps (s * k') := by
        intro s hs k' hk'
        exact hcovK' _ (K'.mul_mem (hinv.sub s hs) (hgsK' k' hk'))
      have hsch := outbSchFold_spec hm h.hsch hRV hY hgY reps (L := L) (by omega) σK'
        (by
          have : (X + 1) ^ 2 + 1 < Y := by
            rw [hYdef]; have := hXp 2 6 (by norm_num); omega
          omega)
        hcov_sch
      refine EvalAll.letE (Det.call (Det.mk3 (Det.mk2 (Det.mk2 pgR pv2) pv1) pv2 (Det.mk1 p1p))
        hsch) ?_
      rintro _ c6 ⟨rfl, hc6⟩
      -- 5c. reduce to `≤ m²` generators
      set L0 := Val.list ((1 :: outbSchreierGens R reps σK').map encPerm) with hL0
      set env6 := env5 ++ [L0] with henv6
      have q0 := Det.arg' (P := P) (vs := [c, v])
        (rest := [.list (σK'.map encPerm), .list (reps.map encPerm), encPerm y0, .nat idx,
          encPerm u0, L0]) (j := 0) (v := c) rfl
      have qm := Det.get' q0 (Det.nat 1)
        (vs := [encGroup hsR, .nat m, pairR, encPerm (1 : Perm (Fin m))]) (v := .nat m) rfl
      have q6 := Det.var' (P := P) (env := env6) (i := 6) (v := L0) rfl
      have hgv_sch : GroupVal m (.list [.nat m, L0]) (gens (outbSchreierGens R reps σK')) :=
        ⟨outbSchreierGens R reps σK', rfl, rfl⟩
      refine EvalAll.letE (EvalAll.call_spec (Det.mk2 qm (Det.mk2 qm q6))
        (red_spec hst h.hred hjst hgv_sch)) ?_
      rintro _ c7 ⟨cb7, ⟨hs, rfl, hgens_hs, hlen_hs, hcb7⟩, hc7⟩
      set env7 := env6 ++ [encGroup hs] with henv7
      have r5 := Det.var' (P := P) (env := env7) (i := 5) (v := encPerm u0) rfl
      have r7 := Det.var' (P := P) (env := env7) (i := 7) (v := encGroup hs) rfl
      refine (Det.mk2 r5 r7).post fun c8 hc8 => ⟨Or.inr ⟨u0, hs, rfl, hlen_hs, ?_⟩, ?_⟩
      · obtain ⟨hs0_mem, hu0R⟩ := outbRebIdx_mem hlt
        rw [tmCs_toFin_refl, outbReb_iso_eq hRH hr, hI,
          outbReb_coset_of_cov hinv.sub hs0_mem hu0R,
          ← outbSchreier_gens_eq rfl h1_reps hinv.sub hinv.distinct hcovK',
          ← hgens_hs]
        rfl
      · -- cost in the hit branch
        have ws0 := (wt_encPerm_le s0).trans (Nat.mul_le_mul_left 4 ((hmp 2).trans (hXp 2 6 (by norm_num))))
        have ws0i := (wt_encPerm_le s0⁻¹).trans (Nat.mul_le_mul_left 4 ((hmp 2).trans (hXp 2 6 (by norm_num))))
        have wu0 := (wt_encPerm_le u0).trans (Nat.mul_le_mul_left 4 ((hmp 2).trans (hXp 2 6 (by norm_num))))
        have whs := (wt_encGroup_le_sq hlen_hs).trans (Nat.mul_le_mul_left 320 (hmp 6))
        have hlen_sch : (outbSchreierGens R reps σK').length ≤ X * (X + 1) ^ 2 := by
          rw [length_outbSchreierGens]
          exact Nat.mul_le_mul hlen_reps hlen_σK'
        have hlen_sch3 : (outbSchreierGens R reps σK').length ≤ (X + 1) ^ 3 := by
          refine hlen_sch.trans ?_
          calc X * (X + 1) ^ 2 ≤ (X + 1) * (X + 1) ^ 2 := Nat.mul_le_mul_right _ (by omega)
            _ = (X + 1) ^ 3 := by ring
        have hmeas_sch : ((outbSchreierGens R reps σK').length + 2) * (m + 1) ≤
            3 * (X + 1) ^ 4 := by
          have : 1 ≤ (X + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
          calc ((outbSchreierGens R reps σK').length + 2) * (m + 1)
              ≤ (3 * (X + 1) ^ 3) * (X + 1) := Nat.mul_le_mul (by omega) hm1
            _ = 3 * (X + 1) ^ 4 := by ring
        have wenc_sch : (encGroup (outbSchreierGens R reps σK')).wt ≤ 360 * (X + 1) ^ 8 := by
          calc (encGroup (outbSchreierGens R reps σK')).wt
              ≤ 40 * (((outbSchreierGens R reps σK').length + 2) * (m + 1)) ^ 2 :=
                wt_encGroup_le _
            _ ≤ 40 * (3 * (X + 1) ^ 4) ^ 2 :=
                Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hmeas_sch 2)
            _ = 360 * (X + 1) ^ 8 := by ring
        have wL0 : L0.wt < (encGroup (outbSchreierGens R reps σK')).wt :=
          wt_le_wt_list (by simp [hL0])
        have w_mL0 : (Val.list [.nat m, L0]).wt = (encGroup (outbSchreierGens R reps σK')).wt := rfl
        have w_red_arg := wt_list2_le (.nat m) (.list [.nat m, L0])
        have w_red_nil := wt_list2_le (.list [.nat m, L0]) (.list [])
        have hl0 : (Val.list []).wt ≤ 5 := by decide
        have h1_8 : 1 ≤ (X + 1) ^ 8 := Nat.one_le_pow _ _ (by omega)
        have hbd7 : (pointwiseStabPrim hst).bound (Val.list [.list [.nat m, L0], .list []]) ≤
            (pointwiseStabPrim hst).boundSize (10 ^ 4 * (X + 1) ^ 8) := by
          apply Prim.bound_le
          have := (Val.list [.list [.nat m, L0], .list []]).size_le_wt
          omega
        have hm9 : (m + 1) ^ 9 ≤ (X + 1) ^ 20 := (hmp 9).trans (hXp 9 20 (by norm_num))
        have hsch_fold : outbSchFoldC hm Y L ≤
            L * tmRpRoundC hm Y L + 10 ^ 21 * (X + 1) ^ 20 := by
          unfold outbSchFoldC outbSchRowC outbSchGenC
          set T := tmRpTestC hm Y L
          have hTR : L * (Y * T) ≤ L * tmRpRoundC hm Y L :=
            Nat.mul_le_mul_left L (Nat.le_add_right _ _)
          have e1 : L * (Y * (T + 10 ^ 7 * (L * Y)) + 10 ^ 8 * (Y * (Y * (L * Y)))) +
              10 ^ 8 * (L * (L * Y * Y)) =
              L * (Y * T) +
                (10 ^ 7 * (L * Y * (L * Y)) + 10 ^ 8 * (L * Y * (Y * (L * Y))) +
                  10 ^ 8 * (L * (L * Y * Y))) := by ring
          rw [e1]
          refine Nat.add_le_add hTR ?_
          rw [hLdef, hYdef]
          have : 2 * (X + 1) * (10 ^ 4 * (X + 1) ^ 6) * (2 * (X + 1) * (10 ^ 4 * (X + 1) ^ 6)) =
              4 * 10 ^ 8 * (X + 1) ^ 14 := by ring
          have : 2 * (X + 1) * (10 ^ 4 * (X + 1) ^ 6) *
              (10 ^ 4 * (X + 1) ^ 6 * (2 * (X + 1) * (10 ^ 4 * (X + 1) ^ 6))) =
              4 * 10 ^ 12 * (X + 1) ^ 20 := by ring
          have : 2 * (X + 1) * (2 * (X + 1) * (10 ^ 4 * (X + 1) ^ 6) * (10 ^ 4 * (X + 1) ^ 6)) =
              4 * 10 ^ 8 * (X + 1) ^ 14 := by ring
          have := hXp 14 20 (by norm_num)
          omega
        rw [← hu0] at hc5
        have w5a := wt_list2_le (encPerm y0) (encPerm s0⁻¹)
        have w6a := wt_list2_le (encGroup hsR) (.list (reps.map encPerm))
        have w6b := wt_list2_le (.list [encGroup hsR, .list (reps.map encPerm)])
          (.list (σK'.map encPerm))
        have w6c := wt_list1_le (encPerm (1 : Perm (Fin m)))
        have w6d := wt_list3_le
          (.list [.list [encGroup hsR, .list (reps.map encPerm)], .list (σK'.map encPerm)])
          (.list (reps.map encPerm)) (.list [encPerm (1 : Perm (Fin m))])
        have w8a := wt_list2_le (encPerm u0) (encGroup hs)
        have hLY8 : L * Y ≤ 4 * 10 ^ 4 * (X + 1) ^ 8 := by
          have : L * Y = 2 * 10 ^ 4 * (X + 1) ^ 7 := by rw [hLdef, hYdef]; ring
          have := hXp 7 8 (by norm_num); omega
        have h6_20 := hXp 6 20 (by norm_num)
        have h8_20 := hXp 8 20 (by norm_num)
        have h14_20 := hXp 14 20 (by norm_num)
        have h16_20 := hXp 16 20 (by norm_num)
        have h20_0 : 1 ≤ (X + 1) ^ 20 := Nat.one_le_pow _ _ (by omega)
        have wn1 : (Val.nat 1).wt ≤ 3 := wt_nat_le 1
        simp only [permK, invK] at hc5
        unfold outbOneK
        rw [← hYdef, ← hLdef]
        omega
    · -- miss: `¬ idx < reps.length`
      have hcond := Det.arith' (op := .lt) m4 mlen (z := 0) (by simp [BinOp.eval, hlt])
      refine (Det.ite_zero (t := outbRebHitF comp inv fb_sch red) hcond Det.nil).post
        fun c5 hc5 => ⟨Or.inl ⟨rfl, ?_⟩, ?_⟩
      · have hncov : ¬ TmRpCov R reps y0 := fun hc => hlt ((outbRebIdx_lt_iff R reps y0).2 hc)
        rw [outbReb_iso_eq hRH hr, hI]
        exact outbReb_empty_of_not_cov hcovK' hncov
      · have hw0 : (Val.list []).wt ≤ 5 := by decide
        have wn0 : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
        have hLY8 : L * Y ≤ 4 * 10 ^ 4 * (X + 1) ^ 8 := by
          have : L * Y = 2 * 10 ^ 4 * (X + 1) ^ 7 := by rw [hLdef, hYdef]; ring
          have := hXp 7 8 (by norm_num); omega
        have h6_20 := hXp 6 20 (by norm_num)
        have h8_20 := hXp 8 20 (by norm_num)
        have h14_20 := hXp 14 20 (by norm_num)
        have h20_0 : 1 ≤ (X + 1) ^ 20 := Nat.one_le_pow _ _ (by omega)
        unfold outbOneK
        rw [← hYdef, ← hLdef]
        omega

/-- A canonical answer on `Fin m` has weight at most `1000 * (m + 1) ^ 6`. -/
theorem outbReb_wt_ansC {Ω' : Type} {e : Ω' ≃ Fin m} {u : Val} {A : Set (Perm Ω')}
    (h : AnsC e u A) : u.wt ≤ 1000 * (m + 1) ^ 6 := by
  have h6 : 1 ≤ (m + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  rcases h with ⟨rfl, -⟩ | ⟨x, gs, rfl, hgl, -⟩
  · have : (Val.list []).wt ≤ 5 := by decide
    omega
  · have := wt_list2_le (encPerm x) (encGroup gs)
    have := wt_encPerm_le x
    have := wt_encGroup_le_sq hgl
    have : (m + 1) ^ 2 ≤ (m + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    omega

/-- A value `v` encodes at most one subset `A` via `AnsC (Equiv.refl (Fin m)) v A`. -/
theorem outbReb_ansC_unique {v : Val} {A₁ A₂ : Set (Perm (Fin m))}
    (h1 : AnsC (Equiv.refl (Fin m)) v A₁) (h2 : AnsC (Equiv.refl (Fin m)) v A₂) : A₁ = A₂ := by
  have h1' := h1
  rcases h1 with ⟨rfl, rfl⟩ | ⟨g, gs, rfl, -, -⟩
  · exact (tmCs_ansC_nil h2 rfl).symm
  · rw [tmCs_ansC_cons h1' rfl, tmCs_ansC_cons h2 rfl]

/-- **Rebasing the full coset table `vs`.** -/
theorem outbRebTab_spec (hst : PointwiseStab) (hm : Membership) {P : Program}
    {reb reb1 mp_reb wh st fb_rp gt ab_rp pt fnd fb_sch srow mg_sch sgen
      comp inv rg app red mp_conj conj jst jm : ℕ}
    (h : OutbRebAt P hm reb reb1 mp_reb wh st fb_rp gt ab_rp pt fnd fb_sch srow mg_sch sgen
      comp inv rg app red mp_conj conj jst jm)
    (hjst : P.prims[jst]? = some (pointwiseStabPrim hst))
    {H R : Subgroup (Perm (Fin m))} (hRH : R ≤ H)
    {hsR : List (Perm (Fin m))} (hlR : hsR.length ≤ m ^ 2) (hgR : gens hsR = R)
    {r : Perm (Fin m)} (hr : r ∈ H)
    {q : ℕ} {Ω : Type*} [RAct (Perm (Fin m)) Ω] {x y : Fin q → Ω} {vs : List Val}
    (hT : TmCsTabOK H x y vs)
    {X : ℕ} (hmX : m ≤ X) (hqX : q ≤ X)
    (hidxX : (R.subgroupOf H).index ≤ X) :
    FunAll P reb (.list [encGroup hsR, .nat m, encPerm r, .list vs]) (fun w' cost =>
      (∃ vs', w' = .list vs' ∧ TmCsTabOK R x (fun j => y j ↼ r⁻¹) vs' ∧
        (Val.list vs').wt ≤ 3000 * (X + 1) ^ 8) ∧
        cost ≤ outbRebK (pointwiseStabPrim hst) hm X) := by
  set c := outbRebCtx hsR r with hc
  have hX1 : 1 ≤ X + 1 := by omega
  have hm1 : m + 1 ≤ X + 1 := by omega
  have hmp : ∀ k, (m + 1) ^ k ≤ (X + 1) ^ k := fun k => Nat.pow_le_pow_left hm1 k
  have hXp : ∀ j k, j ≤ k → (X + 1) ^ j ≤ (X + 1) ^ k := fun j k hjk => Nat.pow_le_pow_right hX1 hjk
  refine FunAll.intro h.hreb ?_
  unfold outbRebTabF
  set a := Val.list [encGroup hsR, .nat m, encPerm r, .list vs] with ha
  have d0 := Det.arg' (P := P) (vs := [encGroup hsR, .nat m, encPerm r, .list vs]) (rest := [])
    (j := 0) (v := encGroup hsR) rfl
  have d1 := Det.arg' (P := P) (vs := [encGroup hsR, .nat m, encPerm r, .list vs]) (rest := [])
    (j := 1) (v := .nat m) rfl
  have d2 := Det.arg' (P := P) (vs := [encGroup hsR, .nat m, encPerm r, .list vs]) (rest := [])
    (j := 2) (v := encPerm r) rfl
  have dc := Det.mk4 d0 d1 (Det.mk2 d2 (Det.call d2 (inv_spec h.hsch.hinv r)))
    (Det.call d1 (range_det h.hrg m))
  have hdc_val : Val.list [encGroup hsR, .nat m, .list [encPerm r, encPerm r⁻¹],
      encPerm (1 : Perm (Fin m))] = c := rfl
  rw [hdc_val] at dc
  refine EvalAll.letE dc ?_
  rintro _ c1 ⟨rfl, hc1⟩
  have e1 := Det.var' (P := P) (env := [a, c]) (i := 1) (v := c) rfl
  have e3 := Det.arg' (P := P) (vs := [encGroup hsR, .nat m, encPerm r, .list vs]) (rest := [c])
    (j := 3) (v := .list vs) rfl
  have hmem_ans : ∀ v ∈ vs, ∃ i j : Fin q, AnsC (Equiv.refl (Fin m)) v (Iso H (x i) (y j)) := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
    have hkq : k < q * q := hT.1 ▸ hk
    have hq0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; omega)
    have hi : k / q < q := (Nat.div_lt_iff_lt_mul hq0).2 hkq
    have hj : k % q < q := Nat.mod_lt k hq0
    obtain ⟨v', hv', hA⟩ := hT.2 ⟨k / q, hi⟩ ⟨k % q, hj⟩
    have heq : (k / q) * q + k % q = k := by
      have := Nat.div_add_mod k q; linarith
    simp only [heq] at hv'
    rw [List.getElem?_eq_getElem hk] at hv'
    cases hv'
    exact ⟨⟨k / q, hi⟩, ⟨k % q, hj⟩, hA⟩
  have hM := map_spec h.hmp_reb (c := c) (xs := vs)
    (R := fun v w' => (∀ i j : Fin q, AnsC (Equiv.refl (Fin m)) v (Iso H (x i) (y j)) →
        AnsC (Equiv.refl (Fin m)) w' (Iso R (x i) (y j ↼ r⁻¹))) ∧
      w'.wt ≤ 1000 * (X + 1) ^ 6)
    (B := fun _ => outbOneK (pointwiseStabPrim hst) hm X)
    (fun v hv => by
      obtain ⟨i₀, j₀, hA₀⟩ := hmem_ans v hv
      refine (outbRebOne_spec hst hm h hjst hRH hlR hgR hr hA₀ hmX hidxX).mono
        fun w' cost ⟨hw', hcost⟩ => ⟨⟨fun i j hij => ?_, ?_⟩, hcost⟩
      · have heq := outbReb_ansC_unique hij hA₀
        have heqR : Iso R (x i) (y j ↼ r⁻¹) = Iso R (x i₀) (y j₀ ↼ r⁻¹) := by
          rw [outbReb_iso_eq hRH hr, outbReb_iso_eq hRH hr, heq]
        rwa [heqR]
      · exact (outbReb_wt_ansC hw').trans (Nat.mul_le_mul_left _ (hmp 6)))
  refine (EvalAll.call_spec (Det.mk2 e1 e3) hM).mono ?_
  rintro w' c2 ⟨cb2, ⟨vs', hw', h2, hcb2⟩, hc2⟩
  subst hw'
  have hlen_vs' : vs'.length = q * q := by rw [← h2.length_eq, hT.1]
  have hlen_vs : vs.length ≤ (X + 1) ^ 2 := by
    rw [hT.1]
    calc q * q ≤ (X + 1) * (X + 1) := Nat.mul_le_mul (by omega) (by omega)
      _ = (X + 1) ^ 2 := by ring
  have hwt_vs : (Val.list vs).wt ≤ 3000 * (X + 1) ^ 8 := by
    have h1 := wt_list_map_le vs id (W := 1000 * (X + 1) ^ 6) fun v hv => by
      obtain ⟨i₀, j₀, hA₀⟩ := hmem_ans v hv
      exact (outbReb_wt_ansC hA₀).trans (Nat.mul_le_mul_left _ (hmp 6))
    simp only [List.map_id] at h1
    have h2' := Nat.mul_le_mul_right (2 * (1000 * (X + 1) ^ 6) + 1) hlen_vs
    have e8 : (X + 1) ^ 2 * (2 * (1000 * (X + 1) ^ 6) + 1) =
        2000 * (X + 1) ^ 8 + (X + 1) ^ 2 := by ring
    have := hXp 2 8 (by norm_num)
    have : 1 ≤ (X + 1) ^ 8 := Nat.one_le_pow _ _ (by omega)
    omega
  have hwt_vs' : (Val.list vs').wt ≤ 3000 * (X + 1) ^ 8 := by
    have hlen_vs'2 : vs'.length ≤ (X + 1) ^ 2 := by rwa [← h2.length_eq]
    have h1 := wt_list_map_le vs' id (W := 1000 * (X + 1) ^ 6) fun w hw => by
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
      have hk_vs : k < vs.length := by rwa [h2.length_eq]
      exact ((List.forall₂_iff_get.1 h2).2 k hk_vs hk).2
    simp only [List.map_id] at h1
    have h2' := Nat.mul_le_mul_right (2 * (1000 * (X + 1) ^ 6) + 1) hlen_vs'2
    have e8 : (X + 1) ^ 2 * (2 * (1000 * (X + 1) ^ 6) + 1) =
        2000 * (X + 1) ^ 8 + (X + 1) ^ 2 := by ring
    have := hXp 2 8 (by norm_num)
    have : 1 ≤ (X + 1) ^ 8 := Nat.one_le_pow _ _ (by omega)
    omega
  refine ⟨⟨vs', rfl, ⟨hlen_vs', fun i j => ?_⟩, hwt_vs'⟩, ?_⟩
  · obtain ⟨v, hv, hA⟩ := hT.2 i j
    have hk : i.1 * q + j.1 < q * q := by
      calc i.1 * q + j.1 < i.1 * q + q := Nat.add_lt_add_left j.2 _
        _ = (i.1 + 1) * q := by ring
        _ ≤ q * q := Nat.mul_le_mul_right q i.2
    have hk_vs : i.1 * q + j.1 < vs.length := hT.1 ▸ hk
    have hk_vs' : i.1 * q + j.1 < vs'.length := hlen_vs' ▸ hk
    rw [List.getElem?_eq_getElem hk_vs, Option.some.injEq] at hv
    subst hv
    refine ⟨vs'[i.1 * q + j.1], List.getElem?_eq_getElem hk_vs', ?_⟩
    exact ((List.forall₂_iff_get.1 h2).2 (i.1 * q + j.1) hk_vs hk_vs').1 i j hA
  · -- cost bound
    rw [tm_sum_map_const] at hcb2
    have hsum_one : vs.length * outbOneK (pointwiseStabPrim hst) hm X ≤
        (X + 1) ^ 2 * outbOneK (pointwiseStabPrim hst) hm X :=
      Nat.mul_le_mul_right _ hlen_vs
    have wgR := (wt_encGroup_le_sq hlR).trans (Nat.mul_le_mul_left 320 (hmp 6))
    have wr := (wt_encPerm_le r).trans (Nat.mul_le_mul_left 4 ((hmp 2).trans (hXp 2 6 (by norm_num))))
    have wri := (wt_encPerm_le r⁻¹).trans (Nat.mul_le_mul_left 4 ((hmp 2).trans (hXp 2 6 (by norm_num))))
    have w1 := (wt_encPerm_le (1 : Perm (Fin m))).trans
      (Nat.mul_le_mul_left 4 ((hmp 2).trans (hXp 2 6 (by norm_num))))
    have wnm : (Val.nat m).wt ≤ 3 * (X + 1) ^ 6 :=
      (wt_nat_le m).trans (by have : X + 1 ≤ (X + 1) ^ 6 := Nat.le_self_pow (by norm_num) _; omega)
    have wpr := wt_list2_le (encPerm r) (encPerm r⁻¹)
    have wc : c.wt ≤ 2000 * (X + 1) ^ 6 := by
      have := wt_list4_le (encGroup hsR) (.nat m) (.list [encPerm r, encPerm r⁻¹])
        (encPerm (1 : Perm (Fin m)))
      have : c.wt = (Val.list [encGroup hsR, .nat m, .list [encPerm r, encPerm r⁻¹],
        encPerm (1 : Perm (Fin m))]).wt := rfl
      have : 1 ≤ (X + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
      omega
    have wa : a.wt ≤ 10 ^ 4 * (X + 1) ^ 8 := by
      have := wt_list4_le (encGroup hsR) (.nat m) (encPerm r) (.list vs)
      have : a.wt = (Val.list [encGroup hsR, .nat m, encPerm r, .list vs]).wt := rfl
      have := hXp 6 8 (by norm_num)
      have : 1 ≤ (X + 1) ^ 8 := Nat.one_le_pow _ _ (by omega)
      omega
    have wcv := wt_list2_le c (.list vs)
    have h6_8 := hXp 6 8 (by norm_num)
    have h8_0 : 1 ≤ (X + 1) ^ 8 := Nat.one_le_pow _ _ (by omega)
    have h3_8 := (hmp 3).trans (hXp 3 8 (by norm_num))
    have h4_8 := (hmp 4).trans (hXp 4 8 (by norm_num))
    have h6_12 := hXp 6 12 (by norm_num)
    have h8_12 := hXp 8 12 (by norm_num)
    have h12_0 : 1 ≤ (X + 1) ^ 12 := Nat.one_le_pow _ _ (by omega)
    have hlp : mapK * (vs.length + 1) *
        ((Val.list [c, .list vs]).wt + (Val.list vs').wt + 1) ≤
        10 ^ 8 * (X + 1) ^ 12 := by
      simp only [mapK]
      have hlen1 : 1000 * (vs.length + 1) ≤ 2000 * (X + 1) ^ 2 := by
        have : 1 ≤ (X + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
        omega
      have hwt1 : (Val.list [c, .list vs]).wt + (Val.list vs').wt + 1 ≤
          2 * 10 ^ 4 * (X + 1) ^ 8 := by omega
      calc 1000 * (vs.length + 1) * ((Val.list [c, .list vs]).wt + (Val.list vs').wt + 1)
          ≤ (2000 * (X + 1) ^ 2) * (2 * 10 ^ 4 * (X + 1) ^ 8) := Nat.mul_le_mul hlen1 hwt1
        _ = 4 * 10 ^ 7 * (X + 1) ^ 10 := by ring
        _ ≤ 10 ^ 8 * (X + 1) ^ 12 := by have := hXp 10 12 (by norm_num); omega
    rw [← ha] at hc1 hc2
    simp only [invK] at hc1
    unfold outbRebK
    omega

/-! ### Module layout of `OutbReb` -/

/-- The eight single functions of `OutbReb` at offsets `0`–`7` from `o`. -/
def outbRebSingles (o comp inv rg app red mp_conj jm : ℕ) : List Expr :=
  [outbRebTabF rg inv (o + 8),
    outbRebOneF mp_conj (o + 2) comp (o + 17) inv (o + 20) red,
    tmRpWhileF (o + 2) (o + 3),
    tmRpStepF (o + 11),
    tmRpTestF (o + 14) comp,
    tmRpPredF jm comp inv,
    outbSchRowF (o + 23) app,
    outbSchGenF (o + 17) comp inv]

/-- The 26 functions of `OutbReb` placed at base `o`, sharing `comp`, `inv`, `rg`, `app`, `red`,
`mp_conj` with the surrounding coset module. -/
def outbRebFuns (o comp inv rg app red mp_conj jm : ℕ) : List Expr :=
  outbRebSingles o comp inv rg app red mp_conj jm ++
    (mapFuns (o + 8) (o + 1) ++ (foldlFuns (o + 11) (o + 4) ++
    (anyFuns (o + 14) (o + 5) ++ (findFuns (o + 17) (o + 5) ++
    (foldlFuns (o + 20) (o + 6) ++ mapFuns (o + 23) (o + 7))))))

theorem length_outbRebFuns (o comp inv rg app red mp_conj jm : ℕ) :
    (outbRebFuns o comp inv rg app red mp_conj jm).length = 26 := rfl

private theorem outbReb_right {P : Program} {b b' : ℕ} {A B : List Expr} (h : P.HasAt b (A ++ B))
    (hb : b + A.length = b') : P.HasAt b' B := hb ▸ h.right

/-- Bundled placement of `outbRebFuns` at `o` together with the shared modules. -/
structure OutbRebPlaced (P : Program) (hm : Membership)
    (o comp inv rg app red mp_conj conj jst jm : ℕ) : Prop where
  hreb : P.HasAt o (outbRebFuns o comp inv rg app red mp_conj jm)
  hcomp : P.HasAt comp (composeFuns comp)
  hinv : P.HasAt inv (invFuns inv)
  hrg : P.HasAt rg (rangeFuns rg)
  happ : P.HasAt app (appendFuns app)
  hred : P.HasAt red (redFuns red jst)
  hmp_conj : P.HasAt mp_conj (mapFuns mp_conj conj)
  hconj : P.funs[conj]? = some (tmCsConjF comp)
  hjm : P.prims[jm]? = some (membershipPrim hm)

theorem outbRebAt_of {P : Program} {hm : Membership}
    {o comp inv rg app red mp_conj conj jst jm : ℕ}
    (h : OutbRebPlaced P hm o comp inv rg app red mp_conj conj jst jm) :
    OutbRebAt P hm o (o + 1) (o + 8) (o + 2) (o + 3) (o + 11) (o + 4) (o + 14) (o + 5)
      (o + 17) (o + 20) (o + 6) (o + 23) (o + 7) comp inv rg app red mp_conj conj jst jm := by
  have hs := h.hreb.left
  have h0 := outbReb_right h.hreb (b' := o + 8) rfl
  have h1 := outbReb_right h0 (b' := o + 11) rfl
  have h2 := outbReb_right h1 (b' := o + 14) rfl
  have h3 := outbReb_right h2 (b' := o + 17) rfl
  have h4 := outbReb_right h3 (b' := o + 20) rfl
  have h5 := outbReb_right h4 (b' := o + 23) rfl
  exact
  { hreb := by simpa using (hs.block (gs := [outbRebTabF rg inv (o + 8)]) 0 rfl).single
    hreb1 := (hs.block
      (gs := [outbRebOneF mp_conj (o + 2) comp (o + 17) inv (o + 20) red]) 1 rfl).single
    hmp_reb := h0.left
    hwh := (hs.block (gs := [tmRpWhileF (o + 2) (o + 3)]) 2 rfl).single
    hround :=
      { step := (hs.block (gs := [tmRpStepF (o + 11)]) 3 rfl).single
        fold := h1.left
        test := (hs.block (gs := [tmRpTestF (o + 14) comp]) 4 rfl).single
        any := h2.left
        pred := (hs.block (gs := [tmRpPredF jm comp inv]) 5 rfl).single
        mem := h.hjm
        comp := h.hcomp
        inv := h.hinv }
    hsch :=
      { hfb_sch := h4.left
        hsrow := (hs.block (gs := [outbSchRowF (o + 23) app]) 6 rfl).single
        hmg := h5
        hsgen := (hs.block (gs := [outbSchGenF (o + 17) comp inv]) 7 rfl).single
        happ := h.happ
        hfnd := h3.left
        hpt := (hs.block (gs := [tmRpPredF jm comp inv]) 5 rfl).single
        hjm := h.hjm
        hcomp := h.hcomp
        hinv := h.hinv }
    hrg := h.hrg
    hred := h.hred
    hmp_conj := h.hmp_conj
    hconj := h.hconj }

/-- **Rebasing the full coset table `vs`** from `OutbRebPlaced`. -/
theorem outbReb_spec (hst : PointwiseStab) (hm : Membership) {P : Program}
    {o comp inv rg app red mp_conj conj jst jm : ℕ}
    (h : OutbRebPlaced P hm o comp inv rg app red mp_conj conj jst jm)
    (hjst : P.prims[jst]? = some (pointwiseStabPrim hst))
    {H R : Subgroup (Perm (Fin m))} (hRH : R ≤ H)
    {hsR : List (Perm (Fin m))} (hlR : hsR.length ≤ m ^ 2) (hgR : gens hsR = R)
    {r : Perm (Fin m)} (hr : r ∈ H)
    {q : ℕ} {Ω : Type*} [RAct (Perm (Fin m)) Ω] {x y : Fin q → Ω} {vs : List Val}
    (hT : TmCsTabOK H x y vs)
    {X : ℕ} (hmX : m ≤ X) (hqX : q ≤ X)
    (hidxX : (R.subgroupOf H).index ≤ X) :
    FunAll P o (.list [encGroup hsR, .nat m, encPerm r, .list vs]) (fun w' cost =>
      (∃ vs', w' = .list vs' ∧ TmCsTabOK R x (fun j => y j ↼ r⁻¹) vs' ∧
        (Val.list vs').wt ≤ 3000 * (X + 1) ^ 8) ∧
        cost ≤ outbRebK (pointwiseStabPrim hst) hm X) :=
  outbRebTab_spec hst hm (outbRebAt_of h) hjst hRH hlR hgR hr hT hmX hqX hidxX

end GI.Impl
