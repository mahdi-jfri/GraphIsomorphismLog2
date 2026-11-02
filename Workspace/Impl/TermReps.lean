import Workspace.Impl.TermRepsStep

/-!
# The radical coset representatives (T2, T3): `Iface.TermRepsSpec`

Corollary A.22 enumerates the right cosets of the radical preimage `R` in `H`. The program
`tmRpInner` on the terminal input `tin = [sv, lv, cv, av, rl]`:

1. the group values of `σH` and `σN` (entries 0 and 1 of `av`, `mkGroup`);
2. generators of `R = radicalPreimage ⟨σH⟩ ⟨σN⟩` (the hypothesis `TermRadSpec`, T2), turned into a
   group value;
3. the closure loop of `TermRepsStep.lean` from the list `[1]`, with the generators `σH`
   (cited **Membership** for the coset tests).

By `tmRp_final`, the result has one representative per right coset, `[H : R]` in all. The cost
is a polynomial in the weight of the input and in `[H : R]` (`tmRpCost`); with
`[H : R] ≤ m^{2 log₂ m} ≤ expLogSq 3 N` (`tm_index_le`, cited bounds of [GMP]) it lies in
`expLogSq` (`tm_reps_cost_le`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens Membership GensOf)
open GI.Multicoset (radicalPreimage)

/-- The group value of entry `i` of `av` (no reduction). -/
def tmRpGrpE (mk i : ℕ) : Expr := .call mk (mk2 tmMExpr (.get (arg 3) (.nat i)))

/-- **The body on the terminal input** `tin`. -/
def tmRpInnerF (mk grad rg wh : ℕ) : Expr :=
  .letE (tmRpGrpE mk 0)
  (.letE (tmRpGrpE mk 1)
  (.letE (.call grad (mk2 (.var 1) (.var 2)))
  (.letE (.call mk (mk2 tmMExpr (.var 3)))
  (.call wh (mk3 (mk2 (.var 4) (.get (arg 3) (.nat 0))) (.nat 0) (mk1 (.call rg tmMExpr)))))))

/-- **The entry** on `[tin, us, vs]`. -/
def tmRpEntryF (fi : ℕ) : Expr := .call fi (.get (.var 0) (.nat 0))

/-- Where the functions of T3 sit. -/
structure TmRpAt (P : Program) (hm : Membership) (f fi mk grad rg wh st fb gt ab pt jm comp inv : ℕ) :
    Prop where
  entry : P.funs[f]? = some (tmRpEntryF fi)
  inner : P.funs[fi]? = some (tmRpInnerF mk grad rg wh)
  mkg : P.HasAt mk (mkGroupFuns mk)
  rg : P.HasAt rg (rangeFuns rg)
  wh : P.funs[wh]? = some (tmRpWhileF wh st)
  round : TmRpRoundAt P hm st fb gt ab pt jm comp inv

/-- The polynomial cost of T3, for `n` cosets and an input of weight below `X`. -/
noncomputable def tmRpCost (hm : Membership) (K D n X : ℕ) : ℕ :=
  10 ^ 9 * X ^ 9 + K * (4000 * X ^ 4) ^ D +
    (n + 2) * (tmRpRoundC hm (10 ^ 3 * X ^ 6) (n + 2) +
      tmRpWK * (10 ^ 3 * X ^ 6 + n + 10 * ((n + 2) * (10 ^ 3 * X ^ 6)) + 10))

theorem tmRp_q1 {m X l : ℕ} (hmX : m + 1 ≤ X) (hl : l + 2 ≤ 2 * X) :
    ((l + 2) * (m + 1)) ^ 3 ≤ 8 * X ^ 6 :=
  calc ((l + 2) * (m + 1)) ^ 3 ≤ (2 * X * X) ^ 3 :=
        Nat.pow_le_pow_left (Nat.mul_le_mul hl hmX) 3
    _ = 8 * X ^ 6 := by ring

theorem tmRp_q2 {m X l : ℕ} (hmX : m + 1 ≤ X) (hl : l + 2 ≤ 2 * X) :
    ((l + 2) * (m + 1)) ^ 2 ≤ 4 * X ^ 4 :=
  calc ((l + 2) * (m + 1)) ^ 2 ≤ (2 * X * X) ^ 2 :=
        Nat.pow_le_pow_left (Nat.mul_le_mul hl hmX) 2
    _ = 4 * X ^ 4 := by ring

theorem tmRp_k3 {m X l : ℕ} (hl : l ≤ m ^ 2) (hmX : m + 1 ≤ X) :
    ((l + 2) * (m + 1)) ^ 3 ≤ 8 * X ^ 9 := by
  have : (l + 2) * (m + 1) ≤ 2 * X ^ 3 := by
    have h1 : l + 2 ≤ 2 * (m + 1) ^ 2 := by
      have : m ^ 2 + 1 ≤ (m + 1) ^ 2 := by nlinarith
      omega
    calc (l + 2) * (m + 1) ≤ 2 * (m + 1) ^ 2 * (m + 1) := Nat.mul_le_mul_right _ h1
      _ = 2 * (m + 1) ^ 3 := by ring
      _ ≤ 2 * X ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hmX 3)
  calc ((l + 2) * (m + 1)) ^ 3 ≤ (2 * X ^ 3) ^ 3 := Nat.pow_le_pow_left this 3
    _ = 8 * X ^ 9 := by ring

section inner

variable {Ω C : Type} {P : Program} {k : ℕ} (e : Ω ≃ Fin k) (S : State Ω C) {m q : ℕ}
  (E : Fin m × Fin q ≃ S.dom)

/-- **The body.** -/
theorem tmRpInner_spec (hm : Membership) {f fi mk grad rg wh st fb gt ab pt jm comp inv : ℕ}
    (h : TmRpAt P hm f fi mk grad rg wh st fb gt ab pt jm comp inv) {K D : ℕ}
    (hrad : Iface.TermRadSpec P K D grad) (sv lv rv : Val) (hq : 0 < q)
    (σH σN σS : List (Perm (Fin m))) (hNH : gens σN ≤ gens σH)
    (hn : GI.Multicoset.Normalizes (gens σH) (gens σN)) :
    FunAll P fi (.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0, rv]) (fun w cost =>
      ∃ reps : List (Perm (Fin m)), w = .list (reps.map encPerm) ∧
        (∃ j, TmRpInv (gens σH) (radicalPreimage (gens σH) (gens σN)) σH j reps ∧
          reps.length ≤ j) ∧
        cost ≤ tmRpCost hm K D (((radicalPreimage (gens σH) (gens σN)).subgroupOf
          (gens σH)).index) ((Val.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0, rv]).wt + 1)) := by
  set av := a18Out σH σN σS 0 with hav
  set tin := Val.list [sv, lv, coordsVal e S E, av, rv] with htin
  set X := tin.wt + 1 with hX
  set R := radicalPreimage (gens σH) (gens σN) with hRdef
  set n := (R.subgroupOf (gens σH)).index with hnI
  have hav' : av = .list [.list (σH.map encPerm), .list (σN.map encPerm), .list (σS.map encPerm),
    .nat 0] := rfl
  set L4 : List Val := [.list (σH.map encPerm), .list (σN.map encPerm), .list (σS.map encPerm),
    .nat 0] with hL4
  set T5 : List Val := [sv, lv, coordsVal e S E, av, rv] with hT5
  refine FunAll.intro h.inner ?_
  unfold tmRpInnerF tmRpGrpE
  -- 1. the group values of `σH` and `σN`
  have dσ : ∀ (rest : List Val) (i : ℕ) (σ : List (Perm (Fin m))),
      L4[i]? = some (.list (σ.map encPerm)) →
      Det P (tin :: rest) (.call mk (mk2 tmMExpr (.get (arg 3) (.nat i)))) (encGroup σ)
        (4 * tin.wt + 20 + (2 * tin.wt + 3 + 5 + (i + 3) + (Val.list (σ.map encPerm)).wt + 1) +
          2 * (Val.list [.nat m, .list (σ.map encPerm)]).wt + 7 +
          mkGroupK * ((σ.length + 2) * (m + 1)) ^ 3 + (encGroup σ).wt + 1) := by
    intro rest i σ hi
    have dm := tmM_det (P := P) e S E sv lv av rv rest hq
    have da := Det.arg' (P := P) (vs := T5) (rest := rest) (j := 3) (v := .list L4) rfl
    exact Det.call (Det.mk2 dm (Det.get' da (Det.nat i) hi)) (mkGroup_spec h.mkg σ)
  have dH := dσ [] 0 σH rfl
  refine EvalAll.letE dH fun v1 c1 hv1 => ?_
  obtain ⟨rfl, hc1⟩ := hv1
  have dN := dσ [encGroup σH] 1 σN rfl
  refine EvalAll.letE dN fun v2 c2 hv2 => ?_
  obtain ⟨rfl, hc2⟩ := hv2
  -- 2. the radical preimage
  have dHN := Det.mk2 (P := P) (env := [tin, encGroup σH, encGroup σN])
    (Det.var' (i := 1) (v := encGroup σH) rfl) (Det.var' (i := 2) (v := encGroup σN) rfl)
  refine EvalAll.letE (EvalAll.call_spec dHN (hrad σH σN hNH hn)) fun v3 c3 hv3 => ?_
  obtain ⟨cb3, ⟨⟨hs, rfl, hsl, hsR⟩, hcb3⟩, hc3⟩ := hv3
  have dmR := tmM_det (P := P) e S E sv lv av rv [encGroup σH, encGroup σN,
    .list (hs.map encPerm)] hq
  have dR := Det.call (Det.mk2 dmR (Det.var' (P := P) (i := 3) (v := .list (hs.map encPerm)) rfl))
    (mkGroup_spec h.mkg hs)
  refine EvalAll.letE dR fun v4 c4 hv4 => ?_
  obtain ⟨rfl, hc4⟩ := hv4
  -- 3. the closure loop
  set env5 : List Val := [tin, encGroup σH, encGroup σN, .list (hs.map encPerm), encGroup hs]
  have da5 := Det.arg' (P := P) (vs := T5) (rest := [encGroup σH, encGroup σN,
    .list (hs.map encPerm), encGroup hs]) (j := 3) (v := .list L4) rfl
  have dc := Det.mk2 (Det.var' (P := P) (env := env5) (i := 4) (v := encGroup hs) rfl)
    (Det.get' da5 (Det.nat 0) (show L4[0]? = some (.list (σH.map encPerm)) from rfl))
  have dm5 := tmM_det (P := P) e S E sv lv av rv [encGroup σH, encGroup σN,
    .list (hs.map encPerm), encGroup hs] hq
  have d1 := Det.mk1 (Det.call dm5 (range_det h.rg m))
  have dl := Det.mk3 dc (Det.nat 0) d1
  have hRV : GroupVal m (encGroup hs) R := ⟨hs, rfl, hsR⟩
  have hgs : ∀ g ∈ σH, g ∈ gens σH := fun g hg => Subgroup.subset_closure hg
  -- weights
  have hX1 : 1 ≤ X := by omega
  have wco : (coordsVal e S E).wt < tin.wt := wt_le_wt_list (by simp [htin])
  have wav : av.wt < tin.wt := wt_le_wt_list (by simp [htin])
  have hmX : m + 1 ≤ X := by
    have h1 := length_lt_wt_natList ((List.finRange m).map fun β =>
      ((e (E (β, ⟨0, hq⟩)).val : Fin k) : ℕ))
    have h2 : (natList ((List.finRange m).map fun β => ((e (E (β, ⟨0, hq⟩)).val : Fin k) : ℕ))).wt <
        (coordsVal e S E).wt := by
      rw [coordsVal_eq_list]
      exact wt_le_wt_list (List.mem_map.2 ⟨⟨0, hq⟩, List.mem_finRange _, rfl⟩)
    simp only [List.length_map, List.length_finRange] at h1
    omega
  have wσH : (Val.list (σH.map encPerm)).wt < av.wt := wt_le_wt_list (by simp [hav'])
  have wσN : (Val.list (σN.map encPerm)).wt < av.wt := wt_le_wt_list (by simp [hav'])
  have lσH := length_lt_wt_list (σH.map encPerm)
  have lσN := length_lt_wt_list (σN.map encPerm)
  simp only [List.length_map] at lσH lσN
  have wR := wt_encGroup_le_sq hsl
  have p1 : (m + 1) ^ 4 ≤ X ^ 6 := (Nat.pow_le_pow_left hmX 4).trans
    (Nat.pow_le_pow_right hX1 (by omega))
  have p2 : (m + 1) ^ 6 ≤ X ^ 6 := Nat.pow_le_pow_left hmX 6
  have p3 : X ≤ X ^ 6 := Nat.le_self_pow (by omega) X
  have hY : (m + 1) ^ 4 ≤ 10 ^ 3 * X ^ 6 := by omega
  have hcY : (Val.list [encGroup hs, .list (σH.map encPerm)]).wt ≤ 10 ^ 3 * X ^ 6 := by
    have := wt_list2_le (encGroup hs) (.list (σH.map encPerm)); omega
  refine (EvalAll.call_spec dl (tmRpLoop_spec hm h.wh h.round hRV hgs hY hcY)).mono ?_
  rintro w c5 ⟨cb5, ⟨reps, rfl, hinv, hcb5⟩, hc5⟩
  refine ⟨reps, rfl, hinv, ?_⟩
  obtain ⟨j, hinvj, -⟩ := hinv
  have hlen := hinvj.length_le
  rw [← hnI] at hlen hcb5
  clear dH dN dHN dR dmR dl dc d1 dm5 da5 dσ
  -- the weights of the values
  have wreps := tmRp_wt_reps hY reps (L := n + 2) (by omega)
  set Y := 10 ^ 3 * X ^ 6 with hYdef
  have hlenσH : σH.length + 2 ≤ 2 * X := by omega
  have hlenσN : σN.length + 2 ≤ 2 * X := by omega
  have k1 := tmRp_q1 hmX hlenσH
  have k2 := tmRp_q1 hmX hlenσN
  have g1 := (wt_encGroup_le σH).trans (Nat.mul_le_mul_left 40 (tmRp_q2 hmX hlenσH))
  have g2 := (wt_encGroup_le σN).trans (Nat.mul_le_mul_left 40 (tmRp_q2 hmX hlenσN))
  have k3 := tmRp_k3 hsl hmX
  have g3 := wt_list_encPerms_le_sq hsl
  have g4 := wt_encPerm_le (1 : Perm (Fin m))
  have p4 : X ^ 4 ≤ X ^ 6 := Nat.pow_le_pow_right hX1 (by omega)
  have p6 : X ^ 6 ≤ X ^ 9 := Nat.pow_le_pow_right hX1 (by omega)
  have p2' : (m + 1) ^ 2 ≤ X ^ 6 := (Nat.pow_le_pow_left hmX 2).trans
    (Nat.pow_le_pow_right hX1 (by omega))
  have p3' : (m + 1) ^ 3 ≤ X ^ 6 := (Nat.pow_le_pow_left hmX 3).trans
    (Nat.pow_le_pow_right hX1 (by omega))
  have w1 := wt_list2_le (Val.nat m) (Val.list (σH.map encPerm))
  have w2 := wt_list2_le (Val.nat m) (Val.list (σN.map encPerm))
  have w3 := wt_list2_le (Val.nat m) (Val.list (hs.map encPerm))
  have w4 := wt_list2_le (encGroup σH) (encGroup σN)
  have w5 := wt_list2_le (encGroup hs) (Val.list (σH.map encPerm))
  have w6 := wt_list1_le (encPerm (1 : Perm (Fin m)))
  have w7 := wt_list3_le (Val.list [encGroup hs, Val.list (σH.map encPerm)]) (Val.nat 0)
    (Val.list [encPerm (1 : Perm (Fin m))])
  have w0 := wt_nat_le 0
  have wm := wt_nat_le m
  have eT : (Val.list T5).wt = tin.wt := rfl
  have eT' : (Val.list [sv, lv, coordsVal e S E, av, rv]).wt = tin.wt := rfl
  have p0 : 1 ≤ X ^ 4 := Nat.one_le_pow _ _ (by omega)
  -- the radical call
  have hrc : K * ((Val.list [encGroup σH, encGroup σN]).wt + 1) ^ D ≤ K * (4000 * X ^ 4) ^ D :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  -- the loop
  set Z := (n + 1) * (tmRpRoundC hm Y (n + 2) +
    tmRpWK * (Y + n + 10 * ((n + 2) * Y) + 10)) with hZ
  have hQ : 100 * ((n + 2) * Y) ≤ tmRpRoundC hm Y (n + 2) := by
    unfold tmRpRoundC
    have : (n + 2) * Y ≤ Y * ((n + 2) * Y) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hZ2 : (n + 2) * (tmRpRoundC hm Y (n + 2) +
      tmRpWK * (Y + n + 10 * ((n + 2) * Y) + 10)) = Z + (tmRpRoundC hm Y (n + 2) +
      tmRpWK * (Y + n + 10 * ((n + 2) * Y) + 10)) := by rw [hZ]; ring
  have hX9 : X ^ 6 ≤ (n + 2) * Y := by
    have : Y ≤ (n + 2) * Y := Nat.le_mul_of_pos_left _ (by omega)
    omega
  unfold tmRpCost
  rw [← hYdef, hZ2]
  simp only [mkGroupK] at *
  clear_value Z Y
  omega
end inner

end GI.Impl
