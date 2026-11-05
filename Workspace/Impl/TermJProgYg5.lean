module

public import Workspace.Impl.TermJProgYg4

@[expose] public section

/-!
# The generators of `Aut_{N ≀ Sym(q)}(X)` (program, main function)

`tmJYgF`, on `[us, q, m]`: the locals of all rows (tabulated, then flattened), then the
transpositions (tabulated), appended. `tmJ_yg_spec`: the result is `tmJPermsVal (tmJYgList O)`.
`TmJYgAt` lists where the pieces sit, and `TmJYgAt.of_hasAt` builds it from the own functions
`tmJYgFuns` at a base `b` and the library modules.
-/

namespace GI.Impl

open GI.Lang GI.Assembly Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens)

/-! ### The number of generators -/

/-- **The number of generators** is at most `q · wt us + q²`. -/
theorem tmJYgList_length_le {m q : ℕ}
    (O : Fin q → Fin q → Option (Perm (Fin m) × List (Perm (Fin m))))
    (hloc : ∀ a, ∃ r gs, O a a = some (r, gs)) (us : List Val)
    (hus : ∀ a a' : Fin q, us[(a : ℕ) * (2 * q) + a']? = some (tmJEntVal (O a a'))) :
    (tmJYgList O).length ≤ q * (Val.list us).wt + q * q := by
  have hrow : ∀ a : Fin q, (tmJYgLoc O a).length ≤ (Val.list us).wt := by
    intro a
    obtain ⟨r, gs, hO⟩ := hloc a
    have hu : us[(a : ℕ) * (2 * q) + a]? = some (.list [encPerm r, encGroup gs]) := by
      rw [hus a a, hO]; rfl
    exact (tmJYgLoc_length_lt O a hO hu).le
  have hs : (((List.finRange q).map (tmJYgLoc O)).map List.length).sum ≤
      q * (Val.list us).wt := by
    have := List.sum_le_card_nsmul (((List.finRange q).map (tmJYgLoc O)).map List.length)
      (Val.list us).wt (by
        intro x hx
        simp only [List.map_map, List.mem_map, List.mem_finRange, true_and,
          Function.comp_apply] at hx
        obtain ⟨a, rfl⟩ := hx
        exact hrow a)
    simpa using this
  unfold tmJYgList
  rw [List.length_append, List.length_flatten, List.length_map, List.length_finRange]
  omega

/-! ### The main function -/

/-- On `[us, q, m]`: the locals of all rows, then the transpositions. -/
def tmJYgF (rg tbR fl tbS ap : ℕ) : Expr :=
  .letE (.call rg (arg 2))
  (.letE (.call rg (arg 1))
  (.letE (mk2 (arg 0) (mk4 (.var 1) (.var 2) (arg 1) (arg 2)))
  (.letE (.call fl (.call tbR (mk2 (.var 3) (.var 2))))
  (.call ap (mk2 (.var 4) (.call tbS (mk2 (.var 3)
    (.call rg (.arith .mul (arg 1) (arg 1))))))))))

/-- The own functions, in order: main, the pieces of the locals, the pieces of the
transpositions, the flattening (with its `foldl` module and step). They sit at `b, …, b + 13`. -/
def tmJYgFuns (b rg ap iv tbA mpL tbR tbD tbP tbS pr : ℕ) : List Expr :=
  [tmJYgF rg tbR (b + 9) tbS ap, tmJDsAEF, tmJDsAF rg tbA, tmJLocAF (b + 2) pr, tmJRowLocF mpL,
    tmJSwDEF, tmJSwPEF, tmJSwSF iv tbD tbP pr, tmJSwF rg (b + 7), tmJFlatF (b + 10)] ++
    foldlFuns (b + 10) (b + 13) ++ [tmJFlatStepF ap]

theorem tmJYgFuns_length (b rg ap iv tbA mpL tbR tbD tbP tbS pr : ℕ) :
    (tmJYgFuns b rg ap iv tbA mpL tbR tbD tbP tbS pr).length = 14 := rfl

/-- Where the pieces sit: the own functions at `b, …, b + 13`, and the library modules. -/
structure TmJYgAt (P : Program) (b rg ap iv tbA mpL tbR tbD tbP tbS pr prg prt prte : ℕ) :
    Prop where
  hmain : P.funs[b]? = some (tmJYgF rg tbR (b + 9) tbS ap)
  hdsAE : P.funs[b + 1]? = some tmJDsAEF
  hdsA : P.funs[b + 2]? = some (tmJDsAF rg tbA)
  hlocA : P.funs[b + 3]? = some (tmJLocAF (b + 2) pr)
  hrow : P.funs[b + 4]? = some (tmJRowLocF mpL)
  hswDE : P.funs[b + 5]? = some tmJSwDEF
  hswPE : P.funs[b + 6]? = some tmJSwPEF
  hswS : P.funs[b + 7]? = some (tmJSwSF iv tbD tbP pr)
  hsw : P.funs[b + 8]? = some (tmJSwF rg (b + 7))
  hflat : P.funs[b + 9]? = some (tmJFlatF (b + 10))
  hfl : P.HasAt (b + 10) (foldlFuns (b + 10) (b + 13))
  hst : P.funs[b + 13]? = some (tmJFlatStepF ap)
  hrg : P.HasAt rg (rangeFuns rg)
  hap : P.HasAt ap (appendFuns ap)
  hiv : P.HasAt iv (invFuns iv)
  htbA : P.HasAt tbA (mapFuns tbA (b + 1))
  hmpL : P.HasAt mpL (mapFuns mpL (b + 3))
  htbR : P.HasAt tbR (mapFuns tbR (b + 4))
  htbD : P.HasAt tbD (mapFuns tbD (b + 5))
  htbP : P.HasAt tbP (mapFuns tbP (b + 6))
  htbS : P.HasAt tbS (mapFuns tbS (b + 8))
  hpr : TmJPairAt P pr prg prt prte

/-- The own functions at `b` and the library modules give `TmJYgAt`. -/
theorem TmJYgAt.of_hasAt {P : Program} {b rg ap iv tbA mpL tbR tbD tbP tbS pr prg prt prte : ℕ}
    (h : P.HasAt b (tmJYgFuns b rg ap iv tbA mpL tbR tbD tbP tbS pr))
    (hrg : P.HasAt rg (rangeFuns rg)) (hap : P.HasAt ap (appendFuns ap))
    (hiv : P.HasAt iv (invFuns iv)) (htbA : P.HasAt tbA (mapFuns tbA (b + 1)))
    (hmpL : P.HasAt mpL (mapFuns mpL (b + 3))) (htbR : P.HasAt tbR (mapFuns tbR (b + 4)))
    (htbD : P.HasAt tbD (mapFuns tbD (b + 5))) (htbP : P.HasAt tbP (mapFuns tbP (b + 6)))
    (htbS : P.HasAt tbS (mapFuns tbS (b + 8))) (hpr : TmJPairAt P pr prg prt prte) :
    TmJYgAt P b rg ap iv tbA mpL tbR tbD tbP tbS pr prg prt prte where
  hmain := by simpa [tmJYgFuns] using h 0 (by simp [tmJYgFuns, foldlFuns, loopFuns])
  hdsAE := h 1 (by simp [tmJYgFuns, foldlFuns, loopFuns])
  hdsA := h 2 (by simp [tmJYgFuns, foldlFuns, loopFuns])
  hlocA := h 3 (by simp [tmJYgFuns, foldlFuns, loopFuns])
  hrow := h 4 (by simp [tmJYgFuns, foldlFuns, loopFuns])
  hswDE := h 5 (by simp [tmJYgFuns, foldlFuns, loopFuns])
  hswPE := h 6 (by simp [tmJYgFuns, foldlFuns, loopFuns])
  hswS := h 7 (by simp [tmJYgFuns, foldlFuns, loopFuns])
  hsw := h 8 (by simp [tmJYgFuns, foldlFuns, loopFuns])
  hflat := h 9 (by simp [tmJYgFuns, foldlFuns, loopFuns])
  hfl := by simpa [tmJYgFuns] using h.left.right
  hst := by simpa [tmJYgFuns, foldlFuns, loopFuns, Nat.add_assoc] using h.right.single
  hrg := hrg
  hap := hap
  hiv := hiv
  htbA := htbA
  hmpL := hmpL
  htbR := htbR
  htbD := htbD
  htbP := htbP
  htbS := htbS
  hpr := hpr

/-- The locals of the rows, as lists of values. -/
def tmJYgRowVals {m q : ℕ} (O : Fin q → Fin q → Option (Perm (Fin m) × List (Perm (Fin m)))) :
    List (List Val) :=
  (List.finRange q).map fun a => (tmJYgLoc O a).map fun σ =>
    encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) σ)

/-- The transpositions, as values. -/
def tmJYgSwVals {m q : ℕ} (O : Fin q → Fin q → Option (Perm (Fin m) × List (Perm (Fin m)))) :
    List Val :=
  (List.finRange (q * q)).map fun t =>
    encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJYgSw O t))

/-- The cost of `tmJYgF`, in `Y = wt [us, q, m] + (m + 1) (q + 1)`. -/
def tmJYgK (Y : ℕ) : ℕ := 10 ^ 19 * Y ^ 12

/-- **The generators read off the table**, on `Fin (m q)`. -/
theorem tmJ_yg_spec {P : Program} {b rg ap iv tbA mpL tbR tbD tbP tbS pr prg prt prte : ℕ}
    (hA : TmJYgAt P b rg ap iv tbA mpL tbR tbD tbP tbS pr prg prt prte) {m q : ℕ}
    (O : Fin q → Fin q → Option (Perm (Fin m) × List (Perm (Fin m))))
    (hloc : ∀ a, ∃ r gs, O a a = some (r, gs)) (us : List Val)
    (hus : ∀ a a' : Fin q, us[(a : ℕ) * (2 * q) + a']? = some (tmJEntVal (O a a'))) :
    FunDet P b (.list [.list us, .nat q, .nat m]) (tmJPermsVal (tmJYgList O))
      (tmJYgK ((Val.list [.list us, .nat q, .nat m]).wt + (m + 1) * (q + 1))) := by
  refine FunDet.intro hA.hmain ?_
  unfold tmJYgF
  -- the steps
  have c1 := Det.call (Det.arg' (P := P) (vs := [.list us, .nat q, .nat m]) (rest := [])
    (j := 2) (v := .nat m) rfl) (tmJ_range_det hA.hrg m)
  rw [tmJ_encFun_id_eq] at c1
  have c2 := Det.call (Det.arg' (P := P) (vs := [.list us, .nat q, .nat m])
    (rest := [encPerm (1 : Perm (Fin m))]) (j := 1) (v := .nat q) rfl) (tmJ_range_det hA.hrg q)
  have a0 := Det.arg' (P := P) (vs := [.list us, .nat q, .nat m])
    (rest := [encPerm (1 : Perm (Fin m)), encFun fun i : Fin q => (i : ℕ)]) (j := 0)
    (v := .list us) rfl
  have a1 := Det.arg' (P := P) (vs := [.list us, .nat q, .nat m])
    (rest := [encPerm (1 : Perm (Fin m)), encFun fun i : Fin q => (i : ℕ)]) (j := 1)
    (v := .nat q) rfl
  have a2 := Det.arg' (P := P) (vs := [.list us, .nat q, .nat m])
    (rest := [encPerm (1 : Perm (Fin m)), encFun fun i : Fin q => (i : ℕ)]) (j := 2)
    (v := .nat m) rfl
  have v1 := Det.var' (P := P) (env := [Val.list [.list us, .nat q, .nat m],
    encPerm (1 : Perm (Fin m)), encFun fun i : Fin q => (i : ℕ)]) (i := 1)
    (v := encPerm (1 : Perm (Fin m))) rfl
  have v2 := Det.var' (P := P) (env := [Val.list [.list us, .nat q, .nat m],
    encPerm (1 : Perm (Fin m)), encFun fun i : Fin q => (i : ℕ)]) (i := 2)
    (v := encPerm (1 : Perm (Fin q))) rfl
  have c3l : Det P _ _ (tmJLocCtx m q) _ := Det.mk4 v1 v2 a1 a2
  have c3 := Det.mk2 a0 c3l
  have w3 := Det.var' (P := P) (env := [Val.list [.list us, .nat q, .nat m],
    encPerm (1 : Perm (Fin m)), encFun fun i : Fin q => (i : ℕ),
    .list [.list us, tmJLocCtx m q]]) (i := 3) (v := .list [.list us, tmJLocCtx m q]) rfl
  have w2 := Det.var' (P := P) (env := [Val.list [.list us, .nat q, .nat m],
    encPerm (1 : Perm (Fin m)), encFun fun i : Fin q => (i : ℕ),
    .list [.list us, tmJLocCtx m q]]) (i := 2) (v := encFun fun i : Fin q => (i : ℕ)) rfl
  have cR := Det.call (Det.mk2 w3 w2) (tmJ_rows_spec hA.htbR hA.hrow hA.hmpL hA.hlocA hA.hdsA
    hA.hrg hA.htbA hA.hdsAE hA.hpr O hloc us hus)
  have eR : Val.list ((List.finRange q).map fun a => tmJPermsVal (tmJYgLoc O a)) =
      Val.list ((tmJYgRowVals O).map Val.list) := by
    simp only [tmJYgRowVals, List.map_map]; rfl
  rw [eR] at cR
  have c4 := Det.call cR (tmJ_flat_spec hA.hflat hA.hfl hA.hst hA.hap (tmJYgRowVals O))
  have x4 := Det.var' (P := P) (env := [Val.list [.list us, .nat q, .nat m],
    encPerm (1 : Perm (Fin m)), encFun fun i : Fin q => (i : ℕ),
    .list [.list us, tmJLocCtx m q], .list (tmJYgRowVals O).flatten]) (i := 4)
    (v := .list (tmJYgRowVals O).flatten) rfl
  have x3 := Det.var' (P := P) (env := [Val.list [.list us, .nat q, .nat m],
    encPerm (1 : Perm (Fin m)), encFun fun i : Fin q => (i : ℕ),
    .list [.list us, tmJLocCtx m q], .list (tmJYgRowVals O).flatten]) (i := 3)
    (v := .list [.list us, tmJLocCtx m q]) rfl
  have b1 := Det.arg' (P := P) (vs := [.list us, .nat q, .nat m])
    (rest := [encPerm (1 : Perm (Fin m)), encFun fun i : Fin q => (i : ℕ),
      .list [.list us, tmJLocCtx m q], .list (tmJYgRowVals O).flatten]) (j := 1)
    (v := .nat q) rfl
  have dqq := Det.arith' (op := .mul) b1 b1 (z := q * q) rfl
  have crg := Det.call dqq (tmJ_range_det hA.hrg (q * q))
  have cS : Det P _ _ (.list (tmJYgSwVals O)) _ := Det.call (Det.mk2 x3 crg)
    (tmJ_sws_spec hA.htbS hA.hsw hA.hrg hA.hswS hA.hiv hA.htbD hA.hswDE hA.htbP hA.hswPE
      hA.hpr O us hus)
  have hval : Val.list ((tmJYgRowVals O).flatten ++ tmJYgSwVals O) = tmJPermsVal (tmJYgList O) := by
    simp only [tmJPermsVal, tmJYgList, List.map_append, List.map_flatten, List.map_map,
      tmJYgRowVals, tmJYgSwVals]
    rfl
  have hlen : (tmJYgSwVals O).length = q * q := by simp [tmJYgSwVals]
  have hAp : FunDet P ap (.list [.list (tmJYgRowVals O).flatten, .list (tmJYgSwVals O)])
      (tmJPermsVal (tmJYgList O))
      (loopModK * (q * q + 1) * ((Val.list [.list (tmJYgRowVals O).flatten,
        .list (tmJYgSwVals O)]).wt + q * q + (tmJPermsVal (tmJYgList O)).wt + 1)) :=
    FunAll.mono (append_spec hA.hap (tmJYgRowVals O).flatten (tmJYgSwVals O)) fun w c h => by
      obtain ⟨rfl, h2⟩ := h
      rw [hlen, hval] at h2
      exact ⟨hval, h2⟩
  have c5 := Det.call (Det.mk2 x4 cS) hAp
  refine (Det.letE c1 (Det.letE c2 (Det.letE c3 (Det.letE c4 c5)))).mono ?_
  clear c1 c2 a0 a1 a2 v1 v2 c3l c3 w3 w2 cR c4 x4 x3 b1 dqq crg cS hAp c5
  -- the cost
  unfold tmJYgK
  have wR := tmJYg_rows_wt O hloc us hus
  rw [eR] at wR
  have wS : (Val.list (tmJYgSwVals O)).wt ≤ 9 * ((m + 1) * (q + 1)) ^ 4 + 4 := tmJYg_sws_wt O
  have wc := wt_tmJLocCtx_le m q
  have hm1 : m + 1 ≤ (m + 1) * (q + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hq1 : q + 1 ≤ (m + 1) * (q + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hmq : m * q + 1 ≤ (m + 1) * (q + 1) := by
    have e : (m + 1) * (q + 1) = m * q + m + q + 1 := by ring
    omega
  set W := (m + 1) * (q + 1) with hW
  set V := (Val.list us).wt + W with hV
  set Y := (Val.list [.list us, .nat q, .nat m]).wt + W with hY
  clear_value W
  have hW1 : 1 ≤ W := by omega
  have hUI : (Val.list us).wt < (Val.list [.list us, .nat q, .nat m]).wt :=
    wt_le_wt_list (by simp)
  have hVY : V ≤ Y := by omega
  have hY1 : 1 ≤ Y := by omega
  have hWY : W ≤ Y := by omega
  clear_value V Y
  have hY2 : Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) _
  have hY24 : Y ^ 2 ≤ Y ^ 4 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hY46 : Y ^ 4 ≤ Y ^ 6 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hY612 : Y ^ 6 ≤ Y ^ 12 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hY1012 : Y ^ 10 ≤ Y ^ 12 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hV4 : V ^ 4 ≤ Y ^ 4 := Nat.pow_le_pow_left hVY 4
  have hV10 : V ^ 10 ≤ Y ^ 10 := Nat.pow_le_pow_left hVY 10
  have hW2 : W ^ 2 ≤ Y ^ 2 := Nat.pow_le_pow_left hWY 2
  have hW4 : W ^ 4 ≤ Y ^ 4 := Nat.pow_le_pow_left hWY 4
  have hW6 : W ^ 6 ≤ Y ^ 6 := Nat.pow_le_pow_left hWY 6
  have hm3 : (m + 1) ^ 3 ≤ W ^ 6 :=
    (Nat.pow_le_pow_left hm1 3).trans (Nat.pow_le_pow_right hW1 (by norm_num))
  have hq3 : (q + 1) ^ 3 ≤ W ^ 6 :=
    (Nat.pow_le_pow_left hq1 3).trans (Nat.pow_le_pow_right hW1 (by norm_num))
  have hm2 : (m + 1) ^ 2 ≤ W ^ 2 := Nat.pow_le_pow_left hm1 2
  have hq2 : (q + 1) ^ 2 ≤ W ^ 2 := Nat.pow_le_pow_left hq1 2
  have hqq : q * q + 1 ≤ W ^ 2 := by
    have e : (q + 1) ^ 2 = q * q + 2 * q + 1 := by ring
    omega
  have hqq3 : (q * q + 1) ^ 3 ≤ W ^ 6 := by
    have := Nat.pow_le_pow_left hqq 3
    have e : (W ^ 2) ^ 3 = W ^ 6 := by ring
    omega
  have hqq2 : (q * q + 1) ^ 2 ≤ W ^ 4 := by
    have := Nat.pow_le_pow_left hqq 2
    have e : (W ^ 2) ^ 2 = W ^ 4 := by ring
    omega
  have hW24 : W ^ 2 ≤ W ^ 4 := Nat.pow_le_pow_right hW1 (by norm_num)
  have hWW : W ≤ W ^ 2 := Nat.le_self_pow (by norm_num) _
  -- weights of the values
  have wone := wt_encPerm_le (1 : Perm (Fin m))
  have wid := wt_ids_le q
  have widqq := wt_ids_le (q * q)
  have wq := wt_nat_le q
  have wm := wt_nat_le m
  have rlc : (Val.list [encPerm (1 : Perm (Fin m)), encPerm (1 : Perm (Fin q)), .nat q,
      .nat m]).wt = (tmJLocCtx m q).wt := rfl
  have wcY := wt_list2_le (.list us) (tmJLocCtx m q)
  have wcR := wt_list2_le (.list [.list us, tmJLocCtx m q]) (encFun fun i : Fin q => (i : ℕ))
  have wcS := wt_list2_le (.list [.list us, tmJLocCtx m q])
    (encFun fun t : Fin (q * q) => (t : ℕ))
  have wF := tmJ_wt_flatten_le (tmJYgRowVals O)
  have wFS := wt_list2_le (.list (tmJYgRowVals O).flatten) (.list (tmJYgSwVals O))
  have wres := wt_tmJPermsVal_le (tmJYgList O)
  have hl := tmJYgList_length_le O hloc us hus
  have hl2 : q * (Val.list us).wt + q * q ≤ 2 * V ^ 2 := by
    have e : V ^ 2 = V * V := by ring
    have h1 : q * (Val.list us).wt ≤ V * V := Nat.mul_le_mul (by omega) (by omega)
    have h2 : q * q ≤ V * V := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hV2W : W ^ 2 ≤ V ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hmq2 : (m * q + 1) ^ 2 ≤ W ^ 2 := Nat.pow_le_pow_left hmq 2
  have wres' : (tmJPermsVal (tmJYgList O)).wt ≤ 18 * V ^ 4 + 4 := by
    have h1 : (tmJYgList O).length * (8 * (m * q + 1) ^ 2 + 1) ≤ (2 * V ^ 2) * (9 * V ^ 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : (2 * V ^ 2) * (9 * V ^ 2) = 18 * V ^ 4 := by ring
    omega
  -- the costs of the calls
  have PR : tmJYgRowsK V ≤ 10 ^ 17 * Y ^ 12 := by
    unfold tmJYgRowsK; omega
  have PS : tmJYgSwsK V ≤ 10 ^ 16 * Y ^ 12 := by
    unfold tmJYgSwsK; omega
  have PF : tmJFlatK (Val.list ((tmJYgRowVals O).map Val.list)).wt ≤ 10 ^ 11 * Y ^ 12 := by
    unfold tmJFlatK
    have h1 : (Val.list ((tmJYgRowVals O).map Val.list)).wt + 1 ≤ 41 * Y ^ 4 := by omega
    calc 10 ^ 6 * ((Val.list ((tmJYgRowVals O).map Val.list)).wt + 1) ^ 3
        ≤ 10 ^ 6 * (41 * Y ^ 4) ^ 3 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 3)
      _ = 68921000000 * Y ^ 12 := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by norm_num)
  have PA : loopModK * (q * q + 1) * ((Val.list [.list (tmJYgRowVals O).flatten,
      .list (tmJYgSwVals O)]).wt + q * q + (tmJPermsVal (tmJYgList O)).wt + 1) ≤
      10 ^ 6 * Y ^ 6 := by
    have h1 : q * q + 1 ≤ Y ^ 2 := by omega
    have h2 : (Val.list [.list (tmJYgRowVals O).flatten, .list (tmJYgSwVals O)]).wt + q * q +
        (tmJPermsVal (tmJYgList O)).wt + 1 ≤ 1000 * Y ^ 4 := by omega
    unfold loopModK
    calc 1000 * (q * q + 1) * ((Val.list [.list (tmJYgRowVals O).flatten,
          .list (tmJYgSwVals O)]).wt + q * q + (tmJPermsVal (tmJYgList O)).wt + 1)
        ≤ 1000 * Y ^ 2 * (1000 * Y ^ 4) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
      _ = 10 ^ 6 * Y ^ 6 := by ring
  have PG1 : 10000 * (m + 1) ^ 3 ≤ 10000 * Y ^ 12 := by omega
  have PG2 : 10000 * (q + 1) ^ 3 ≤ 10000 * Y ^ 12 := by omega
  have PG3 : 10000 * (q * q + 1) ^ 3 ≤ 10000 * Y ^ 12 := by omega
  have wone' := wt_encPerm_le (1 : Perm (Fin q))
  omega

end GI.Impl
