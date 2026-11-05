module

public import Workspace.Impl.TermJProgTl
public import Workspace.Impl.TermJProgYg4

@[expose] public section

/-!
# The even products of lifted transpositions (program)

`Aut_J(x)` gets the generators `t₀ t` for the lifted transpositions `t` of two different rows,
where `t₀` is the first of them (`tmJ_autJ_gens`). This file maps over the list `Tl` of
triples `(a, a', b)` and returns `t₀ · tmJSw a a' b` for each.

`tmJ_ts_spec`: on `[[lc, t₀], Tl]` the program returns these products on `Fin (m q)`.
-/

namespace GI.Impl

open GI.Lang GI.Assembly Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens)

variable {m q : ℕ}

/-- On `[[lc, t₀], [a, a', b]]`: `t₀ · tmJSw a a' b`. -/
def tmJTsEF (sw cp : ℕ) : Expr :=
  .call cp (mk2 (.get (arg 0) (.nat 1))
    (.call sw (mk4 (.get (arg 1) (.nat 2)) (.get (arg 0) (.nat 0)) (.get (arg 1) (.nat 0))
      (.get (arg 1) (.nat 1)))))

/-- The cost of one product. -/
def tmJTsEK (W Y : ℕ) : ℕ := tmJLocK W + permK * W ^ 3 + 100 * (Y + 10 * W ^ 2 + 20)

theorem tmJ_tsE_spec {P : Program} {f sw cp iv tbD swDE tbP swPE pr prg prt prte : ℕ}
    (hf : P.funs[f]? = some (tmJTsEF sw cp))
    (hsw : P.funs[sw]? = some (tmJSwSF iv tbD tbP pr)) (hiv : P.HasAt iv (invFuns iv))
    (htbD : P.HasAt tbD (mapFuns tbD swDE)) (hswDE : P.funs[swDE]? = some tmJSwDEF)
    (htbP : P.HasAt tbP (mapFuns tbP swPE)) (hswPE : P.funs[swPE]? = some tmJSwPEF)
    (hpr : TmJPairAt P pr prg prt prte) (hcp : P.HasAt cp (composeFuns cp))
    (t0 : Perm (Fin m × Fin q)) (x : Fin q × Fin q × Perm (Fin m)) :
    FunDet P f (.list [.list [tmJLocCtx m q,
        encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) t0)], tmJTrVal x])
      (encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
        (t0 * tmJSw x.1 x.2.1 x.2.2)))
      (tmJTsEK ((m + 1) * (q + 1)) ((Val.list [.list [tmJLocCtx m q,
        encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) t0)], tmJTrVal x]).wt)) := by
  refine FunDet.intro hf ?_
  unfold tmJTsEF
  obtain ⟨a, a', b⟩ := x
  set T := encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) t0)
  set X := Val.list [.list [tmJLocCtx m q, T], tmJTrVal (a, a', b)]
  have d0 := Det.arg' (P := P) (vs := [.list [tmJLocCtx m q, T], tmJTrVal (a, a', b)])
    (rest := []) (j := 0) (v := .list [tmJLocCtx m q, T]) rfl
  have d1 := Det.arg' (P := P) (vs := [.list [tmJLocCtx m q, T], tmJTrVal (a, a', b)])
    (rest := []) (j := 1) (v := tmJTrVal (a, a', b)) rfl
  have dlc := Det.get' d0 (Det.nat 0) (vs := [tmJLocCtx m q, T]) (v := tmJLocCtx m q) rfl
  have dT := Det.get' d0 (Det.nat 1) (vs := [tmJLocCtx m q, T]) (v := T) rfl
  have da := Det.get' d1 (Det.nat 0) (vs := [.nat a, .nat a', encPerm b]) (v := .nat a) rfl
  have da' := Det.get' d1 (Det.nat 1) (vs := [.nat a, .nat a', encPerm b]) (v := .nat a') rfl
  have db := Det.get' d1 (Det.nat 2) (vs := [.nat a, .nat a', encPerm b]) (v := encPerm b) rfl
  have dsw := Det.call (Det.mk4 db dlc da da')
    (tmJ_swS_spec hsw hiv htbD hswDE htbP hswPE hpr a a' b)
  have dc := Det.call (Det.mk2 dT dsw) (compose_spec hcp _ _)
  rw [← map_mul] at dc
  refine dc.mono ?_
  -- the cost
  have hmq : m * q + 1 ≤ (m + 1) * (q + 1) := by nlinarith
  set W := (m + 1) * (q + 1)
  have hW2 : (m * q + 1) ^ 2 ≤ W ^ 2 := Nat.pow_le_pow_left hmq 2
  have hW3 : (m * q + 1) ^ 3 ≤ W ^ 3 := Nat.pow_le_pow_left hmq 3
  have wX0 : (Val.list [tmJLocCtx m q, T]).wt < X.wt := wt_le_wt_list (by simp)
  have wX1 : (tmJTrVal (a, a', b)).wt < X.wt := wt_le_wt_list (by simp)
  have wlc : (tmJLocCtx m q).wt < (Val.list [tmJLocCtx m q, T]).wt := wt_le_wt_list (by simp)
  have wT : T.wt < (Val.list [tmJLocCtx m q, T]).wt := wt_le_wt_list (by simp)
  have wa : (Val.nat a).wt < (tmJTrVal (a, a', b)).wt := wt_le_wt_list (by simp)
  have wa' : (Val.nat a').wt < (tmJTrVal (a, a', b)).wt := wt_le_wt_list (by simp)
  have wb : (encPerm b).wt < (tmJTrVal (a, a', b)).wt := wt_le_wt_list (by simp)
  have w0 := wt_nat_le 0
  have w1 := wt_nat_le 1
  have w2 := wt_nat_le 2
  have wsw := wt_encPerm_le (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
    (tmJSw a a' b))
  have wT' : T.wt ≤ 4 * (m * q + 1) ^ 2 := wt_encPerm_le _
  have wout := wt_encPerm_le (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
    (t0 * tmJSw a a' b))
  have w4 := wt_list4_le (encPerm b) (tmJLocCtx m q) (.nat a) (.nat a')
  have w2' := wt_list2_le T (encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
    (tmJSw a a' b)))
  have hpK : permK * (m * q + 1) ^ 3 ≤ permK * W ^ 3 := Nat.mul_le_mul_left _ hW3
  have wlc' := wt_tmJLocCtx_le m q
  have eW : ((m + 1) * (q + 1)) ^ 2 = W ^ 2 := rfl
  have eX : (Val.list [Val.list [tmJLocCtx m q, T], tmJTrVal (a, a', b)]).wt = X.wt := rfl
  unfold tmJTsEK
  omega

/-- On `[c, Tl]` with `c = [lc, t₀]`: map `tmJTsEF` over `Tl`. -/
def tmJTsF (mp : ℕ) : Expr := .call mp (mk2 (arg 0) (arg 1))

/-- The products for every triple of `Tl`. -/
def tmJTsList (t0 : Perm (Fin m × Fin q)) (Tl : List (Fin q × Fin q × Perm (Fin m))) :
    List (Perm (Fin m × Fin q)) :=
  Tl.map fun x => t0 * tmJSw x.1 x.2.1 x.2.2

theorem tmJ_ts_spec {P : Program} {f mp e sw cp iv tbD swDE tbP swPE pr prg prt prte : ℕ}
    (hf : P.funs[f]? = some (tmJTsF mp)) (hmp : P.HasAt mp (mapFuns mp e))
    (he : P.funs[e]? = some (tmJTsEF sw cp))
    (hsw : P.funs[sw]? = some (tmJSwSF iv tbD tbP pr)) (hiv : P.HasAt iv (invFuns iv))
    (htbD : P.HasAt tbD (mapFuns tbD swDE)) (hswDE : P.funs[swDE]? = some tmJSwDEF)
    (htbP : P.HasAt tbP (mapFuns tbP swPE)) (hswPE : P.funs[swPE]? = some tmJSwPEF)
    (hpr : TmJPairAt P pr prg prt prte) (hcp : P.HasAt cp (composeFuns cp))
    (t0 : Perm (Fin m × Fin q)) (Tl : List (Fin q × Fin q × Perm (Fin m))) :
    FunDet P f (.list [.list [tmJLocCtx m q,
        encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) t0)], tmJTlVal Tl])
      (tmJPermsVal (tmJTsList t0 Tl))
      (Tl.length * tmJTsEK ((m + 1) * (q + 1)) (2 * ((Val.list [tmJLocCtx m q,
          encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) t0)]).wt +
          (tmJTlVal Tl).wt) + 6) +
        mapK * (Tl.length + 1) * ((Val.list [.list [tmJLocCtx m q,
          encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) t0)], tmJTlVal Tl]).wt +
          (tmJPermsVal (tmJTsList t0 Tl)).wt + 1) +
        (Val.list [.list [tmJLocCtx m q,
          encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) t0)], tmJTlVal Tl]).wt *
          10 + 2 * (tmJPermsVal (tmJTsList t0 Tl)).wt + 20) := by
  refine FunDet.intro hf ?_
  unfold tmJTsF
  set c := Val.list [tmJLocCtx m q,
    encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) t0)]
  have d0 := Det.arg' (P := P) (vs := [c, tmJTlVal Tl]) (rest := []) (j := 0) (v := c) rfl
  have d1 := Det.arg' (P := P) (vs := [c, tmJTlVal Tl]) (rest := []) (j := 1)
    (v := tmJTlVal Tl) rfl
  have hM := mapList_spec hmp Tl tmJTrVal (fun x => encPerm (toFin
      (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (t0 * tmJSw x.1 x.2.1 x.2.2))) (c := c)
    (B := tmJTsEK ((m + 1) * (q + 1)) (2 * (c.wt + (tmJTlVal Tl).wt) + 6))
    (fun x _ x' _ hx => by
      obtain ⟨a, a', b⟩ := x
      obtain ⟨a2, a2', b2⟩ := x'
      simp only [tmJTrVal, Val.list.injEq, List.cons.injEq, Val.nat.injEq] at hx
      obtain ⟨h1, h2, h3, -⟩ := hx
      have e1 : a = a2 := Fin.ext h1
      have e2 : a' = a2' := Fin.ext h2
      rw [e1, e2, encPerm_injective h3])
    (fun x hx => (tmJ_tsE_spec he hsw hiv htbD hswDE htbP hswPE hpr hcp t0 x).mono (by
      unfold tmJTsEK
      have e : (Val.list [Val.list [tmJLocCtx m q, encPerm (toFin
          (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) t0)], tmJTrVal x]).wt =
          (Val.list [c, tmJTrVal x]).wt := rfl
      have := wt_list2_le c (tmJTrVal x)
      have : (tmJTrVal x).wt < (tmJTlVal Tl).wt := wt_le_wt_list (List.mem_map.2 ⟨x, hx, rfl⟩)
      omega))
  have dall := Det.call (Det.mk2 d0 d1) hM
  have hval : Val.list (Tl.map fun x => encPerm (toFin
      (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (t0 * tmJSw x.1 x.2.1 x.2.2))) =
      tmJPermsVal (tmJTsList t0 Tl) := by
    simp only [tmJPermsVal, tmJTsList, List.map_map]; rfl
  rw [hval] at dall
  refine dall.mono ?_
  rw [show Val.list [c, Val.list (Tl.map tmJTrVal)] = Val.list [c, tmJTlVal Tl] from rfl]
  have w2 := wt_list2_le c (tmJTlVal Tl)
  have wc : c.wt < (Val.list [c, tmJTlVal Tl]).wt := wt_le_wt_list (by simp)
  have wt' : (tmJTlVal Tl).wt < (Val.list [c, tmJTlVal Tl]).wt := wt_le_wt_list (by simp)
  have w22 := wt_list2_le c c
  omega

end GI.Impl
