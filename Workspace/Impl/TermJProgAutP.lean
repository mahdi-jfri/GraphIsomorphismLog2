module

public import Workspace.Impl.TermJProgPrep
public import Workspace.Impl.TermJProgNs
public import Workspace.Impl.TermJProgTs
public import Workspace.Impl.TermJProgS2

@[expose] public section

/-!
# Polynomial forms of the step specifications used for `Aut_J`

The program for the generators of `Aut_J(x)` calls the row stabilizers `ns`
(`tmJ_ns_spec`), the lifted transposition `tmJSw` of the first triple (`tmJ_swS_spec`), the
products `t₀ t` (`tmJ_ts_spec`) and `append`. This file restates their costs in the form
`K (w + 1)^D`, with `w` the weight of the input, so that the costs compose by `TmJPoly`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv
open GI.Cited (Val encPerm encGroup encPerms gens NormalizedIntersection)

variable {m q : ℕ}

private theorem tmJAP_lt_wt {n : ℕ} (σ : Equiv.Perm (Fin n)) : n < (encPerm σ).wt := by
  have h := length_lt_wt_list ((List.finRange n).map fun i => Val.nat (σ i))
  simp only [List.length_map, List.length_finRange] at h
  exact h

theorem tmJ_mq_le_wt (m q : ℕ) : (m + 1) * (q + 1) ≤ ((tmJLocCtx m q).wt + 1) ^ 2 := by
  have hm : m < (tmJLocCtx m q).wt :=
    (tmJAP_lt_wt (1 : Equiv.Perm (Fin m))).trans (wt_le_wt_list (by simp))
  have hq : q < (tmJLocCtx m q).wt :=
    (tmJAP_lt_wt (1 : Equiv.Perm (Fin q))).trans (wt_le_wt_list (by simp))
  rw [sq]
  exact Nat.mul_le_mul (by omega) (by omega)

/-- `append_spec` as a deterministic call with a polynomial cost. -/
theorem tmJ_app_det {P : Program} {b : ℕ} (h : P.HasAt b (appendFuns b)) (xs ys : List Val) :
    FunDet P b (.list [.list xs, .list ys]) (.list (xs ++ ys))
      (6 * loopModK * ((Val.list [.list xs, .list ys]).wt + 1) ^ 2) := by
  refine (append_spec h xs ys).mono fun w c hw => ⟨hw.1, ?_⟩
  obtain ⟨rfl, hc⟩ := hw
  obtain ⟨W, hW⟩ : ∃ W, (Val.list [.list xs, .list ys]).wt = W := ⟨_, rfl⟩
  rw [hW] at hc ⊢
  have hx : (Val.list xs).wt < W := hW ▸ wt_le_wt_list (by simp)
  have hy : (Val.list ys).wt < W := hW ▸ wt_le_wt_list (by simp)
  have ly := length_lt_wt_list ys
  have lx := length_lt_wt_list xs
  have sx := sum_wt_lt_wt_list xs
  have sy := sum_wt_lt_wt_list ys
  have sxy := sum_wt_lt_wt_list [Val.list xs, Val.list ys]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at sxy
  rw [hW] at sxy
  have ho : (Val.list (xs ++ ys)).wt ≤ 3 * W + 4 := by
    have := wt_list_le (xs ++ ys)
    simp only [List.map_append, List.sum_append, List.length_append] at this
    omega
  calc c ≤ loopModK * (ys.length + 1) * (W + ys.length + (Val.list (xs ++ ys)).wt + 1) := hc
    _ ≤ loopModK * (W + 1) * (6 * (W + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    _ = 6 * loopModK * (W + 1) ^ 2 := by ring

/-- The cost of the lifted transposition of one triple. -/
theorem tmJ_swS_det {P : Program} {f iv tbD swDE tbP swPE pr prg prt prte : ℕ}
    (hf : P.funs[f]? = some (tmJSwSF iv tbD tbP pr)) (hiv : P.HasAt iv (invFuns iv))
    (htbD : P.HasAt tbD (mapFuns tbD swDE)) (hswDE : P.funs[swDE]? = some tmJSwDEF)
    (htbP : P.HasAt tbP (mapFuns tbP swPE)) (hswPE : P.funs[swPE]? = some tmJSwPEF)
    (hpr : TmJPairAt P pr prg prt prte) (a a' : Fin q) (b : Perm (Fin m)) :
    FunDet P f (.list [encPerm b, tmJLocCtx m q, .nat a, .nat a'])
      (encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJSw a a' b)))
      (10 ^ 14 * ((Val.list [encPerm b, tmJLocCtx m q, .nat a, .nat a']).wt + 1) ^ 16) := by
  refine (tmJ_swS_spec hf hiv htbD hswDE htbP hswPE hpr a a' b).mono ?_
  have h1 := tmJ_mq_le_wt m q
  have h2 : (tmJLocCtx m q).wt < (Val.list [encPerm b, tmJLocCtx m q, .nat a, .nat a']).wt :=
    wt_le_wt_list (by simp)
  unfold tmJLocK
  calc 10 ^ 14 * ((m + 1) * (q + 1)) ^ 8 ≤ 10 ^ 14 * (((tmJLocCtx m q).wt + 1) ^ 2) ^ 8 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)
    _ ≤ 10 ^ 14 * (((Val.list [encPerm b, tmJLocCtx m q, .nat a, .nat a']).wt + 1) ^ 2) ^ 8 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.pow_le_pow_left (by omega) _) _)
    _ = _ := by rw [← pow_mul]

/-- The bound of `tmJ_ts_spec` in the input weight. -/
def tmJTsPK (W : ℕ) : ℕ :=
  W * (10 ^ 14 * ((W + 1) ^ 2) ^ 8 + permK * ((W + 1) ^ 2) ^ 3 +
      100 * (2 * (W + W) + 6 + 10 * ((W + 1) ^ 2) ^ 2 + 20)) +
    mapK * (W + 1) * (W + (W * (8 * ((W + 1) ^ 2) ^ 2 + 1) + 4) + 1) +
    W * 10 + 2 * (W * (8 * ((W + 1) ^ 2) ^ 2 + 1) + 4) + 20

theorem tmJTsPK_poly : TmJPoly tmJTsPK := by
  have hW : TmJPoly fun W => W := TmJPoly.id
  have hS : TmJPoly fun W => (W + 1) ^ 2 := TmJPoly.pow (TmJPoly.add hW (TmJPoly.const 1)) 2
  have hO : TmJPoly fun W => W * (8 * ((W + 1) ^ 2) ^ 2 + 1) + 4 :=
    TmJPoly.add (TmJPoly.mul hW (TmJPoly.add (TmJPoly.smul 8 (TmJPoly.pow hS 2))
      (TmJPoly.const 1))) (TmJPoly.const 4)
  unfold tmJTsPK
  refine TmJPoly.add (TmJPoly.add (TmJPoly.add (TmJPoly.add ?_ ?_) (TmJPoly.smul 10 hW |>.mono
    fun W => by rw [mul_comm])) (TmJPoly.smul 2 hO)) (TmJPoly.const 20)
  · exact TmJPoly.mul hW (TmJPoly.add (TmJPoly.add (TmJPoly.smul _ (TmJPoly.pow hS 8))
      (TmJPoly.smul _ (TmJPoly.pow hS 3))) (TmJPoly.smul 100 (TmJPoly.add (TmJPoly.add
        (TmJPoly.add (TmJPoly.smul 2 (TmJPoly.add hW hW)) (TmJPoly.const 6))
        (TmJPoly.smul 10 (TmJPoly.pow hS 2))) (TmJPoly.const 20))))
  · exact TmJPoly.mul (TmJPoly.smul _ (TmJPoly.add hW (TmJPoly.const 1)))
      (TmJPoly.add (TmJPoly.add hW hO) (TmJPoly.const 1))

/-- `tmJ_ts_spec` with the bound `tmJTsPK` of the input weight. -/
theorem tmJ_ts_det {P : Program} {f mp e sw cp iv tbD swDE tbP swPE pr prg prt prte : ℕ}
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
      (tmJTsPK (Val.list [.list [tmJLocCtx m q,
        encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) t0)], tmJTlVal Tl]).wt) := by
  refine (tmJ_ts_spec hf hmp he hsw hiv htbD hswDE htbP hswPE hpr hcp t0 Tl).mono ?_
  obtain ⟨X0, hX0⟩ : ∃ X0, Val.list [tmJLocCtx m q,
      encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) t0)] = X0 := ⟨_, rfl⟩
  rw [hX0]
  obtain ⟨W, hW⟩ : ∃ W, (Val.list [X0, tmJTlVal Tl]).wt = W := ⟨_, rfl⟩
  rw [hW]
  have hX : X0.wt < W := hW ▸ wt_le_wt_list (by simp)
  have hT : (tmJTlVal Tl).wt < W := hW ▸ wt_le_wt_list (by simp)
  have hlen : Tl.length < W := by
    have := length_lt_wt_list (Tl.map tmJTrVal)
    simp only [List.length_map] at this
    exact this.trans (by simpa [tmJTlVal] using hT)
  have hlc : (tmJLocCtx m q).wt < W := by
    have : (tmJLocCtx m q).wt < X0.wt := hX0 ▸ wt_le_wt_list (by simp)
    omega
  have hmq : (m + 1) * (q + 1) ≤ (W + 1) ^ 2 :=
    (tmJ_mq_le_wt m q).trans (Nat.pow_le_pow_left (by omega) 2)
  have hmq' : m * q + 1 ≤ (W + 1) ^ 2 := le_trans (by nlinarith) hmq
  have hO : (tmJPermsVal (tmJTsList t0 Tl)).wt ≤ W * (8 * ((W + 1) ^ 2) ^ 2 + 1) + 4 := by
    have := wt_tmJPermsVal_le (tmJTsList t0 Tl)
    simp only [tmJTsList, List.length_map] at this
    refine this.trans ?_
    gcongr
  unfold tmJTsPK tmJTsEK tmJLocK
  gcongr

theorem tmJ_boundSize_mono (p : Prim) {B B' : ℕ} (h : B ≤ B') : p.boundSize B ≤ p.boundSize B' :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

/-- The bound of `tmJ_ns_spec` in the input weight. -/
def tmJNsPK (p : Prim) (W : ℕ) : ℕ :=
  (W + W + (W + 1) ^ 2) * p.boundSize (2 * (W + W + (W + 1) ^ 2) + 6) +
    tmJNsK (W + W + (W + 1) ^ 2)

theorem tmJNsPK_poly (p : Prim) : TmJPoly (tmJNsPK p) := by
  have hW : TmJPoly fun W => W := TmJPoly.id
  have hV : TmJPoly fun W => W + W + (W + 1) ^ 2 :=
    TmJPoly.add (TmJPoly.add hW hW) (TmJPoly.pow (TmJPoly.add hW (TmJPoly.const 1)) 2)
  unfold tmJNsPK Prim.boundSize tmJNsK
  exact TmJPoly.add (TmJPoly.mul hV (TmJPoly.smul _ (TmJPoly.pow (TmJPoly.add (TmJPoly.add
    (TmJPoly.smul 2 hV) (TmJPoly.const 6)) (TmJPoly.const 2)) _)))
    (TmJPoly.smul _ (TmJPoly.pow hV _))

/-- `tmJ_ns_spec` with the bound `tmJNsPK` of the input weight. -/
theorem tmJ_ns_all (hni : NormalizedIntersection) {P : Program}
    {f rg mpR row ni mp locA dsA tbA tbe pr prg prt prte fl app : ℕ}
    (hA : TmJNsAt P f rg mpR row ni mp locA dsA tbA tbe pr prg prt prte fl app)
    (hj : P.prims[ni]? = some (normalizedIntersectionPrim hni))
    (O : Fin q → Fin q → Option (Perm (Fin m) × List (Perm (Fin m)))) (us : List Val)
    (hus : ∀ a a' : Fin q, us[(a : ℕ) * (2 * q) + a']? = some (tmJEntVal (O a a')))
    (σS : List (Perm (Fin m)))
    (hloc : ∀ a, ∃ r gs, O a a = some (r, gs) ∧ GI.Multicoset.Normalizes (gens gs) (gens σS)) :
    FunAll P f (.list [.list us, tmJLocCtx m q, encGroup σS]) (fun out cost =>
      (∃ hsA : Fin q → List (Perm (Fin m)), out = tmJPermsVal (tmJNsList hsA) ∧
        ∀ a r gs, O a a = some (r, gs) → gens (hsA a) = gens gs ⊓ gens σS) ∧
      cost ≤ tmJNsPK (normalizedIntersectionPrim hni)
        (Val.list [.list us, tmJLocCtx m q, encGroup σS]).wt) := by
  refine (tmJ_ns_spec hni hA hj O us hus σS hloc).mono fun out cost h => ⟨h.1, h.2.trans ?_⟩
  obtain ⟨W, hW⟩ : ∃ W, (Val.list [.list us, tmJLocCtx m q, encGroup σS]).wt = W := ⟨_, rfl⟩
  rw [hW]
  have h1 : (Val.list us).wt < W := hW ▸ wt_le_wt_list (by simp)
  have h2 : (encGroup σS).wt < W := hW ▸ wt_le_wt_list (by simp)
  have h3 : (tmJLocCtx m q).wt < W := hW ▸ wt_le_wt_list (by simp)
  have hmq : (m + 1) * (q + 1) ≤ (W + 1) ^ 2 :=
    (tmJ_mq_le_wt m q).trans (Nat.pow_le_pow_left (by omega) 2)
  have hV : (Val.list us).wt + (encGroup σS).wt + (m + 1) * (q + 1) ≤ W + W + (W + 1) ^ 2 := by
    omega
  unfold tmJNsPK
  exact Nat.add_le_add (Nat.mul_le_mul hV (tmJ_boundSize_mono _ (by omega)))
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hV _))

end GI.Impl
