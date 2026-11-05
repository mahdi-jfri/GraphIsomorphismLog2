module

public import Workspace.Impl.TermJProgYg3

@[expose] public section

/-!
# The generators of `Aut_{N ≀ Sym(q)}(X)` (program, part 4)

The lifted transposition of an index `t < q²` (`tmJSwF`), and all of them tabulated
(`tmJ_sws_spec`).
-/

namespace GI.Impl

open GI.Lang GI.Assembly Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens)

/-- `q`, read from `[[us, lc], t]`. -/
def tmJYgQE : Expr := .get (.get (arg 0) (.nat 1)) (.nat 2)

/-- `m`, read from `[[us, lc], t]`. -/
def tmJYgME : Expr := .get (.get (arg 0) (.nat 1)) (.nat 3)

/-- On `[[us, lc], t]`, with `a = t / q`, `a' = t % q` and `e = us[a (2q) + a']`: the identity
of `Fin (m q)` if `e` is empty, else the lifted transposition of `a, a'` and `e[0]`. -/
def tmJSwF (rg swS : ℕ) : Expr :=
  .letE (.get (.get (arg 0) (.nat 0)) (.arith .add (.arith .mul (.arith .div (arg 1) tmJYgQE)
    (.arith .mul (.nat 2) tmJYgQE)) (.arith .mod (arg 1) tmJYgQE)))
  (.ite (.length (.var 1))
    (.call swS (mk4 (.get (.var 1) (.nat 0)) (.get (arg 0) (.nat 1))
      (.arith .div (arg 1) tmJYgQE) (.arith .mod (arg 1) tmJYgQE)))
    (.call rg (.arith .mul tmJYgME tmJYgQE)))

/-- The cost of one transposition, in `V = wt us + (m + 1) (q + 1)`. -/
def tmJYgSwK (V : ℕ) : ℕ := 10 ^ 15 * V ^ 8

theorem tmJYg_fst_le {q : ℕ} (t : Fin (q * q)) : (tmJFst t : ℕ) < q := (tmJFst t).2

theorem tmJYg_snd_le {q : ℕ} (t : Fin (q * q)) : (tmJSnd t : ℕ) < q := (tmJSnd t).2

theorem tmJ_sw_spec {P : Program} {f rg swS iv tbD swDE tbP swPE pr prg prt prte : ℕ}
    (hf : P.funs[f]? = some (tmJSwF rg swS)) (hrg : P.HasAt rg (rangeFuns rg))
    (hswS : P.funs[swS]? = some (tmJSwSF iv tbD tbP pr)) (hiv : P.HasAt iv (invFuns iv))
    (htbD : P.HasAt tbD (mapFuns tbD swDE)) (hswDE : P.funs[swDE]? = some tmJSwDEF)
    (htbP : P.HasAt tbP (mapFuns tbP swPE)) (hswPE : P.funs[swPE]? = some tmJSwPEF)
    (hpr : TmJPairAt P pr prg prt prte) {m q : ℕ}
    (O : Fin q → Fin q → Option (Perm (Fin m) × List (Perm (Fin m)))) (us : List Val)
    (hus : ∀ a a' : Fin q, us[(a : ℕ) * (2 * q) + a']? = some (tmJEntVal (O a a')))
    (t : Fin (q * q)) :
    FunDet P f (.list [.list [.list us, tmJLocCtx m q], .nat t])
      (encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJYgSw O t)))
      (tmJYgSwK ((Val.list us).wt + (m + 1) * (q + 1))) := by
  refine FunDet.intro hf ?_
  unfold tmJSwF tmJYgQE tmJYgME
  have hq0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; exact t.elim0)
  have d0 := Det.arg' (P := P) (vs := [.list [.list us, tmJLocCtx m q], .nat t]) (rest := [])
    (j := 0) (v := .list [.list us, tmJLocCtx m q]) rfl
  have d1 := Det.arg' (P := P) (vs := [.list [.list us, tmJLocCtx m q], .nat t]) (rest := [])
    (j := 1) (v := .nat t) rfl
  have dus := Det.get' d0 (Det.nat 0) (vs := [.list us, tmJLocCtx m q]) (v := .list us) rfl
  have dlc := Det.get' d0 (Det.nat 1) (vs := [.list us, tmJLocCtx m q]) (v := tmJLocCtx m q) rfl
  have dq := Det.get' dlc (Det.nat 2) (vs := [encPerm (1 : Perm (Fin m)),
    encPerm (1 : Perm (Fin q)), .nat q, .nat m]) (v := .nat q) rfl
  have ddiv := Det.arith' (op := .div) d1 dq (z := (tmJFst t : ℕ)) rfl
  have dmod := Det.arith' (op := .mod) d1 dq (z := (tmJSnd t : ℕ)) rfl
  have d2q := Det.arith' (op := .mul) (Det.nat 2) dq (z := 2 * q) rfl
  have dmul := Det.arith' (op := .mul) ddiv d2q (z := (tmJFst t : ℕ) * (2 * q)) rfl
  have didx := Det.arith' (op := .add) dmul dmod
    (z := (tmJFst t : ℕ) * (2 * q) + (tmJSnd t : ℕ)) rfl
  have de := Det.get' dus didx (hus (tmJFst t) (tmJSnd t))
  -- common cost facts
  have hm1 : m + 1 ≤ (m + 1) * (q + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hq1 : q + 1 ≤ (m + 1) * (q + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hW1 : 1 ≤ (m + 1) * (q + 1) := by omega
  have hmq : m * q + 1 ≤ (m + 1) * (q + 1) := by nlinarith
  have hV1 : (m + 1) * (q + 1) ≤ (Val.list us).wt + (m + 1) * (q + 1) := by omega
  have hY1 : 1 ≤ (Val.list us).wt + (m + 1) * (q + 1) := by omega
  have hV2 : (Val.list us).wt + (m + 1) * (q + 1) ≤ ((Val.list us).wt + (m + 1) * (q + 1)) ^ 2 :=
    Nat.le_self_pow (by norm_num) _
  have hV28 : ((Val.list us).wt + (m + 1) * (q + 1)) ^ 2 ≤
      ((Val.list us).wt + (m + 1) * (q + 1)) ^ 8 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hW2 : ((m + 1) * (q + 1)) ^ 2 ≤ ((Val.list us).wt + (m + 1) * (q + 1)) ^ 2 :=
    Nat.pow_le_pow_left hV1 2
  have hW8 : ((m + 1) * (q + 1)) ^ 8 ≤ ((Val.list us).wt + (m + 1) * (q + 1)) ^ 8 :=
    Nat.pow_le_pow_left hV1 8
  have hWW : (m + 1) * (q + 1) ≤ ((m + 1) * (q + 1)) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hqq : q * q ≤ ((m + 1) * (q + 1)) ^ 2 := by
    have : q * q ≤ (q + 1) ^ 2 := by nlinarith
    have : (q + 1) ^ 2 ≤ ((m + 1) * (q + 1)) ^ 2 := Nat.pow_le_pow_left hq1 2
    omega
  have ht := t.2
  have hfs := tmJYg_fst_le t
  have hsn := tmJYg_snd_le t
  have hfq : (tmJFst t : ℕ) * (2 * q) ≤ 2 * ((m + 1) * (q + 1)) ^ 2 := by
    have : (tmJFst t : ℕ) * (2 * q) ≤ q * (2 * q) := Nat.mul_le_mul_right _ hfs.le
    have e : q * (2 * q) = 2 * (q * q) := by ring
    omega
  have hmqW : m * q ≤ ((m + 1) * (q + 1)) ^ 2 := by omega
  have wc := wt_tmJLocCtx_le m q
  have wt' := wt_nat_le t
  have wq := wt_nat_le q
  have wm := wt_nat_le m
  have w2 := wt_nat_le 2
  have wul := wt_list2_le (.list us) (tmJLocCtx m q)
  have win := wt_list2_le (.list [.list us, tmJLocCtx m q]) (.nat t)
  have wf := wt_nat_le (tmJFst t)
  have ws := wt_nat_le (tmJSnd t)
  have he : (tmJEntVal (O (tmJFst t) (tmJSnd t))).wt < (Val.list us).wt :=
    wt_le_wt_list (List.mem_of_getElem? (hus (tmJFst t) (tmJSnd t)))
  have wout := wt_encPerm_le (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
    (tmJYgSw O t))
  have hout : (m * q + 1) ^ 2 ≤ ((m + 1) * (q + 1)) ^ 2 := Nat.pow_le_pow_left hmq 2
  cases h : O (tmJFst t) (tmJSnd t) with
  | none =>
    have hsw : tmJYgSw O t = 1 := by unfold tmJYgSw; rw [h]
    rw [h] at de he
    have de' : Det P [Val.list [.list [.list us, tmJLocCtx m q], .nat t]] _ (.list []) _ := de
    have v1 := Det.var' (P := P) (env := [Val.list [.list [.list us, tmJLocCtx m q], .nat t],
      .list []]) (i := 1) (v := .list []) rfl
    have dlen : Det P _ _ (.nat 0) _ := Det.length v1
    have e0 := Det.arg' (P := P) (vs := [.list [.list us, tmJLocCtx m q], .nat t])
      (rest := [.list []]) (j := 0) (v := .list [.list us, tmJLocCtx m q]) rfl
    have elc := Det.get' e0 (Det.nat 1) (vs := [.list us, tmJLocCtx m q]) (v := tmJLocCtx m q) rfl
    have eq' := Det.get' elc (Det.nat 2) (vs := [encPerm (1 : Perm (Fin m)),
      encPerm (1 : Perm (Fin q)), .nat q, .nat m]) (v := .nat q) rfl
    have em := Det.get' elc (Det.nat 3) (vs := [encPerm (1 : Perm (Fin m)),
      encPerm (1 : Perm (Fin q)), .nat q, .nat m]) (v := .nat m) rfl
    have emq := Det.arith' (op := .mul) em eq' (z := m * q) rfl
    have crg := Det.call emq (tmJ_range_det hrg (m * q))
    have dite := Det.ite_zero (t := .call swS (mk4 (.get (.var 1) (.nat 0))
      (.get (arg 0) (.nat 1)) (.arith .div (arg 1) (.get (.get (arg 0) (.nat 1)) (.nat 2)))
      (.arith .mod (arg 1) (.get (.get (arg 0) (.nat 1)) (.nat 2))))) dlen crg
    have hval : encFun (fun i : Fin (m * q) => (i : ℕ)) =
        encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJYgSw O t)) := by
      rw [hsw, map_one]; rfl
    rw [hval] at dite
    refine (Det.letE de' dite).mono ?_
    have wid := wt_ids_le (m * q)
    rw [hval] at wid
    have e3 : ((m * q + 1) ^ 3) ≤ ((m + 1) * (q + 1)) ^ 3 := Nat.pow_le_pow_left hmq 3
    have hW38 : ((m + 1) * (q + 1)) ^ 3 ≤ ((m + 1) * (q + 1)) ^ 8 :=
      Nat.pow_le_pow_right hW1 (by norm_num)
    have wnil : (Val.list []).wt = 4 := wt_list_nil
    simp only [List.length_nil] at *
    show _ ≤ 10 ^ 15 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 8
    omega
  | some p =>
    obtain ⟨b, gs⟩ := p
    have hsw : tmJYgSw O t = tmJSw (tmJFst t) (tmJSnd t) b := by unfold tmJYgSw; rw [h]
    rw [h] at de he
    have de' : Det P [Val.list [.list [.list us, tmJLocCtx m q], .nat t]] _
        (.list [encPerm b, encGroup gs]) _ := de
    have he' : (Val.list [encPerm b, encGroup gs]).wt < (Val.list us).wt := he
    have v1 := Det.var' (P := P) (env := [Val.list [.list [.list us, tmJLocCtx m q], .nat t],
      .list [encPerm b, encGroup gs]]) (i := 1) (v := .list [encPerm b, encGroup gs]) rfl
    have dlen : Det P _ _ (.nat 2) _ := Det.length v1
    have dbb := Det.get' v1 (Det.nat 0) (vs := [encPerm b, encGroup gs]) (v := encPerm b) rfl
    have e0 := Det.arg' (P := P) (vs := [.list [.list us, tmJLocCtx m q], .nat t])
      (rest := [.list [encPerm b, encGroup gs]]) (j := 0) (v := .list [.list us, tmJLocCtx m q]) rfl
    have e1 := Det.arg' (P := P) (vs := [.list [.list us, tmJLocCtx m q], .nat t])
      (rest := [.list [encPerm b, encGroup gs]]) (j := 1) (v := .nat t) rfl
    have elc := Det.get' e0 (Det.nat 1) (vs := [.list us, tmJLocCtx m q]) (v := tmJLocCtx m q) rfl
    have eq' := Det.get' elc (Det.nat 2) (vs := [encPerm (1 : Perm (Fin m)),
      encPerm (1 : Perm (Fin q)), .nat q, .nat m]) (v := .nat q) rfl
    have ediv := Det.arith' (op := .div) e1 eq' (z := (tmJFst t : ℕ)) rfl
    have emod := Det.arith' (op := .mod) e1 eq' (z := (tmJSnd t : ℕ)) rfl
    have csw := Det.call (Det.mk4 dbb elc ediv emod)
      (tmJ_swS_spec hswS hiv htbD hswDE htbP hswPE hpr (tmJFst t) (tmJSnd t) b)
    have dite := Det.ite_pos (e := .call rg (.arith .mul
      (.get (.get (arg 0) (.nat 1)) (.nat 3)) (.get (.get (arg 0) (.nat 1)) (.nat 2))))
      dlen (by norm_num) csw
    rw [← hsw] at dite
    refine (Det.letE de' dite).mono ?_
    have wb := wt_encPerm_le b
    have w4 := wt_list4_le (encPerm b) (tmJLocCtx m q) (.nat (tmJFst t)) (.nat (tmJSnd t))
    have hL : tmJLocK ((m + 1) * (q + 1)) ≤ 10 ^ 14 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 8 := by
      unfold tmJLocK; exact Nat.mul_le_mul_left _ hW8
    have hbW : (m + 1) ^ 2 ≤ ((m + 1) * (q + 1)) ^ 2 := Nat.pow_le_pow_left hm1 2
    have w2' : (Val.nat 2).wt ≤ 4 := wt_nat_le 2
    have rlen : [encPerm b, encGroup gs].length = 2 := rfl
    show _ ≤ 10 ^ 15 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 8
    omega

/-! ### All transpositions -/

/-- The transposition values weigh little. -/
theorem tmJYg_sws_wt {m q : ℕ} (O : Fin q → Fin q → Option (Perm (Fin m) × List (Perm (Fin m)))) :
    (Val.list ((List.finRange (q * q)).map fun t =>
      encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJYgSw O t)))).wt ≤
      9 * ((m + 1) * (q + 1)) ^ 4 + 4 := by
  have := tmJ_wt_list_le (vs := (List.finRange (q * q)).map fun t =>
      encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJYgSw O t)))
    (E := 4 * (m * q + 1) ^ 2) (by
      intro v hv
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 hv
      exact wt_encPerm_le _)
  simp only [List.length_map, List.length_finRange] at this
  have hq1 : q + 1 ≤ (m + 1) * (q + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hmq : m * q + 1 ≤ (m + 1) * (q + 1) := by nlinarith
  have hout : (m * q + 1) ^ 2 ≤ ((m + 1) * (q + 1)) ^ 2 := Nat.pow_le_pow_left hmq 2
  have hqq : q * q ≤ ((m + 1) * (q + 1)) ^ 2 := by
    have : q * q ≤ (q + 1) ^ 2 := by nlinarith
    have : (q + 1) ^ 2 ≤ ((m + 1) * (q + 1)) ^ 2 := Nat.pow_le_pow_left hq1 2
    omega
  have h1 : 1 ≤ ((m + 1) * (q + 1)) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have h2 : q * q * (2 * (4 * (m * q + 1) ^ 2) + 1) ≤
      ((m + 1) * (q + 1)) ^ 2 * (9 * ((m + 1) * (q + 1)) ^ 2) :=
    Nat.mul_le_mul hqq (by omega)
  have e : ((m + 1) * (q + 1)) ^ 2 * (9 * ((m + 1) * (q + 1)) ^ 2) =
      9 * ((m + 1) * (q + 1)) ^ 4 := by ring
  omega

/-- The cost of all transpositions, in `V = wt us + (m + 1) (q + 1)`. -/
def tmJYgSwsK (V : ℕ) : ℕ := 10 ^ 16 * V ^ 10

/-- **All transpositions**, tabulated over `0, …, q² - 1`. -/
theorem tmJ_sws_spec {P : Program} {tbS f rg swS iv tbD swDE tbP swPE pr prg prt prte : ℕ}
    (htbS : P.HasAt tbS (mapFuns tbS f))
    (hf : P.funs[f]? = some (tmJSwF rg swS)) (hrg : P.HasAt rg (rangeFuns rg))
    (hswS : P.funs[swS]? = some (tmJSwSF iv tbD tbP pr)) (hiv : P.HasAt iv (invFuns iv))
    (htbD : P.HasAt tbD (mapFuns tbD swDE)) (hswDE : P.funs[swDE]? = some tmJSwDEF)
    (htbP : P.HasAt tbP (mapFuns tbP swPE)) (hswPE : P.funs[swPE]? = some tmJSwPEF)
    (hpr : TmJPairAt P pr prg prt prte) {m q : ℕ}
    (O : Fin q → Fin q → Option (Perm (Fin m) × List (Perm (Fin m)))) (us : List Val)
    (hus : ∀ a a' : Fin q, us[(a : ℕ) * (2 * q) + a']? = some (tmJEntVal (O a a'))) :
    FunDet P tbS (.list [.list [.list us, tmJLocCtx m q], encFun fun t : Fin (q * q) => (t : ℕ)])
      (.list ((List.finRange (q * q)).map fun t =>
        encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJYgSw O t))))
      (tmJYgSwsK ((Val.list us).wt + (m + 1) * (q + 1))) := by
  have hT := tabulate_spec htbS (c := .list [.list us, tmJLocCtx m q])
    (F := fun t : Fin (q * q) =>
      encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJYgSw O t)))
    (B := tmJYgSwK ((Val.list us).wt + (m + 1) * (q + 1)))
    (fun t => tmJ_sw_spec hf hrg hswS hiv htbD hswDE htbP hswPE hpr O us hus t)
  refine hT.mono ?_
  have wS := tmJYg_sws_wt O
  have hq1 : q + 1 ≤ (m + 1) * (q + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hV1 : (m + 1) * (q + 1) ≤ (Val.list us).wt + (m + 1) * (q + 1) := by omega
  have hY1 : 1 ≤ (Val.list us).wt + (m + 1) * (q + 1) := by omega
  have hqq : q * q + 1 ≤ ((m + 1) * (q + 1)) ^ 2 := by
    have : q * q + 1 ≤ (q + 1) ^ 2 := by nlinarith
    have : (q + 1) ^ 2 ≤ ((m + 1) * (q + 1)) ^ 2 := Nat.pow_le_pow_left hq1 2
    omega
  have hW2 : ((m + 1) * (q + 1)) ^ 2 ≤ ((Val.list us).wt + (m + 1) * (q + 1)) ^ 2 :=
    Nat.pow_le_pow_left hV1 2
  have hW4 : ((m + 1) * (q + 1)) ^ 4 ≤ ((Val.list us).wt + (m + 1) * (q + 1)) ^ 4 :=
    Nat.pow_le_pow_left hV1 4
  have hid4 : (q * q + 1) ^ 2 ≤ ((m + 1) * (q + 1)) ^ 4 := by
    have := Nat.pow_le_pow_left hqq 2
    have e : (((m + 1) * (q + 1)) ^ 2) ^ 2 = ((m + 1) * (q + 1)) ^ 4 := by ring
    omega
  have hV24 : ((Val.list us).wt + (m + 1) * (q + 1)) ^ 2 ≤
      ((Val.list us).wt + (m + 1) * (q + 1)) ^ 4 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hV12 : (Val.list us).wt + (m + 1) * (q + 1) ≤
      ((Val.list us).wt + (m + 1) * (q + 1)) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hV610 : ((Val.list us).wt + (m + 1) * (q + 1)) ^ 6 ≤
      ((Val.list us).wt + (m + 1) * (q + 1)) ^ 10 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hW1 : 1 ≤ ((m + 1) * (q + 1)) ^ 2 := by omega
  have wc := wt_tmJLocCtx_le m q
  have wid := wt_ids_le (q * q)
  have w2 := wt_list2_le (.list us) (tmJLocCtx m q)
  have w3 := wt_list2_le (.list [.list us, tmJLocCtx m q])
    (encFun fun t : Fin (q * q) => (t : ℕ))
  have hWW : (m + 1) * (q + 1) ≤ ((m + 1) * (q + 1)) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hW24 : ((m + 1) * (q + 1)) ^ 2 ≤ ((m + 1) * (q + 1)) ^ 4 :=
    Nat.pow_le_pow_right (by omega) (by norm_num)
  have P1 : q * q * tmJYgSwK ((Val.list us).wt + (m + 1) * (q + 1)) ≤
      10 ^ 15 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 10 := by
    unfold tmJYgSwK
    calc q * q * (10 ^ 15 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 8)
        ≤ ((Val.list us).wt + (m + 1) * (q + 1)) ^ 2 *
          (10 ^ 15 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 8) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 10 ^ 15 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 10 := by ring
  have P2 : mapK * (q * q + 1) * ((Val.list [.list [.list us, tmJLocCtx m q],
      encFun fun t : Fin (q * q) => (t : ℕ)]).wt +
      (Val.list ((List.finRange (q * q)).map fun t =>
        encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJYgSw O t)))).wt + 1) ≤
      1000 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 2 *
        (300 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 4) := by
    have h1 : q * q + 1 ≤ ((Val.list us).wt + (m + 1) * (q + 1)) ^ 2 := by omega
    have h2 : (Val.list [.list [.list us, tmJLocCtx m q],
        encFun fun t : Fin (q * q) => (t : ℕ)]).wt +
        (Val.list ((List.finRange (q * q)).map fun t =>
          encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJYgSw O t)))).wt + 1 ≤
        300 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 4 := by omega
    unfold mapK
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
  have e2 : 1000 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 2 *
      (300 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 4) =
      300000 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 6 := by ring
  show _ ≤ 10 ^ 16 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 10
  omega

end GI.Impl
